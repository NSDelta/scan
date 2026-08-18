// render-scale 运行时扫描 + 盲试 patch dylib (v7 全模式)
// 扫描模式:
//   [A] 相邻 STR-S 对: 同函数同基址连续 STR S 到偏移差4 => scaleX/scaleY 候选
//   [B] FMOV #1.0 -> STR S 对象字段 (scale=1 设置)
//   [C] FMOV #6.0 -> STR S 对象字段 (scale=6 设置)
//   [D] FMUL s,#6 -> STR S 对象字段 (乘以6后写入)
//   [E] 对象字段自更新: LDR S [X,#off] -> FMUL/FDIV -> STR S [X,#off]
//
// 三种运行模式:
//   [S] 纯扫描: 无配置文件 -> 输出全部候选
//   [P] 手动 patch: Documents/render_scale_patch.txt 每行候选号 -> NOP 它们
//   [A] 自动盲试: Documents/render_scale_autotest.txt -> 每次启动 patch 下一个未测候选
//
// 日志: App 沙盒 Documents/render_scale.log; 也写 stderr (log stream | grep RS)
//
// 编译 (GitHub Actions macOS):
//   SDK=$(xcrun --sdk iphoneos --show-sdk-path)
//   clang -arch arm64 -isysroot "$SDK" -miphoneos-version-min=14.0 -fobjc-arc -dynamiclib \
//     -framework UIKit -framework Foundation -o RenderScale.dylib render_scan.m
//   ldid -S RenderScale.dylib
//
// 注入: dylib 放入 Payload/worldflipper.app/Frameworks/,
//        Mach-O 添加 LC_LOAD_DYLIB @executable_path/Frameworks/RenderScale.dylib
//
// 使用: 1) 纯扫描 -> 看候选
//       2) 建 render_scale_autotest.txt -> 重启 N 次逐个测
//       3) 找到变化那次 -> 用 render_scale_patch.txt 固定

#import <UIKit/UIKit.h>
#import <objc/runtime.h>
#import <mach-o/dyld.h>
#import <mach-o/loader.h>
#import <stdio.h>
#import <string.h>
#import <stdarg.h>
#import <stdlib.h>
#import <math.h>
#import <sys/mman.h>

#define MAX_HITS 4096
#define MAX_LOG 32768

static uint64_t hit_vm[MAX_HITS];
static uint32_t hit_imm[MAX_HITS];
static uint32_t hit_imm2[MAX_HITS];
static uint32_t hit_rn[MAX_HITS];
static char hit_mode[MAX_HITS];
static int hit_count = 0;
static char log_buf[MAX_LOG];
static int log_len = 0;
static const uint8_t *g_text = NULL;
static uint64_t g_vm_base = 0;

static void RSLog(const char *fmt, ...) {
    if (log_len >= MAX_LOG - 400) return;
    va_list args;
    va_start(args, fmt);
    log_len += vsnprintf(log_buf + log_len, MAX_LOG - log_len, fmt, args);
    va_end(args);
}

static void add_hit(char mode, uint64_t vm_off, uint32_t rn, uint32_t imm1, uint32_t imm2) {
    if (hit_count >= MAX_HITS) return;
    hit_vm[hit_count] = vm_off;
    hit_rn[hit_count] = rn;
    hit_imm[hit_count] = imm1;
    hit_imm2[hit_count] = imm2;
    hit_mode[hit_count] = mode;
    hit_count++;
}

// FMOV Sd,#imm8 判定: 用精确掩码匹配特定值 (绕过解码难题)
// 基于 capstone 反推: #1.0 系列 = 0x1E2E1000 + rd, #6.0 系列 = 0x1E231000 + rd
// 掩码 0xFFFFF800 保留 bit12 (区分 ucvtf/scvtf 的 0x1E230000) 并忽略 rd (低5位)
#define FMOV_MASK   0xFFFFF800
#define FMOV_ONE    0x1E2E1000   // #1.0
#define FMOV_SIX    0x1E231000   // #6.0
static int is_fmov_one(uint32_t w) { return (w & FMOV_MASK) == FMOV_ONE; }
static int is_fmov_six(uint32_t w) { return (w & FMOV_MASK) == FMOV_SIX; }

// 检查指令是否 STR S [Xn,#imm]
static int is_str_s(uint32_t w, uint32_t *rn, uint32_t *imm) {
    if ((w & 0xFFC00000) != 0xBD000000) return 0;
    *rn = (w >> 5) & 0x1F;
    *imm = ((w >> 10) & 0xFFF) * 4;
    return 1;
}

// 检查指令是否 LDR S [Xn,#imm]
static int is_ldr_s(uint32_t w, uint32_t *rn, uint32_t *imm) {
    if ((w & 0xFFC00000) != 0xBD400000) return 0;
    *rn = (w >> 5) & 0x1F;
    *imm = ((w >> 10) & 0xFFF) * 4;
    return 1;
}

// 扫描 __TEXT 全模式
static void scan_text(uint64_t slide, const uint8_t *header_base) {
    const struct mach_header_64 *header = (const struct mach_header_64 *)header_base;
    const uint8_t *base = (const uint8_t *)header;
    const struct load_command *cmd = (const struct load_command *)(base + sizeof(struct mach_header_64));
    for (uint32_t j = 0; j < header->ncmds; j++) {
        if (cmd->cmd == LC_SEGMENT_64) {
            const struct segment_command_64 *seg = (const struct segment_command_64 *)cmd;
            if (strcmp(seg->segname, "__TEXT") == 0) {
                const struct section_64 *sect = (const struct section_64 *)((uint8_t *)seg + sizeof(struct segment_command_64));
                for (uint32_t s = 0; s < seg->nsects; s++) {
                    if (strcmp(sect[s].sectname, "__text") == 0) {
                        const uint8_t *text = (const uint8_t *)(sect[s].addr + slide);
                        const uint64_t text_size = sect[s].size;
                        const uint64_t vm_base = sect[s].addr;
                        g_text = text;
                        g_vm_base = vm_base;
                        RSLog("[RS] __text @ %p size=0x%llx\n", text, text_size);

                        // ============ [A] 相邻 STR-S 对 ============
                        for (uint64_t off = 0; off + 12 < text_size; off += 4) {
                            uint32_t rn1, imm1;
                            uint32_t w1 = *(uint32_t *)(text + off);
                            if (!is_str_s(w1, &rn1, &imm1)) continue;
                            if (imm1 < 0x40 || rn1 == 31) continue;
                            for (uint32_t k = 1; k <= 4; k++) {
                                if (off + 4*k + 4 > text_size) break;
                                uint32_t rn2, imm2;
                                uint32_t w2 = *(uint32_t *)(text + off + 4*k);
                                if (!is_str_s(w2, &rn2, &imm2)) continue;
                                if (rn1 == rn2 && imm2 == imm1 + 4) {
                                    add_hit('A', vm_base + off, rn1, imm1, imm2);
                                    break;
                                }
                            }
                        }
                        RSLog("[RS] [A] adjacent STR-S pairs: done\n");

                        // ============ [B] FMOV #1.0 -> STR S 对象字段 ============
                        for (uint64_t off = 0; off + 8 < text_size; off += 4) {
                            uint32_t w = *(uint32_t *)(text + off);
                            if (!is_fmov_one(w)) continue;
                            uint32_t rd = w & 0x1F;
                            for (uint32_t k = 1; k <= 4; k++) {
                                if (off + 4*k + 4 > text_size) break;
                                uint32_t rn, imm;
                                uint32_t w2 = *(uint32_t *)(text + off + 4*k);
                                if (is_str_s(w2, &rn, &imm) && (w2 & 0x1F) == rd && rn != 31 && imm >= 0x40) {
                                    add_hit('B', vm_base + off, rn, imm, imm);
                                    break;
                                }
                                if (w2 == 0xD65F03C0) break; // RET
                            }
                        }
                        RSLog("[RS] [B] FMOV#1.0->STR: done\n");

                        // ============ [C] FMOV #6.0 -> STR S 对象字段 ============
                        for (uint64_t off = 0; off + 8 < text_size; off += 4) {
                            uint32_t w = *(uint32_t *)(text + off);
                            if (!is_fmov_six(w)) continue;
                            uint32_t rd = w & 0x1F;
                            for (uint32_t k = 1; k <= 4; k++) {
                                if (off + 4*k + 4 > text_size) break;
                                uint32_t rn, imm;
                                uint32_t w2 = *(uint32_t *)(text + off + 4*k);
                                if (is_str_s(w2, &rn, &imm) && (w2 & 0x1F) == rd && rn != 31 && imm >= 0x40) {
                                    add_hit('C', vm_base + off, rn, imm, imm);
                                    break;
                                }
                                if (w2 == 0xD65F03C0) break;
                            }
                        }
                        RSLog("[RS] [C] FMOV#6.0->STR: done\n");

                        // ============ [D] FMUL s,#6 -> STR S 对象字段 ============
                        // (ARM64 FMUL 无立即数版, 6 通过寄存器传递, 该模式并入 [E] 自更新扫描)
                        RSLog("[RS] [D] merged into [E]\n");

                        // ============ [E] 对象字段自更新: LDR S -> FMUL/FDIV -> STR S 同偏移 ============
                        for (uint64_t off = 0; off + 20 < text_size; off += 4) {
                            uint32_t rn, imm;
                            uint32_t w1 = *(uint32_t *)(text + off);
                            if (!is_ldr_s(w1, &rn, &imm)) continue;
                            if (rn == 31 || imm < 0x40) continue;
                            // 后续 6 条内找 FMUL/FDIV/FADD 用 rt, 再后续 4 条内 STR S [同rn,同imm]
                            for (uint32_t k = 1; k <= 6; k++) {
                                if (off + 4*k + 8 > text_size) break;
                                uint32_t wm = *(uint32_t *)(text + off + 4*k);
                                // FMUL 0x1E200800, FDIV 0x1E201800, FADD 0x1E202800, FSUB 0x1E203800
                                uint32_t opc = wm & 0x7FE0FC00;
                                int is_math = (opc == 0x1E200800 || opc == 0x1E201800 ||
                                              opc == 0x1E202800 || opc == 0x1E203800);
                                if (!is_math) continue;
                                // 数学指令结果写回同一字段
                                for (uint32_t q = k+1; q <= k+5; q++) {
                                    if (off + 4*q + 4 > text_size) break;
                                    uint32_t rn2, imm2;
                                    uint32_t ws = *(uint32_t *)(text + off + 4*q);
                                    if (is_str_s(ws, &rn2, &imm2) && (ws & 0x1F) == (wm & 0x1F) && rn2 == rn && imm2 == imm) {
                                        add_hit('E', vm_base + off, rn, imm, imm);
                                        break;
                                    }
                                }
                                break;
                            }
                        }
                        RSLog("[RS] [E] field self-update: done\n");

                        RSLog("[RS] total candidates: %d\n", hit_count);
                        return;
                    }
                }
            }
        }
        cmd = (const struct load_command *)((uint8_t *)cmd + cmd->cmdsize);
    }
}

// 从配置文件读取候选号
static void read_patch_config(int *indices, int *count, NSString *filename) {
    *count = 0;
    NSString *doc = NSSearchPathForDirectoriesInDomains(NSDocumentDirectory, NSUserDomainMask, YES).firstObject;
    if (!doc) return;
    NSString *cfgPath = [doc stringByAppendingPathComponent:filename];
    NSString *content = [NSString stringWithContentsOfFile:cfgPath encoding:NSUTF8StringEncoding error:NULL];
    if (!content) return;
    for (NSString *line in [content componentsSeparatedByCharactersInSet:[NSCharacterSet newlineCharacterSet]]) {
        __strong NSString *trimmed = [line stringByTrimmingCharactersInSet:[NSCharacterSet whitespaceCharacterSet]];
        if (trimmed.length == 0) continue;
        int idx = trimmed.intValue;
        if (indices && *count < MAX_HITS) indices[(*count)++] = idx;
    }
}

// patch: NOP 指定候选的第一条 STR
static void patch_hits(uint64_t slide) {
    int indices[MAX_HITS];
    int count = 0;
    read_patch_config(indices, &count, @"render_scale_patch.txt");
    if (count == 0) {
        RSLog("[RS] no render_scale_patch.txt -> scan only\n");
        return;
    }
    for (int i = 0; i < count; i++) {
        int idx = indices[i];
        if (idx >= 0 && idx < hit_count) {
            uint8_t *runtime = (uint8_t *)(hit_vm[idx] + slide);
            uintptr_t page = (uintptr_t)runtime & ~0xFFFULL;
            mprotect((void *)page, 0x4000, PROT_READ | PROT_WRITE | PROT_EXEC);
            uint32_t orig = *(uint32_t *)runtime;
            *(uint32_t *)runtime = 0xD503201F;
            RSLog("[RS] PATCHED #%d [%c] vm=0x%llx STR->[X,#0x%x] orig=0x%08x\n",
                 idx, hit_mode[idx], hit_vm[idx], hit_imm[idx], orig);
        } else {
            RSLog("[RS] WARN invalid patch idx %d (0-%d)\n", idx, hit_count-1);
        }
    }
}

// 自动盲试: 每次启动 patch 下一个未测候选
static void autotest_next(uint64_t slide) {
    NSString *doc = NSSearchPathForDirectoriesInDomains(NSDocumentDirectory, NSUserDomainMask, YES).firstObject;
    if (!doc) return;
    NSString *statePath = [doc stringByAppendingPathComponent:@"render_scale_autotest.txt"];
    NSString *content = [NSString stringWithContentsOfFile:statePath encoding:NSUTF8StringEncoding error:NULL];
    NSMutableSet *done = [NSMutableSet set];
    for (NSString *line in [content componentsSeparatedByCharactersInSet:[NSCharacterSet newlineCharacterSet]]) {
        NSString *t = [line stringByTrimmingCharactersInSet:[NSCharacterSet whitespaceCharacterSet]];
        if (t.length) [done addObject:t];
    }
    for (int h = 0; h < hit_count; h++) {
        NSString *key = [NSString stringWithFormat:@"%d", h];
        if ([done containsObject:key]) continue;
        uint8_t *runtime = (uint8_t *)(hit_vm[h] + slide);
        uintptr_t page = (uintptr_t)runtime & ~0xFFFULL;
        mprotect((void *)page, 0x4000, PROT_READ | PROT_WRITE | PROT_EXEC);
        uint32_t orig = *(uint32_t *)runtime;
        *(uint32_t *)runtime = 0xD503201F;
        RSLog("[RS] AUTOTEST patching #%d [%c] vm=0x%llx STR->[X,#0x%x] orig=0x%08x\n",
              h, hit_mode[h], hit_vm[h], hit_imm[h], orig);
        NSString *newContent = [NSString stringWithFormat:@"%@%d\n", content ? content : @"", h];
        [newContent writeToFile:statePath atomically:YES encoding:NSUTF8StringEncoding error:NULL];
        return;
    }
    RSLog("[RS] AUTOTEST all %d candidates tested\n", hit_count);
}

static void log_buf_write(NSString *path) {
    NSData *d = [NSData dataWithBytes:log_buf length:log_len];
    [d writeToFile:path atomically:YES];
}

__attribute__((constructor))
static void init(void) {
    RSLog("[RS] render-scale dylib v7 all-mode loaded pid=%d\n", getpid());

    for (uint32_t i = 0; i < _dyld_image_count(); i++) {
        const char *name = _dyld_get_image_name(i);
        if (!name || !strstr(name, "worldflipper")) continue;
        const struct mach_header_64 *header = (const struct mach_header_64 *)_dyld_get_image_header(i);
        if (!header || header->magic != MH_MAGIC_64) continue;
        const uintptr_t slide = _dyld_get_image_vmaddr_slide(i);
        RSLog("[RS] main image=%s slide=0x%lx\n", name, slide);
        scan_text(slide, (const uint8_t *)header);

        for (int h = 0; h < hit_count; h++) {
            RSLog("[RS]   #%d [%c]: vm=0x%llx STR S->[X%d,#0x%x]%s (file_off=0x%llx)\n",
                 h, hit_mode[h], hit_vm[h], hit_rn[h], hit_imm[h],
                 (hit_imm2[h] != hit_imm[h]) ? " [+next]" : "",
                 hit_vm[h]);
        }

        patch_hits(slide);
        autotest_next(slide);
        break;
    }

    fprintf(stderr, "%s", log_buf);
    fflush(stderr);

    NSString *doc = NSSearchPathForDirectoriesInDomains(NSDocumentDirectory, NSUserDomainMask, YES).firstObject;
    if (doc) {
        NSString *logPath = [doc stringByAppendingPathComponent:@"render_scale.log"];
        log_buf_write(logPath);
        NSLog(@"[RS] log written to %@", logPath);
    }
}