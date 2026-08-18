// render-scale 运行时扫描 + 盲试 patch dylib (v5)
// 策略: 纯字节模式扫描 (不依赖 FMOV 解码), 输出候选地址.
//   模式: 同函数内同基址连续 STR-S 到相邻偏移 (偏移差4, 偏移>=0x40) => scaleX/scaleY 候选
// patch: 读 App 沙盒 Documents/render_scale_patch.txt, 每行一个候选号, NOP 掉该候选第一条 STR.
//   (设备上用 Filza/文件App 创建该文件, 内容如 "0\n1\n2" 表示 patch 候选 #0,#1,#2)
// 日志: 写 App 沙盒 Documents/render_scale.log; 也可 log stream | grep RS
// 编译: 见 build-render-scale.yml (GitHub Actions macOS + clang)
// 注入: 同 SplashText —— dylib 放入 Payload/worldflipper.app/Frameworks/,
//        Mach-O 添加 LC_LOAD_DYLIB @executable_path/Frameworks/RenderScale.dylib
// 使用: 1) 装好后先不建配置文件 -> 运行进战斗 -> 读 render_scale.log 看候选
//       2) 建 render_scale_patch.txt 写候选号 -> 重启游戏 -> 看角色是否变化

#import <UIKit/UIKit.h>
#import <objc/runtime.h>
#import <mach-o/dyld.h>
#import <mach-o/loader.h>
#import <stdio.h>
#import <string.h>
#import <stdarg.h>
#import <stdlib.h>
#import <sys/mman.h>

#define MAX_HITS 2048
#define MAX_LOG 16384

static uint64_t hit_vm[MAX_HITS];
static uint32_t hit_imm[MAX_HITS];     // 该候选的 STR 偏移 (第一条)
static uint32_t hit_imm2[MAX_HITS];    // 第二条偏移
static uint32_t hit_rn[MAX_HITS];      // 基址寄存器
static int hit_count = 0;
static char log_buf[MAX_LOG];
static int log_len = 0;
static const uint8_t *g_text = NULL;
static uint64_t g_vm_base = 0;

static void logf(const char *fmt, ...) {
    if (log_len >= MAX_LOG - 300) return;
    va_list args;
    va_start(args, fmt);
    log_len += vsnprintf(log_buf + log_len, MAX_LOG - log_len, fmt, args);
    va_end(args);
}

// 检查候选点前 6 条指令内是否有 FMOV S,#1.0 (scale=1 的特征)
static int has_fmov_one_before(uint64_t file_off) {
    if (file_off < 24 || !g_text) return 0;
    for (uint32_t k = 1; k <= 6; k++) {
        uint32_t w = *(uint32_t *)(g_text + file_off - 4*k);
        // FMOV Sd,#imm: 0x1E2x0000 系, 低 5 位是 Rd
        if ((w & 0xFFFFFC00) == 0x1E2E1000) return 1;
        // 也接受 0x1E2C1000 (0.5) 等小立即数
        if ((w & 0xFFFFF000) == 0x1E2C1000) return 1;
    }
    return 0;
}

// 从沙盒 Documents/render_scale_patch.txt 读取要 patch 的候选号
// 返回 -1 表示无配置文件
static void read_patch_config(int *indices, int *count) {
    *count = 0;
    NSString *doc = NSSearchPathForDirectoriesInDomains(NSDocumentDirectory, NSUserDomainMask, YES).firstObject;
    if (!doc) return;
    NSString *cfgPath = [doc stringByAppendingPathComponent:@"render_scale_patch.txt"];
    NSString *content = [NSString stringWithContentsOfFile:cfgPath encoding:NSUTF8StringEncoding error:NULL];
    if (!content) return;
    for (NSString *line in [content componentsSeparatedByCharactersInSet:[NSCharacterSet newlineCharacterSet]]) {
        line = [line stringByTrimmingCharactersInSet:[NSCharacterSet whitespaceCharacterSet]];
        if (line.length == 0) continue;
        int idx = line.intValue;
        if (indices && *count < MAX_HITS) indices[(*count)++] = idx;
    }
}

// 扫描 __TEXT: 模式1 + 模式2
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
                        logf("[RS] __text @ %p size=0x%llx\n", text, text_size);

                        // 模式2: 紧邻 STR-S 对 (k=1 相邻)
                        for (uint64_t off = 0; off + 12 < text_size; off += 4) {
                            uint32_t w1 = *(uint32_t *)(text + off);
                            if ((w1 & 0xFFC00000) != 0xBD000000) continue; // STR S
                            uint32_t rn1 = (w1 >> 5) & 0x1F;
                            uint32_t imm1 = ((w1 >> 10) & 0xFFF) * 4;
                            if (imm1 < 0x40) continue;
                            if (rn1 == 31) continue; // 排除栈指针(sp)局部变量
                            for (uint32_t k = 1; k <= 4; k++) {
                                if (off + 4*k + 4 > text_size) break;
                                uint32_t w2 = *(uint32_t *)(text + off + 4*k);
                                if ((w2 & 0xFFC00000) != 0xBD000000) continue;
                                uint32_t rn2 = (w2 >> 5) & 0x1F;
                                uint32_t imm2 = ((w2 >> 10) & 0xFFF) * 4;
                                if (rn1 == rn2 && imm2 == imm1 + 4) {
                                    if (hit_count < MAX_HITS) {
                                        hit_vm[hit_count] = vm_base + off;
                                        hit_imm[hit_count] = imm1;
                                        hit_imm2[hit_count] = imm2;
                                        hit_rn[hit_count] = rn1;
                                        hit_count++;
                                    }
                                    break;
                                }
                            }
                        }
                        logf("[RS] adjacent STR-S pairs (k<=4): %d\n", hit_count);
                        return;
                    }
                }
            }
        }
        cmd = (const struct load_command *)((uint8_t *)cmd + cmd->cmdsize);
    }
}

// patch: NOP 掉指定候选的第一条 STR (scaleX 写入)
// 从配置文件读取候选号
static void patch_hits(uint64_t slide) {
    int indices[MAX_HITS];
    int count = 0;
    read_patch_config(indices, &count);
    if (count == 0) {
        logf("[RS] no render_scale_patch.txt -> scan only\n");
        return;
    }
    for (int i = 0; i < count; i++) {
        int idx = indices[i];
        if (idx >= 0 && idx < hit_count) {
            uint8_t *runtime = (uint8_t *)(hit_vm[idx] + slide);
            uintptr_t page = (uintptr_t)runtime & ~0xFFFULL;
            mprotect((void *)page, 0x4000, PROT_READ | PROT_WRITE | PROT_EXEC);
            uint32_t orig = *(uint32_t *)runtime;
            *(uint32_t *)runtime = 0xD503201F; // NOP
            logf("[RS] PATCHED #%d vm=0x%llx STR S->[X,#0x%x] orig=0x%08x\n",
                 idx, hit_vm[idx], hit_imm[idx], orig);
        } else {
            logf("[RS] WARN invalid patch idx %d (0-%d)\n", idx, hit_count-1);
        }
    }
}

// 渲染钩子: 每帧在进入渲染前打印候选 (可观察)
static void (*orig_displayTimerDraw)(id, SEL);
static int frame_count = 0;
static void hooked_displayTimerDraw(id self, SEL _cmd) {
    if (orig_displayTimerDraw) orig_displayTimerDraw(self, _cmd);
    if (frame_count++ < 3) {
        logf("[RS] frame %d\n", frame_count);
    }
}

static void log_buf_write(NSString *path) {
    NSData *d = [NSData dataWithBytes:log_buf length:log_len];
    [d writeToFile:path atomically:YES];
}

__attribute__((constructor))
static void init(void) {
    logf("[RS] render-scale dylib v4 loaded pid=%d\n", getpid());

    for (uint32_t i = 0; i < _dyld_image_count(); i++) {
        const char *name = _dyld_get_image_name(i);
        if (!name || !strstr(name, "worldflipper")) continue;
        const struct mach_header_64 *header = (const struct mach_header_64 *)_dyld_get_image_header(i);
        if (!header || header->magic != MH_MAGIC_64) continue;
        const uintptr_t slide = _dyld_get_image_vmaddr_slide(i);
        logf("[RS] main image=%s slide=0x%lx\n", name, slide);
        scan_text(slide, (const uint8_t *)header);
        // 输出候选列表 (标注 FMOV #1.0 特征)
        for (int h = 0; h < hit_count; h++) {
            int fm = has_fmov_one_before(hit_vm[h] - g_vm_base);
            logf("[RS]   #%d: vm=0x%llx STR S->[X%d,#0x%x] + [X%d,#0x%x] (file_off=0x%llx) %s\n",
                 h, hit_vm[h], hit_rn[h], hit_imm[h], hit_rn[h], hit_imm2[h],
                 hit_vm[h], fm ? "<-- FMOV#1.0 nearby" : "");
        }
        patch_hits(slide);
        break;
    }

    // hook 渲染入口
    Class cls = NSClassFromString(@"CTStageView");
    if (cls) {
        Method m = class_getInstanceMethod(cls, sel_registerName("_displayTimerDraw:"));
        if (m) {
            orig_displayTimerDraw = (void (*)(id, SEL))method_getImplementation(m);
            method_setImplementation(m, (IMP)hooked_displayTimerDraw);
            logf("[RS] hooked _displayTimerDraw\n");
        } else {
            logf("[RS] WARN no _displayTimerDraw\n");
        }
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