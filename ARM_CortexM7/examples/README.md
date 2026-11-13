# Examples of Cortex-M7 assembly read by `arm_file`

| File | What it shows |
| --- | --- |
| `startup.s` | the vector table and the reset handler of a Cortex-M7: sections, `.weak`, `.thumb_set`, a macro that defines the weak handlers, numeric labels, literal pools, enabling the FPU |
| `memcpy.s` | `memcpy`, `memset` and a word-wise copy: numeric labels, `cbz`, post-indexed loads and stores, `ldmia`/`stmia` |
| `macros.s` | register aliases (`.req`), macros with defaults, `:vararg` and keyword arguments, `.if`/`.else`, `.rept`, `.irp`, local labels in macros |
| `fpu.s` | single and double precision (FPv5): `vldmia`, `vfma.f32`, `vpush`, `vcvt.s32.f32`, `vsqrt.f64`, `vmrs`, an `it` block |
| `context.s` | the context switch of a small RTOS: `PendSV`, `SVC`, `mrs`/`msr` of `psp`, `basepri`, `primask`, `tbb` with a table of `(label - label) / 2`, `.comm` |

They assemble with LLVM's integrated assembler (and are written in the syntax of GNU `as`):
`clang --target=thumbv7em-none-eabihf -mcpu=cortex-m7 -c file.s`.
