@ Floating point: a dot product in single and double precision.
    .syntax unified
    .cpu cortex-m7
    .fpu fpv5-d16
    .thumb
    .text

    .global dot_f32
    .type dot_f32, %function
    .thumb_func
@ float dot_f32(const float *a, const float *b, int n)
dot_f32:
    vsub.f32 s0, s0, s0
    cbz r2, 2f
1:  vldmia r0!, {s1}
    vldmia r1!, {s2}
    vfma.f32 s0, s1, s2
    subs r2, r2, #1
    bne 1b
2:  bx lr
    .size dot_f32, . - dot_f32

    .global dot_f64
    .type dot_f64, %function
    .thumb_func
dot_f64:
    vpush {d8-d9}
    vsub.f64 d0, d0, d0
    cbz r2, 2f
1:  vldr d8, [r0]
    vldr d9, [r1]
    vmla.f64 d0, d8, d9
    adds r0, r0, #8
    adds r1, r1, #8
    subs r2, r2, #1
    bne 1b
2:  vpop {d8-d9}
    bx lr
    .size dot_f64, . - dot_f64

    .global to_int
    .type to_int, %function
    .thumb_func
to_int:
    vcvt.s32.f32 s0, s0
    vmov r0, s0
    bx lr
    .size to_int, . - to_int

    .global norm
    .type norm, %function
    .thumb_func
norm:
    vmul.f64 d0, d0, d0
    vsqrt.f64 d0, d0
    vcmp.f64 d0, #0
    vmrs APSR_nzcv, fpscr
    it eq
    vmoveq.f64 d0, d1
    bx lr
    .size norm, . - norm
