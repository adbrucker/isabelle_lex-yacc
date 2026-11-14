@ The context switch of a small RTOS: PendSV, SVC and the critical sections.
    .syntax unified
    .cpu cortex-m7
    .fpu fpv5-d16
    .thumb
    .text

    .global PendSV_Handler
    .type PendSV_Handler, %function
    .thumb_func
PendSV_Handler:
    mrs r0, psp
    isb
    ldr r3, =current_tcb
    ldr r2, [r3]
    tst lr, #0x10               @ is the extended frame in use?
    it eq
    vstmdbeq r0!, {s16-s31}
    stmdb r0!, {r4-r11, lr}
    str r0, [r2]
    stmdb sp!, {r0, r3}
    mov r0, #0x50
    msr basepri, r0
    dsb
    isb
    bl select_next_task
    mov r0, #0
    msr basepri, r0
    ldmia sp!, {r0, r3}
    ldr r1, [r3]
    ldr r0, [r1]
    ldmia r0!, {r4-r11, lr}
    tst lr, #0x10
    it eq
    vldmiaeq r0!, {s16-s31}
    msr psp, r0
    isb
    bx lr
    .ltorg
    .size PendSV_Handler, . - PendSV_Handler

    .global SVC_Handler
    .type SVC_Handler, %function
    .thumb_func
SVC_Handler:
    ldr r3, =current_tcb
    ldr r1, [r3]
    ldr r0, [r1]
    ldmia r0!, {r4-r11, lr}
    msr psp, r0
    isb
    mov r0, #0
    msr basepri, r0
    bx lr

    .global enter_critical
    .type enter_critical, %function
    .thumb_func
enter_critical:
    mrs r0, primask
    cpsid i
    dsb
    isb
    bx lr

    .global exit_critical
    .type exit_critical, %function
    .thumb_func
exit_critical:
    msr primask, r0
    bx lr

    .global dispatch
    .type dispatch, %function
    .thumb_func
dispatch:
    cmp r0, #4
    bhi 9f
    tbb [pc, r0]
0:  .byte (1f - 0b) / 2
    .byte (2f - 0b) / 2
    .byte (3f - 0b) / 2
    .byte (4f - 0b) / 2
    .byte (5f - 0b) / 2
1:  movs r0, #10
    bx lr
2:  movs r0, #20
    bx lr
3:  movs r0, #30
    bx lr
4:  movs r0, #40
    bx lr
5:  movs r0, #50
    bx lr
9:  movs r0, #0
    bx lr
    .size dispatch, . - dispatch

    .bss
    .align 2
    .comm current_tcb, 4, 4
