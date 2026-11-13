@ Macros, register aliases, conditional assembly and loops.
    .syntax unified
    .cpu cortex-m7
    .thumb

    DEBUG = 0
    ARRAY_LEN = 8

acc     .req r4
ptr     .req r5
count   .req r6

    .macro save_regs regs:vararg
    push {\regs, lr}
    .endm

    .macro restore_regs regs:vararg
    pop {\regs, pc}
    .endm

    .macro zero_reg reg, value=0
    movs \reg, #\value
    .endm

    .macro load_const reg, value
    movw \reg, #:lower16:\value
    movt \reg, #:upper16:\value
    .endm

    .macro delay n
    movs r0, #\n
1:  subs r0, r0, #1
    bne 1b
    .endm

    .macro vector_entry name, handler=Default_Handler
    .word \handler
    .endm

    .text
    .global sum_array
    .type sum_array, %function
    .thumb_func
sum_array:
    save_regs acc, ptr, count
    zero_reg acc
    mov ptr, r0
    movs count, #ARRAY_LEN
.Lloop:
    ldr r1, [ptr], #4
    add acc, acc, r1
    subs count, count, #1
    bne .Lloop
    .if DEBUG
    bl trace
    .else
    nop
    .endif
    mov r0, acc
    restore_regs acc, ptr, count
    .size sum_array, . - sum_array

    .global wait
    .thumb_func
wait:
    delay 10
    delay n=20
    bx lr

    .global fill
    .thumb_func
fill:
    .rept 4
    str r1, [r0], #4
    .endr
    bx lr

    .irp reg, r0, r1, r2, r3
    mov \reg, #0
    .endr

    .section .rodata
    .align 2
table:
    .word 1, 2, 3, 4
table_end:
    .equ TABLE_BYTES, table_end - table
