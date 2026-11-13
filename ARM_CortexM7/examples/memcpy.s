@ memcpy and memset, with the numeric labels of the assembler.
    .syntax unified
    .cpu cortex-m7
    .thumb
    .text
    .align 2

    .global memcpy
    .type memcpy, %function
    .thumb_func
memcpy:
    push {r4, lr}
    mov r4, r0
    cbz r2, 2f
1:  ldrb r3, [r1], #1
    strb r3, [r0], #1
    subs r2, r2, #1
    bne 1b
2:  mov r0, r4
    pop {r4, pc}
    .size memcpy, . - memcpy

    .global memset
    .type memset, %function
    .thumb_func
memset:
    mov r3, r0
    cbz r2, 2f
1:  strb r1, [r3], #1
    subs r2, r2, #1
    bne 1b
2:  bx lr
    .size memset, . - memset

@ word-wise copy for aligned buffers; the number of words in r2
    .global copy_words
    .type copy_words, %function
    .thumb_func
copy_words:
    lsrs r2, r2, #2
    beq 3f
2:  ldmia r1!, {r3}
    stmia r0!, {r3}
    subs r2, r2, #1
    bne 2b
3:  bx lr
    .size copy_words, . - copy_words
