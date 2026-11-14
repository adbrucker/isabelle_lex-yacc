@ Startup code of a Cortex-M7: the vector table and the reset handler.
    .syntax unified
    .cpu cortex-m7
    .fpu fpv5-d16
    .thumb

    .global _estack
    .global g_pfnVectors

    .section .isr_vector, "a", %progbits
    .type g_pfnVectors, %object
g_pfnVectors:
    .word _estack
    .word Reset_Handler
    .word NMI_Handler
    .word HardFault_Handler
    .word MemManage_Handler
    .word BusFault_Handler
    .word UsageFault_Handler
    .word 0, 0, 0, 0
    .word SVC_Handler
    .word DebugMon_Handler
    .word 0
    .word PendSV_Handler
    .word SysTick_Handler
    .size g_pfnVectors, . - g_pfnVectors

    .section .text.Reset_Handler, "ax", %progbits
    .weak Reset_Handler
    .type Reset_Handler, %function
    .thumb_func
Reset_Handler:
    ldr sp, =_estack            @ the stack
    movs r1, #0
    b 2f
1:  ldr r3, =_sidata            @ copy .data from flash to RAM
    ldr r3, [r3, r1]
    str r3, [r0, r1]
    adds r1, r1, #4
2:  ldr r0, =_sdata
    ldr r3, =_edata
    adds r2, r0, r1
    cmp r2, r3
    bcc 1b
    ldr r2, =_sbss              @ clear .bss
    b 4f
3:  movs r3, #0
    str r3, [r2], #4
4:  ldr r3, =_ebss
    cmp r2, r3
    bcc 3b
    @ enable the floating point unit: CP10 and CP11 full access
    ldr r0, =0xE000ED88
    ldr r1, [r0]
    orr r1, r1, #(0xF << 20)
    str r1, [r0]
    dsb
    isb
    bl main
5:  b 5b
    .size Reset_Handler, . - Reset_Handler

    .section .text.Default_Handler, "ax", %progbits
    .thumb_func
Default_Handler:
Infinite_Loop:
    b Infinite_Loop
    .size Default_Handler, . - Default_Handler

    .macro weak_handler name
    .weak \name
    .thumb_set \name, Default_Handler
    .endm

    weak_handler NMI_Handler
    weak_handler HardFault_Handler
    weak_handler MemManage_Handler
    weak_handler BusFault_Handler
    weak_handler UsageFault_Handler
    weak_handler SVC_Handler
    weak_handler DebugMon_Handler
    weak_handler PendSV_Handler
    weak_handler SysTick_Handler
