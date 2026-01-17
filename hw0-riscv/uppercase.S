        .section .data
input_string:   .asciz "Hello world!"

        # tohost/fromhost are data locations used by Spike
        .align 8
tohost: .byte 0
        .align 8
fromhost: .byte 0

        
        .section .text
        .globl _start
_start:
        # Load the address of the input string into a0
        la a0, input_string

        # Your code here!

loop:
        lb t0, 0(a0)
        beq t0, zero, done      #stops at Nul

        li t1, 'a'
        li t2, 'z'
        blt t0,t1,next          #compare if <a
        bgt t0,t2,next          #compare if >z        
        addi t0, t0, -32        #removing imm of 32 to convert to uppercase, doing this only when its only case
        sb t0, 0(a0)

next:
        addi a0, a0, 1
        j loop

done:   
        j end_program


        
end_program:
        # jump here when you're done
        j end_program

