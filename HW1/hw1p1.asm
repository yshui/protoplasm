
.text
main:
	li $v0, 5
	syscall
	move $t0, $v0   # read n into $t0
	blez $t0, end   # quit if n <= 0

	li $t2, 1       # $t2 is the step counter
L1:
	and $t1, $t0, 1 # tmp = n % 2
	bnez $t1, L2    # jump to 3n+1 branch if tmp != 0
	div $t0, $t0, 2 # otherwise n = n/2
	b L3            # end of branch
L2:
	mul $t0, $t0, 3
	add $t0, $t0, 1 # n = 3n+1
L3:
	add $t2, $t2, 1 # increment step counter
	bne $t0, 1, L1  # continue looping if n != 1

	move $a0, $t2
	li $v0, 1
	syscall         # print result

end:
	li $v0, 10
	syscall
