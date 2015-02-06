main:
	li $v0, 5
	syscall
	move $t0, $v0     # read m into $t0
	blez $t0, end     # quit if m <= 0

	li $v0, 5
	syscall
	move $t1, $v0     # read n into $t1
	blez $t1, end     # quit if n <= n

L1:
	rem $t2, $t0, $t1 # tmp = m%n
	beqz $t2, print   # break if tmp == 0
	move $t0, $t1     # m = n
	move $t1, $t2     # n = tmp
	b L1              # loop

print:
	move $a0, $t1
	li $v0, 1
	syscall

end:
	li $v0, 10
	syscall
