main:
	li $v0, 5
	syscall
	move $t0, $v0
	blez $t0, end     # read n into $t0, quit if n <= 0

	li $t1, 1         # $t1 = 2^k
	li $t2, 1         # $t2 = k!
	li $t3, 0         # $t3 = counter

L1:
	add $t3, $t3, 1   # increment counter
	mul $t1, $t1, 2   # $t1 = $t1*2
	mul $t2, $t2, $t3 # $t2 = $t2*counter

	# then we remove common factors from $t1 and $t2
L2:
	ble $t1, 1, L3    # if $t1 <= 1, end loop
	and $t4, $t2, 1   # $t4 = $t2 % 2
	bnez $t4, L3      # if $t2 is not multiply of 2, end loop
	div $t1, $t1, 2   # $t1 = $t1/2
	div $t2, $t2, 2   # $t2 = $t2/2
	b L2
L3:
	div $t4, $t2, $t1 # calculate floor(k!/2^k)
	blt $t4, $t0, L1  # floor(k!/2^k) < n, continue

print:
	sub $t3, $t3, 1
	move $a0, $t3
	li $v0, 1
	syscall

end:
	li $v0, 10
	syscall

