.data
str_p: .asciiz "perfect\n"
str_d: .asciiz "deficient\n"
str_a: .asciiz "abundant\n"

.text
main:
	li $v0, 5
	syscall
	move $t0, $v0     # read n
	ble $t0, 1, end     # quit if n <= 1

	# loop through 1~n-1, sum all the divisors
	li $t1, 0         # $t1 = sum
	li $t2, 1         # $t2 = iterator

L1:
	rem $t3, $t0, $t2 # $t3 = n % $t2
	bnez $t3, L2      # if $t3 != 0, don't add $t2 to sum
	add $t1, $t1, $t2 # sum = sum+$t2 if reminder == 0
L2:
	add $t2, $t2, 1
	blt $t2, $t0, L1  # continue loop if $t2 < n

	blt $t1, $t0, DEF # sum of divisors < n
	bgt $t1, $t0, ABU # sum of divisors > n
	la $a0, str_p     # load the address of string "perfect"
	b print
DEF:
	la $a0, str_d     # load "deficient"
	b print
ABU:
	la $a0, str_a     # load "abundant"
print:
	li $v0, 4
	syscall           # print the loaded string
#	move $a0, $t1
#	li $v0, 1
#	syscall

end:
	li $v0, 10
	syscall
