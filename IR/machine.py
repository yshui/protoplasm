from .operand import Register
usable_reg = []
for i in range(0, 10):
    usable_reg += ["s%d" % i]
for i in range(0, 10):
    usable_reg += ["t%d" % i]

all_reg = [Register(x) for x in usable_reg]