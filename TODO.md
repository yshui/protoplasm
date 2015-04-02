#Course Assignment
## Array support

We need to make Load/Store take variable operands.

#Improvements I would like to do
##NOP removal

it can be as simple as removing single NOP instructions, or as complex as tracking the result of each instruction. So for instructions like:

```
add $t0, $t1, 0
add $t1, $t0, 0
```

We can remove the second instruction
