from IR.mod import BuiltinFn
from IR.operand import Type
print_int = BuiltinFn("print_int", "\tli $v0, 1\n\tsyscall\n\tjr $ra\n", Type('void'), 1)
print_str = BuiltinFn("print_str", "\tli $v0, 4\n\tsyscall\n\tjr $ra\n", Type('void'), 1)
input_int = BuiltinFn("input_int", "\tli $v0, 5\n\tsyscall\n\tjr $ra\n", Type('i32'), 0)
builtin_exit = BuiltinFn("exit", "\tli $v0, 10\n\tsyscall\n", Type('void'), 0)

builtins = [print_int, print_str, input_int, builtin_exit]
