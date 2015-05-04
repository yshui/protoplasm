from . import instruction as ins
import logging
def operand_cmp(a, b):
    xa = id(type(a))
    xb = id(type(b))
    if xa != xb:
        return xa < xb
    return a.val < b.val

def sort_operand(a, b):
    if operand_cmp(a, b):
        return (a, b)
    return (b, a)

class SubExpr:
    def __init__(self, i):
        self.i = i
        if self.eliminatable:
            logging.info("%s=%d", self, self.__hash__())
    @property
    def eliminatable(self):
        if isinstance(self.i, ins.Arithm) or isinstance(self.i, ins.Cmp):
            return True
        if isinstance(self.i, ins.GetAddrOf):
            return True
        if isinstance(self.i, ins.Load) and self.i.m.is_imm:
            return True
        return False
    def __str__(self):
        return "Sub:"+str(self.i)
    def __hash__(self):
        assert self.eliminatable
        if isinstance(self.i, ins.Load):
            return ("LoadImm", self.i.m.val).__hash__()
        if isinstance(self.i, ins.Arithm) or isinstance(self.i, ins.Cmp):
            opr1, opr2 = sort_operand(self.i.opr1, self.i.opr2)
            return (self.i.ops[self.i.op], str(opr1), str(opr2)).__hash__()
        return ("GerAddrOf", str(self.i.src)).__hash__()
    def __eq__(self, o):
        if type(self.i) != type(o.i):
            logging.info("%s != %s", type(self.i), type(o.i))
            return False
        if isinstance(self.i, ins.Load):
            return self.i.m == o.i.m
        if isinstance(self.i, ins.GetAddrOf):
            logging.info("2WTF %s == %s, %s", self.i.src, o.i.src, self.i.src==o.i.src)
            return self.i.src == o.i.src
        sopr1, sopr2 = sort_operand(self.i.opr1, self.i.opr2)
        oopr1, oopr2 = sort_operand(o.i.opr1, o.i.opr2)
        return sopr1 == oopr1 and sopr2 == oopr2

