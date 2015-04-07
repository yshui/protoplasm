import copy
from utils import _str_set, _str_dict, _dict_print, _set_print
from functools import reduce
import logging

usable_reg = []
for __i in range(0, 2):
    usable_reg += ["t{0}".format(__i)]
def gen_rvmap(*arg):
    #res = ""
    #for v in arg:
        #if not v or v.is_nil:
            #continue
        #if not v.is_reg and not v.is_mem:
            #continue
        #if v.xvar:
            #res += "%s->%s, " % (v.xvar, v)
    #if res:
        #return "  #"+res
    return ""

class BaseOpr:
    @property
    def is_reg(self):
        return isinstance(self, Register)
    @property
    def is_var(self):
        return isinstance(self, Var)
    @property
    def is_imm(self):
        return isinstance(self, Imm)
    @property
    def is_mem(self):
        return isinstance(self, Cell)
    @property
    def is_nil(self):
        return False
    def get_rodata(self):
        return set()

class Cell(BaseOpr):
    def __init__(self, off, base=None, var=None):
        if not base:
            self.base = Register("sp")
        else :
            self.base = get_operand(base)
        assert self.base.is_reg or self.base.is_var
        self.off = off
        assert isinstance(off, int)
        self.xvar = var
    def __eq__(self, other):
        if not isinstance(other, Cell):
            return False
        return self.off == other.off and self.base == other.base
    def __hash__(self):
        return str.__hash__(str(self))
    def validate(self, dfn):
        return True
    def get_dfn(self):
        return set()
    def __str__(self):
        return "%d(%s)" % (self.off, self.base)
    def get_used(self):
        return self.base.get_used()
    def allocate(self, regmap):
        #allocate register for base
        nbase = self.base.allocate(regmap)
        return Cell(self.off, base=nbase)

class Register(BaseOpr):
    def __eq__(self, other):
        if not isinstance(other, Register):
            return False
        return other.val == self.val
    def __hash__(self):
        return str(self).__hash__()
    def __init__(self, val, var=None):
        self.val = val
        self.used = True
        self.xvar = var
    def validate(self, dfn):
        return True
    def get_dfn(self):
        return set()
    def __str__(self):
        return "$"+self.val
    def get_used(self):
        return set()
    def allocate(self, _):
        assert False, "Cannot allocate register for a register %s" % self

class Imm(BaseOpr):
    def __init__(self, number):
        assert isinstance(number, int)
        self.val = number
    def validate(self, dfn):
        return True
    def get_dfn(self):
        assert False
    def __str__(self):
        return str(self.val)
    def __hash__(self):
        return str.__hash__("Imm(%s)" % self.val)
    def __eq__(self, other):
        if not isinstance(other, Imm):
            return False
        return self.val == other.val
    def get_used(self):
        return set()
    def allocate(self, _):
        return self


class Var(BaseOpr):
    def __init__(self, var, dst=False):
        self.val = var
        self.dst = dst
        self.used = False
    def validate(self, dfn):
        if not self.dst:
            assert self in dfn, "%s not defined" % self
        else :
            assert self not in dfn
    def get_dfn(self):
        assert self.dst
        return {self}
    def __str__(self):
        return "%"+self.val
    def __hash__(self):
        return str(self).__hash__()
    def __eq__(self, other):
        if not isinstance(other, Var):
            return False
        return self.val == other.val
    def get_used(self):
        if self.dst:
            return set()
        return {self}
    def allocate(self, regmap):
        #assert self.val in regmap
        if self in regmap:
            regmap[self].xvar = self
            return regmap[self]
        return self

class Nil:
    def __init__(self, var=0, dst=0):
        self.is_nil = True
    def validate(self, dfn):
        return True
    def get_dfn(self):
        return set()
    @property
    def val(self):
        assert False
    def __str__(self):
        return "Nil()"
    def get_used(self):
        return set()
    def allocate(self, _):
        return self
    def get_rodata(self):
        return set()

def get_operand(val, dst=False):
    if isinstance(val, Nil) or isinstance(val, Var) or isinstance(val, Register) or isinstance(val, Cell) or isinstance(val, Imm):
        if dst :
            assert (val.is_var and val.dst) or val.is_reg
        return val
    if dst :
        assert isinstance(val, str), val
        assert val[0] == '%'
    if val is None :
        return Nil()
    if isinstance(val, int):
        return Imm(val)
    assert isinstance(val, str), val
    if val[0] == '%':
        return Var(val[1:], dst)
    return Register(val)

class BaseIns:
    last_use = None #Which variable is used the last time in this instructions
    def get_used(self):
        assert False, self
    def get_rodata(self):
        return set()

class NIns(BaseIns):
    'Normal instructions, not end of basic block or phi'
    is_br = False
    is_phi = False
    def __init__(self):
        self.dst = None
    def get_dfn(self):
        return self.dst.get_dfn()

class Rename(NIns):
    def __init__(self, dst, src, c=""):
        self.dst = get_operand(dst, True)
        self.src = get_operand(src)
        self.comment = ""
        if c is not None :
            self.comment = "\t#"+c
        assert self.src.is_var, src
        assert self.dst.is_var, dst
    def get_used(self):
        return self.src.get_used()
    def gencode(self):
        assert False
    def allocate(self):
        assert False
    def validate(self, dfn):
        self.dst.validate(dfn)
        self.src.validate(dfn)
    def __str__(self):
        return "%s = rename %s%s" % (self.dst, self.src, self.comment)


class Arithm(NIns):
    opc = {"+": 1, "-": 2, "*": 3, "//": 4, "%": 5, "&": 6, "|": 7}
    opname = {
            1 : 'add',
            2 : 'sub',
            3 : 'mul',
            4 : 'div',
            5 : 'rem',
            6 : 'and',
            7 : 'or',
    }
    def gencode(self):
        if self.opr1.is_imm and self.opr2.is_imm:
            assert False
        if self.opr2.is_imm:
            if self.opr2.val == 0 and self.opr1 == self.dst:
                logging.info("%s is NOP" % self)
                return ""
        assert self.opr1.is_reg
        assert self.opr2.is_reg or self.opr2.is_imm
        return "\t%s %s, %s, %s\n" % (self.opname[self.op], str(self.dst), str(self.opr1), str(self.opr2))

    def __init__(self, op, dst, opr1, opr2, c=None):
        assert op in self.opc
        self.op = self.opc[op]
        self.dst = get_operand(dst, True)
        self.opr1 = get_operand(opr1)
        self.opr2 = get_operand(opr2)
        self.comment = ""
        if c is not None :
            self.comment = "\t#"+c
        if self.opr1.is_imm:
            if self.opr1.val == 0:
                #use the 0 register
                self.opr1 = Register("r0")
            elif self.op in {1, 3, 6, 7}:
                #swap opr1 and opr2 for +, *, &, |
                self.opr1, self.opr2 = self.opr2, self.opr1
            else :
                #otherwise fail
                assert False

    def allocate(self, regmap):
        self.dst = self.dst.allocate(regmap)
        self.opr1 = self.opr1.allocate(regmap)
        self.opr2 = self.opr2.allocate(regmap)
    def validate(self, dfn):
        self.opr1.validate(dfn)
        self.opr2.validate(dfn)
        self.dst.validate(dfn)
    def __str__(self):
        res = "%s = %s, %s, %s" % (self.dst, self.opname[self.op], str(self.opr1), str(self.opr2))
        res += gen_rvmap(self.dst, self.opr1, self.opr2)
        return res+self.comment
    def get_used(self):
        return self.opr1.get_used()|self.opr2.get_used()

class IInpt(NIns):
    def __init__(self, dst, c=None):
        self.comment = ""
        if c is not None :
            self.comment = "\t#"+c
        if dst is None:
            self.dst = Nil()
        else :
            self.dst = get_operand(dst, True)
    def validate(self, dfn):
        self.dst.validate(dfn)
    def allocate(self, regmap):
        self.dst = self.dst.allocate(regmap)
    def get_used(self):
        return set()
    def gencode(self):
        out = "\tli $v0, 5\n\tsyscall\n"
        if not self.dst.is_nil:
            assert self.dst.is_reg
            out += "\tadd %s, $v0, 0\n" % str(self.dst)
        return out
    def __str__(self):
        return "%s = input%s" % (self.dst, self.comment)

class ROStr:
    def __init__(self, s):
        self.s = s
    def validate(self, _):
        return True
    def allocate(self, _):
        return self
    def get_used(self):
        return set()
    def get_rodata(self):
        return {self.s}
    def __str__(self):
        return "\"%s\"" % self.s

class IPrnt(NIns):
    def __init__(self, var, c=None):
        if not isinstance(var, ROStr):
            self.var = get_operand(var)
        else :
            self.var = var
        self.comment = ""
        if c is not None :
            self.comment = "\t#"+c
    def validate(self, dfn):
        self.var.validate(dfn)
    def allocate(self, regmap):
        self.var = self.var.allocate(regmap)
    def get_dfn(self):
        return set()
    def get_rodata(self):
        return self.var.get_rodata()
    def __str__(self):
        return "print %s%s" % (self.var, self.comment)
    def get_used(self):
        return self.var.get_used()
    def gencode(self, ir):
        out = ""
        if isinstance(self.var, ROStr):
            out += "\tli $v0, 4\n\tla $a0, %s\n\tsyscall\n" % ir.rodata[self.var.s]
            return out
        if self.var.is_reg:
            out += "\tadd $a0, %s, 0\n" % str(self.var)
        else :
            assert self.var.is_imm
            out += "\tli $a0, %s\n" % str(self.var)
        out += "\tli $v0, 1\n\tsyscall\n"
        return out

class Cmp(NIns):
    '0 : seq'
    opname = {
            0 : "seq",
            1 : "sle",
            2 : "slt",
            3 : "sge",
            4 : "sgt",
            5 : "sne"
    }
    opc = {'==': 0, '<=': 1, '<' : 2, '>=': 3, '>' : 4, '!=': 5}
    iopc = {0: 0, 1: 4, 2: 3, 3: 2, 4: 1, 5: 5}
    def gencode(self, _):
        assert self.dst.is_reg
        if self.src1.is_imm and self.src2.is_imm:
            assert False
        if self.src1.is_imm:
            assert self.src2.is_reg
            return "\t%s %s, %s, %s\n" % (self.opname[self.iopc[self.op]], str(self.dst), str(self.src2), str(self.src1))
        else :
            assert self.src1.is_reg, self.src1
            assert self.src2.is_reg or self.src2.is_imm
            return "\t%s %s, %s, %s\n" % (self.opname[self.op], str(self.dst), str(self.src1), str(self.src2))
    def __init__(self, op, src1, src2, dst, c=None):
        assert op in self.opc
        self.op = self.opc[op]
        self.src1 = get_operand(src1)
        self.src2 = get_operand(src2)
        self.dst = get_operand(dst, True)
        self.is_phi = False
        self.is_br = False
        self.comment = ""
        if c is not None :
            self.comment = "\t#"+c
    def allocate(self, regmap):
        rrr = _str_dict(regmap)
        print(rrr)
        self.dst = self.dst.allocate(regmap)
        self.src1 = self.src1.allocate(regmap)
        self.src2 = self.src2.allocate(regmap)
    def get_used(self):
        return self.src1.get_used()|self.src2.get_used()
    def validate(self, dfn):
        self.src1.validate(dfn)
        self.src2.validate(dfn)
        self.dst.validate(dfn)
    def __str__(self):
        res = "%s = cmp %s %s, %s" % (self.dst, self.opname[self.op], self.src1, self.src2)
        return res+self.comment

class Br(BaseIns):
    '0 : j, 1 : beqz, 2 : bnez'
    brname = {
            0 : "j",
            1 : "beqz",
            2 : "bnez",
    }
    def __init__(self, op, src, target, target2, c=None):
        self.src = get_operand(src)
        self.tgt = [target, target2]
        self.op = op
        self.is_br = True
        self.is_phi = False
        self.used = True
        self.comment = ""
        if c is not None :
            self.comment = "\t#"+c
        if src is not None and self.src.is_imm:
            #static branch
            self.op = 0
            bv = self.src.val
            self.src = Nil()
            if (bv == 0 and op == 1) or (bv != 0 and op == 2):
                self.tgt = [target, None]
            else :
                self.tgt = [target2, None]
    def validate(self, dfn):
        self.src.validate(dfn)
    def allocate(self, regmap):
        logging.debug(regmap)
        self.src = self.src.allocate(regmap)
    def get_dfn(self):
        return set()
    def get_used(self):
        if self.src:
            return self.src.get_used()
        return set()
    def gencode(self, nextbb):
        if self.op == 0:
            if self.tgt[0] != nextbb:
                return "\tb "+self.tgt[0]+"\n"
            else :
                return ""
        assert self.src.is_reg, self
        res = "\t%s %s, %s\n" % (self.brname[self.op], self.src, self.tgt[0])
        if self.tgt[1] != nextbb:
            res += ("\tb %s\n" % self.tgt[1])
        return res
    def __str__(self):
        if not self.src.is_nil :
            res = "br %s %s, [ %s, %s ]" % (self.brname[self.op], self.src, self.tgt[0], self.tgt[1])
        else :
            res = "br %s [ %s ]" % (self.brname[self.op], self.tgt[0])
        res += gen_rvmap(self.src)
        return res+self.comment

class Phi:
    def __init__(self, dst, *arg):
        if len(arg)%2 :
            raise Exception("Wrong number of arg for Phi")
        it = iter(arg)
        self.srcs = {}
        for x in it:
            self.srcs[x] = get_operand(next(it))
        self.is_phi = True
        self.is_br = False
        self.dst = get_operand(dst, True)
    @property
    def used(self):
        return self.dst.used
    def set_source(self, bb, src):
        self.srcs[bb] = get_operand(src)
    def del_source(self, bb):
        del self.srcs[bb]
    def get_dfn(self):
        return self.dst.get_dfn()
    def allocate(self, regmap):
        self.dst = self.dst.allocate(regmap)
    def validate(self, bb, bbmap):
        for src, var in self.srcs.items():
            #does src point to us?
            logging.debug("{0} does point to us".format(src))
            #are we referring to ourselves?
            #assert not var == self.dst, "Phi %s -> %s" % (var, self.dst)
            #is var defined in src?
            _dfn = bbmap[src].internal_dfn|bbmap[src].avail_dfn
            var.validate(_dfn)
            logging.debug("{0} is defined in {1}".format(var, src))
        for pred in bb.preds:
            assert pred in self.srcs
        assert len(bb.preds) == len(self.srcs), "%s %s" % (bb, self)
    def __str__(self):
        res = "%s = phi " % self.dst
        for x, y in self.srcs.items():
            res += "[ %s: %s ], " % (x, y)
        return res[:-2]
    def get_rodata(self):
        return set()

def is_stack_pointer(r):
    if not r.is_reg:
        return False
    return r.val == "sp"

def load_or_move(src, dst):
    assert dst.is_reg
    if src.is_imm:
        return "\tli "+str(dst)+", "+str(src)+"\n"
    elif src.is_reg:
        return "\tadd %s, %s, 0\n" % (str(dst), str(src))
    else :
        return "\tlw %s, %s\n" % (str(dst), src)

def move_or_store(src, dst):
    assert src.is_reg
    if dst.is_reg:
        return "\tadd %s, %s, 0\n" % (dst, src)
    else :
        return "\tsw %s, %s\n" % (src, dst)

def get_stack_usage(ins):
    if isinstance(ins, Load) and ins.m.is_mem and is_stack_pointer(ins.m.base):
        return ins.m.off
    if isinstance(ins, Store) and is_stack_pointer(ins.dst.base):
        return ins.dst.off
    return -1

class Load(NIns):
    def __init__(self, dst, m, c=None):
        self.dst = get_operand(dst, True)
        assert not self.dst.is_imm
        self.m = get_operand(m)
        assert self.m.is_mem or self.m.is_imm
        self.is_phi = False
        self.is_br = False
        self.comment = ""
        if c is not None :
            self.comment = "\t#"+c
    def __str__(self):
        return "%s = load %s%s" % (self.dst, self.m, self.comment)
    def allocate(self, regmap):
        self.dst = self.dst.allocate(regmap)
    def get_used(self):
        return set()
    def gencode(self, _):
        return load_or_move(self.m, self.dst)
    def validate(self, dfn):
        self.dst.validate(dfn)

class Store(NIns):
    def __init__(self, dst, r, c=None):
        self.dst = get_operand(dst)
        assert self.dst.is_mem
        self.r = get_operand(r)
        assert self.r.is_reg or self.r.is_var
        self.comment = ""
        if c is not None :
            self.comment = "\t#"+c
    def allocate(self, regmap):
        self.r = self.r.allocate(regmap)
        self.dst = self.dst.allocate(regmap)
    def gencode(self, _):
        return move_or_store(self.r, self.dst)
    def validate(self, dfn):
        self.r.validate(dfn)
    def get_used(self):
        return self.r.get_used()
    def __str__(self):
        return "store %s, %s%s" % (self.dst, self.r, self.comment)

class Malloc(NIns):
    def __init__(self, dst, size, c=None):
        self.dst = get_operand(dst, True)
        assert self.dst.is_var or self.dst.is_reg
        self.size = get_operand(size)
        assert not self.size.is_mem
        self.comment = ""
        if c is not None :
            self.comment = "\t#"+c
    def allocate(self, regmap):
        self.dst = self.dst.allocate(regmap)
        self.size = self.size.allocate(regmap)
    def validate(self, dfn):
        self.dst.validate(dfn)
        self.size.validate(dfn)
    def get_used(self):
        return self.size.get_used()
    def __str__(self):
        return "%s = malloc %s%s" % (self.dst, self.size, self.comment)
    def gencode(self, _):
        res = "\tli $v0, 9\n"
        if self.size.is_imm:
            res += "\tli $a0, %d\n" % (self.size.val)
        else :
            assert self.size.is_reg
            res += "\tadd $a0, %s, 0\n" % (self.size)
        res += "\tsyscall\n"
        assert self.dst.is_reg
        res += "\tadd %s, $v0, 0\n" % (self.dst)
        return res

class Ret:
    def __init__(self):
        self.used = True
        self.is_br = True
        self.is_phi = False
        self.tgt = [None, None]
    def allocate(self, _):
        return
    def gencode(self, nextbb):
        return "\tjr $ra\n"
    def validate(self, _):
        return True
    def get_used(self):
        return set()
    def get_dfn(self):
        return set()
    def __str__(self):
        return "ret"
    def get_rodata(self):
        return set()

class BB:
    '''
    Last and only the last instruction can be Br
    Phi instructions must be at the beginning of a bb
    '''
    def __str__(self):
        res = self.name+":\n"
        res += "#availbb: "+str(self.availbb)+"\n"
        res += "#pred: "+str(self.preds)+"\n"
        res += "#succ: "+str(self.succs)+"\n"
        res += "#In: "+_str_set(self.In)+"\n"
        if self.required:
            res += "#Required: "+str(self.required)+"\n"
        for i in self.phis:
            res += "\t"+str(i)+"\n"
        for i in self.ins:
            res += "\t"+str(i)+"\n"
        res += "\t"+str(self.br)+"\t#end\n"
        res += "#Out: "+_str_set(self.out)+"\n"
        if self.out_reg:
            res += "#Out_reg: \n"
            for k, v in self.out_reg.items():
                res += str(k)+": "+str(v)+", "
            res += "\n"
        return res
    def gencode(self, ir, nextbb):
        res = self.name+":\n"
        assert not self.phis
        for i in self.ins:
            res += i.gencode(ir)
        res += self.br.gencode(nextbb)
        return res
    def __hash__(self):
        return self.name.__hash__()
    def __eq__(self, other):
        return self is other
    def __init__(self, name, bb=None):
        #dfn is variable defined in all paths lead to this bb
        self.ins = []
        self.phis = []
        self.name = name
        self.avail_done = False
        self.inout_done = False
        self.br = None
        self.in_dfn = set() #in_dfn = definitions in this bb
        self.a_dfn = set() #available definitions
        self.in_used = set()
        self.succs = [] #next[0] = branch taken, next[1] = otherwise
        self.preds = []
        self.validated = False
        self.availbb = set()
        self.out = set()
        self.In = set()
        self.out_reg = {}
        self.required = set()
        self.dombb = set()
        self.stack_top = 0
        self.rodata = set()
        if bb:
            self += bb.phis
            self += bb.ins
            self += [bb.br]

    def avail_next(self, bbmap, queue):
        if not self.preds:
            availbb_next = set()
        else :
            pabb = [bbmap[pbb].availbb|{pbb} for pbb in self.preds]
            availbb_next = reduce(lambda x, y: x&y, pabb)
        if availbb_next != self.availbb:
            for nbb in self.succs:
                if nbb:
                    queue |= {nbb}
            self.availbb = set(availbb_next)

    def avail_finish(self, bbmap):
        self.avail_done = True
        for prevbb in self.availbb:
            pbb = bbmap[prevbb]
            self.a_dfn |= pbb.internal_dfn
            pbb.dombb |= {self.name}

    @property
    def internal_used(self):
        if self.in_used:
            return self.in_used
        for i in self.ins+[self.br]:
            self.in_used |= i.get_used()
        return self.in_used

    def inout_next(self, bbmap, queue):
        self.In = (self.out|self.internal_used)-self.internal_dfn
        visited = set()
        for prevbb in self.preds:
            sbb = bbmap[prevbb]
            new_out = sbb.out|self.In
            for i in self.phis:
                srcu = i.srcs[prevbb].get_used()
                new_out |= srcu
            if new_out != sbb.out:
                sbb.out = new_out
                queue |= {prevbb}

    def inout_finish(self, bbmap):
        self.inout_done = True
        for abb in self.availbb:
            aabb = bbmap[abb]
            if aabb.out&self.In:
                self.required |= {abb}

    def __iadd__(self, _ins):
        ins = copy.copy(_ins)
        while ins:
            assert not self.br, "Appending instruction after end of BB %s" % self
            i = ins.pop(0)
            stk = get_stack_usage(i)
            if stk >= self.stack_top:
                self.stack_top = stk+4
            if i.is_phi:
                if self.ins:
                    raise Exception("Phi instructions in the middle of a BB")
                self.phis.append(i)
            else :
                if i.is_br:
                    self.br = i
                    self.succs = i.tgt
                else :
                    self.ins.append(i)
                    self.rodata |= i.get_rodata()
        return self
    @property
    def avail_dfn(self):
        if not self.avail_done:
            raise Exception("Call calc_avail before get avail_dfn")
        return self.a_dfn
    @property
    def internal_dfn(self):
        if self.in_dfn:
            return self.in_dfn
        for i in self.phis+self.ins:
            self.in_dfn |= i.get_dfn()
        return self.in_dfn
    def finish(self):
        assert self.br
    def validate(self, bbmap):
        #with the help of available dfn
        #we can make sure all of the variables used in this bb
        #is always defined on all the paths leading to this bb
        self.validated = True
        _dfn = copy.copy(self.a_dfn)
        #skip phi instructions, only get their defines
        #because phi instruction can grab a variable defined later in this bb
        for i in self.phis:
            i.validate(self, bbmap)
            _dfn |= i.get_dfn()
        #validate other instructions
        for i in self.ins:
            i.validate(_dfn)
            _dfn |= i.get_dfn()
    def liveness(self):
        #we assume there're no unreachable code
        #we have a pruning pass to make sure of that
        alive = set(self.out)
        for i in reversed(self.ins+[self.br]):
            u = i.get_used()
            i.last_use = set()
            for v in u:
                if v not in alive:
                    i.last_use |= {v}
                    alive |= {v}
            ds = i.get_dfn()
            if ds:
                d, = ds
                alive -= {d}

    def assign_out_reg(self, R):
        for v in self.out:
            assert v in R or v in R.M, "%s not allocated" % v
            self.out_reg[v] = R.get_reg_or_mem(v)

class IR:
    def __str__(self):
        res = "\n\n==========================IR============================\n"
        for bb in self.bb:
            res += str(bb)
        return res

    def __init__(self, bb=None):
        if bb:
            self.bb = copy.copy(bb)
        else :
            self.bb = []
        self.bbmap = {}
        self.namecnt = 0
        self.stack_top = 0
        self.rodata = {}
        self.rodatacnt = 0

    def __iadd__(self, o):
        for i in o:
            assert i.name not in self.bbmap, "Basic blocks with duplicated name "+i.name+str(self.bbmap)
            self.bbmap[i.name] = i
            self.bb.append(i)
            if i.stack_top > self.stack_top:
                self.stack_top = i.stack_top
            for d in i.rodata:
                if d not in self.rodata:
                    self.rodata[d] = "rodata%d" % self.rodatacnt
                    self.rodatacnt += 1
        return self

    def next_name(self):
        res = "L"+str(self.namecnt)
        self.namecnt += 1
        return res

    def append_bb(self, name):
        if not name:
            name = self.next_name()
        r = BB(name)
        self += [r]
        return r

    def calc_connections(self):
        for i in self.bb:
            for succ in i.succs:
                if not succ:
                    continue
                assert succ in self.bbmap, "Jumping to a non-existent block %s" % succ
                self.bbmap[succ].preds.append(i.name)

    def calc_avail(self):
        #calculate blocks that are 'available' to this bb
        #the definition of 'available' is the same as in the slides
        #the 'available' variable would than be all variable defined in available blocks
        init = set(self.bbmap.keys())
        for bb in self.bb:
            bb.availbb = init
        queue = {self.bb[0].name}
        while queue :
            h = queue.pop()
            self.bbmap[h].avail_next(self.bbmap, queue)
        for bb in self.bb:
            bb.avail_finish(self.bbmap)

    def calc_inout(self):
        queue = set()
        for bb in self.bb:
            bb.In = set()
            bb.out = set()
            queue |= {bb.name}
        while queue:
            h = queue.pop()
            self.bbmap[h].inout_next(self.bbmap, queue)
            #print("%s: new In %s, new out %s" % (h, self.bbmap[h].In, self.bbmap[h].out))
        for bb in self.bb:
            bb.inout_finish(self.bbmap)

    def gencode(self, fname):
        f = open(fname, 'w')
        f.write(".data\n")
        for d, n in self.rodata.items():
            assert isinstance(d, str)
            f.write("%s: .asciiz \"%s\"\n" % (n, d))
        f.write(".text\nmain:\n")
        #shift the stack pointer
        if self.stack_top > 0:
            f.write("\tsub $sp, $sp, %d\n" % (self.stack_top))
        numbb = len(self.bb)
        for n, bb in enumerate(self.bb):
            nextbb = None
            if n+1 < numbb:
                nextbb = self.bb[n+1].name
            f.write(bb.gencode(ir, nextbb))
        f.close()
    def finish(self):
        logging.debug(self)
        for bb in self.bb:
            bb.finish()
        self.calc_connections()
        self.calc_avail()
        logging.info(self)
        self.validate()
        self.calc_inout()
        for bb in self.bb:
            bb.liveness()

    @property
    def last_bb(self):
        return self.bb[-1]
    def validate(self):
        for i in self.bb:
            i.validate(self.bbmap)

all_reg = [Register(x) for x in usable_reg]
