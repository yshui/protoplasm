from .operand import Register, Nil, Type, get_operand
from utils import _str_dict, _str_set
import logging

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
        assert not self.dst.is_var or self.dst.dst, self
        return self.dst.get_dfn()
    def validate(self, *_):
        pass
    def machine_validate(self, _):
        pass

class GetAddrOf(NIns):
    def __init__(self, dst, src, c=None):
        self.dst = get_operand(dst, True)
        self.src = get_operand(src)
        self.comment = ""
        if c is not None :
            self.comment = "\t#"+c
        assert self.src.is_glob
    def get_used(self):
        return set()
    def gencode(self, _):
        return "\tla %s, %s\n" % (self.dst, self.src.get_name())
    def allocate(self, varmap, dst=True):
        if dst:
            self.dst = self.dst.allocate(varmap)
    def machine_validate(self, _):
        assert self.dst.is_reg
    def __str__(self):
        return "%s = getaddrof %s%s" % (self.dst, self.src, self.comment)

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
    def machine_validate(self, _):
        assert False, "rename is not allowed in machine IR"
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
    def gencode(self, _):
        if self.opr1.is_imm and self.opr2.is_imm:
            assert False
        if self.opr2.is_imm:
            if self.opr2.val == 0 and self.opr1 == self.dst:
                logging.info("%s is NOP" % self)
                return ""
        elif self.opr1.is_imm:
            if self.op in {1, 3, 6, 7}:
                #swap opr1 and opr2 for +, *, &, |
                self.opr1, self.opr2 = self.opr2, self.opr1

        res = ""
        opr1 = self.opr1
        if opr1.is_imm:
            if opr1.val == 0:
                opr1 = Register("0")
            else :
                res += "\tli $v0, %d\n" % opr1.val
                opr1 = Register("v0")
        assert opr1.is_reg
        assert self.opr2.is_reg or self.opr2.is_imm
        return res+"\t%s %s, %s, %s\n" % (self.opname[self.op], self.dst, opr1, self.opr2)

    def __init__(self, op, dst, opr1, opr2, c=None):
        assert op in self.opc
        self.ops = {v:k for k, v in self.opc.items()}
        self.op = self.opc[op]
        self.dst = get_operand(dst, True)
        self.opr1 = get_operand(opr1)
        self.opr2 = get_operand(opr2)
        self.comment = ""
        if c is not None :
            self.comment = "\t#"+c

    def allocate(self, regmap, dst=True):
        if dst:
            self.dst = self.dst.allocate(regmap)
        self.opr1 = self.opr1.allocate(regmap)
        self.opr2 = self.opr2.allocate(regmap)
    def machine_validate(self, _):
        self.opr1.machine_validate()
        self.opr2.machine_validate()
        self.dst.machine_validate()
    def __str__(self):
        res = "%s = %s %s, %s" % (self.dst, self.opname[self.op], str(self.opr1), str(self.opr2))
        res += gen_rvmap(self.dst, self.opr1, self.opr2)
        return res+self.comment
    def get_used(self):
        return self.opr1.get_used()|self.opr2.get_used()

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
    iopc = {0: 0, 1: 3, 2: 4, 3: 1, 4: 2, 5: 5}
    def gencode(self, _):
        assert self.dst.is_reg
        if self.opr1.is_imm and self.opr2.is_imm:
            assert False
        if self.opr1.is_imm:
            assert self.opr2.is_reg
            return "\t%s %s, %s, %s\n" % (self.opname[self.iopc[self.op]], str(self.dst), str(self.opr2), str(self.opr1))
        else :
            assert self.opr1.is_reg, self.opr1
            assert self.opr2.is_reg or self.opr2.is_imm
            return "\t%s %s, %s, %s\n" % (self.opname[self.op], str(self.dst), str(self.opr1), str(self.opr2))
    def __init__(self, op, dst, src1, src2, c=None):
        assert op in self.opc
        self.ops = {v:k for k, v in self.opc.items()}
        self.op = self.opc[op]
        self.opr1 = get_operand(src1)
        self.opr2 = get_operand(src2)
        self.dst = get_operand(dst, True)
        self.is_phi = False
        self.is_br = False
        self.comment = ""
        if c is not None :
            self.comment = "\t#"+c
    def allocate(self, regmap, dst=True):
        rrr = _str_dict(regmap)
        if dst:
            self.dst = self.dst.allocate(regmap)
        self.opr1 = self.opr1.allocate(regmap)
        self.opr2 = self.opr2.allocate(regmap)
    def get_used(self):
        return self.opr1.get_used()|self.opr2.get_used()
    def machine_validate(self, _):
        self.opr1.machine_validate()
        self.opr2.machine_validate()
        self.dst.machine_validate()
    def __str__(self):
        res = "%s = cmp %s %s, %s" % (self.dst, self.opname[self.op], self.opr1, self.opr2)
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
    def tgt_validate(self, allname):
        for i in range(0, len(self.tgt)):
            if self.tgt[i] is None:
                continue
            assert self.tgt[i] in allname, self.tgt[i]
    def validate(self, allname, _):
        self.tgt_validate(allname)
    def machine_validate(self, allname):
        self.tgt_validate(allname)
        assert self.src.is_reg or self.src.is_nil
    def allocate(self, regmap, _=True):
        logging.debug(_str_dict(regmap))
        self.src = self.src.allocate(regmap)
    def get_dfn(self):
        return set()
    def get_used(self):
        return self.src.get_used()
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
    def allocate(self):
        assert False
    def validate(self, preds):
        for pred in preds:
            assert pred.name in self.srcs, "Predessor %s not handled in phi %s" % (pred.name, self)
        assert len(preds) == len(self.srcs), "%s %s" % (preds, self)
    def __str__(self):
        res = "%s = phi " % self.dst
        for x, y in self.srcs.items():
            res += "[ %s: %s ], " % (x, y)
        return res[:-2]

def load_or_move(src, dst):
    assert dst.is_reg
    if src.is_imm:
        return "\tli "+str(dst)+", "+str(src)+"\n"
    elif src.is_reg:
        return "\tadd %s, %s, 0\n" % (str(dst), str(src))
    else :
        assert src.is_mem
        return "\tlw %s, %s\n" % (str(dst), src)

def move_or_store(src, dst):
    assert src.is_reg, src
    res = ""
#    if src.is_imm:
#        res += "\tli $v0, %s\n" % str(src)
#        src = Register("v0")
    if dst.is_reg:
        res += "\tadd %s, %s, 0\n" % (dst, src)
    else :
        res += "\tsw %s, %s\n" % (src, dst)
    return res

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
    def allocate(self, regmap, dst=True):
        if dst:
            self.dst = self.dst.allocate(regmap)
        self.m = self.m.allocate(regmap)
    def get_used(self):
        return self.m.get_used()|self.dst.get_used()
    def gencode(self, _):
        return load_or_move(self.m, self.dst)
    def machine_validate(self, _):
        self.dst.machine_validate()
        self.m.machine_validate()

class Store(NIns):
    def __init__(self, dst, r, c=None):
        self.dst = get_operand(dst)
        assert self.dst.is_mem
        self.r = get_operand(r)
        assert self.r.is_reg or self.r.is_var
        self.comment = ""
        if c is not None :
            self.comment = "\t#"+c
    def allocate(self, regmap, _=True):
        self.r = self.r.allocate(regmap)
        self.dst = self.dst.allocate(regmap)
    def gencode(self, _):
        return move_or_store(self.r, self.dst)
    def machine_validate(self, _):
        self.dst.machine_validate()
        self.r.machine_validate()
    def get_used(self):
        return self.r.get_used()|self.dst.get_used()
    def __str__(self):
        return "store %s, %s%s" % (self.dst, self.r, self.comment)

class Ret:
    def __init__(self, retval=None):
        self.used = True
        self.is_br = True
        self.is_phi = False
        self.tgt = [None, None]
        self.tgtbb = [None, None]
        self.src = Nil()
        self.retval = get_operand(retval)
    def allocate(self, varmap, _=True):
        self.retval = self.retval.allocate(varmap)
    def gencode(self, _):
        return "\tjr $ra\n"
    def validate(self, _, rety):
        if rety == Type("void") :
            assert self.retval.is_nil
        else :
            assert not self.retval.is_nil
    def machine_validate(self, bbmap):
        self.retval.machine_validate()
    def get_used(self):
        return self.retval.get_used()
    def get_dfn(self):
        return set()
    def __str__(self):
        return "ret %s" % self.retval
    def get_rodata(self):
        return set()

class Invoke(NIns):
    def __init__(self, name, args, dst, c=None):
        self.name = name
        self.name_mangled = ""
        self.args = [get_operand(arg) for arg in args]
        self.dst = get_operand(dst, True)
        self.comment = ""
        if c is not None :
            self.comment = "\t#"+c
    def validate(self, fmap):
        assert self.name in fmap
        assert fmap[self.name].rety == self.dst.get_type() or self.dst.is_nil
        assert len(self.args) == len(fmap[self.name].param), fmap[self.name].param
    def get_used(self):
        res = set()
        for arg in self.args:
            logging.info("%s %s", arg, type(arg))
            res |= arg.get_used()
        return res
    def __str__(self):
        res = "%s = invoke %s [" % (self.dst, self.name)
        for arg in self.args:
            res += str(arg)+", "
        if self.args:
            res = res[:-2]
        res += "]"+self.comment
        return res
    def allocate(self, varmap, dst=True):
        logging.info("Invoke before: %s", self)
        if dst:
            self.dst = self.dst.allocate(varmap)
        logging.info("Invoke varmap: "+_str_dict(varmap))
        self.args = [arg.allocate(varmap) for arg in self.args]
        logging.info("Invoke after: %s", self)
    def machine_validate(self, fmap):
        assert self.name in fmap
        self.name_mangled = fmap[self.name].mangle()
        self.dst.machine_validate()
        return True
    def gencode(self, _):
        #4 arguments are passed via a0-a3
        res = ""
        res += "\tjal %s\n" % self.name_mangled
        if not self.dst.is_nil:
            res += "\tadd %s, $v0, 0\n" % self.dst
        return res

