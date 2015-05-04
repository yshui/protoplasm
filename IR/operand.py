
class Type:
    def __init__(self, ty):
        if ty == "i32":
            self.ty = 1
        else :
            assert ty == "void"
            self.ty = 0
    def __eq__(self, o):
        assert isinstance(o, Type), o
        return self.ty == o.ty
    def __str__(self):
        tyname = ['void', 'i32']
        return tyname[self.ty]

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
        return isinstance(self, Nil)
    @property
    def is_glob(self):
        return isinstance(self, Global)
    def get_rodata(self):
        return set()
    def get_type(self):
        if not isinstance(self, Nil):
            return Type("i32")
        return Type("void")
    def machine_validate(self):
        if self.is_mem:
            self.base.machine_validate()
            return True
        if self.is_reg or self.is_imm or self.is_nil:
            return True
        assert False, "Operand %s not allowed in machine IR" % self

class Global(BaseOpr):
    def __init__(self, name):
        self.name = name
    def __eq__(self, o):
        return self.name == o.name
    def __hash__(self):
        return str(self).__hash__()
    def __str__(self):
        return "@"+self.name
    def get_name(self):
        return "_G_"+self.name

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
        assert self.base.is_var or self.base == Register("sp"), "Comparing %s %s " % (self, other)
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
        return {self}
    def __str__(self):
        return "$"+self.val
    def get_used(self):
        return set()
    def allocate(self, regmap):
        assert self not in regmap, "Cannot allocate register for a register %s" % self
        return self

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
            assert self not in dfn, self
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

class Nil(BaseOpr):
    def __init__(self, var=0, dst=0):
        pass
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
    def get_type(self):
        return Type("void")

def get_operand(val, dst=False):
    if type(val) in {Nil, Var, Register, Cell, Imm, Global}:
        if dst :
            assert (val.is_var and val.dst) or val.is_reg
        return val
    if val is None :
        return Nil()
    if dst :
        assert isinstance(val, str), val
        assert val[0] == '%' or val[0] == '$', val
    if isinstance(val, int):
        return Imm(val)
    assert isinstance(val, str), val
    if val[0] == '%':
        return Var(val[1:], dst)
    if val[0] == '$':
        return Register(val[1:])
    if val[0] == '@':
        return Global(val[1:])
    assert False, val
