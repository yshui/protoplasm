import IR.operand as opr

class Allocator:
    def __init__(self):
        self.ver = {}
        self.ver[0] = -1
    def next_name(self, prefix=None):
        if prefix is None :
            self.ver[0] += 1
            return "%%%d" % self.ver[0]
        prefix = str(prefix)
        if prefix not in self.ver:
            self.ver[prefix] = 0
        else :
            self.ver[prefix] += 1
        return "%%%s.%d" % (prefix, self.ver[prefix])

class DupErr(Exception):
    def __init__(self, name, linenum=0):
        self.name = name
        self.linenum = linenum
        Exception.__init__(self)

class SymTable:
    #this class is used to keep track of variable version
    #since we are using SSA here
    def __init__(self, globs=None, dlist=None, prototype=None):
        self.t = {}
        self.d = {}
        self.prototype = prototype
        self.modified = {}
        self.mstack = []
        if prototype:
            self.allocator = prototype.allocator
            self.globs = prototype.globs
        else :
            self.allocator = Allocator()
            self.globs = globs
        if dlist:
            for d in dlist:
                if d.name in self.d:
                    raise DupErr(d.name, d.linenum)
                self.d[d.name] = None
                self.t[d.name] = d

    def __contains__(self, other):
        if other in self.d:
            return True
        if not self.prototype:
            return False
        return other in self.prototype

    def cp_push(self):
        #restart nonlocal variable accounting
        self.mstack.append(self.modified)
        self.modified = {}

    def cp_pop(self):
        m = self.modified
        if self.mstack:
            self.modified = self.mstack.pop()
            for v in m:
                if v not in self.modified:
                    self.modified[v] = m[v]
        else :
            self.modified = {}
        ret = {}
        for v in m:
            ret[v] = (self.curr_ver(v), m[v])
        return ret

    def cp_revert(self):
        #revert to last check point
        m = self.modified
        self.modified = {}
        ret = {}
        for v in m:
            ret[v] = (self.curr_ver(v), m[v])
            if m[v] is not None:
                self.assign(v, m[v])
            else :
                self.unassign(v)
        if self.mstack:
            self.modified = self.mstack.pop()
        else :
            self.modified = {}
        return ret

    def get_dclr(self):
        res = set(self.d.keys())
        if self.prototype:
            res |= self.prototype.get_dclr()
        return res

    def get_dfn(self): #get all possibly initialized variable
        res = set([x for x in self.d if self.d[x] is not None])
        if self.prototype:
            res |= self.prototype.get_dfn()
        return res

    def is_initialized(self, name):
        if name in self.d:
            return self.d[name] is not None
        assert self.prototype
        return self.prototype.is_initialized(name)

    def assign(self, name, var):
        assert isinstance(name, str)
        if name not in self.modified:
            if self.is_initialized(name):
                self.modified[name] = self.curr_ver(name)
            else :
                self.modified[name] = None
        if name not in self.d:
            return self.prototype.assign(name, var)
        self.d[name] = str(var)

    def get_ty(self, name):
        if name not in self:
            return None
        if name in self.t:
            return self.t[name].ty
        return self.prototype.get_ty(name)

    def unassign(self, name):
        if name in self.modified:
            assert self.modified[name] is None
            del self.modified[name]
        if name not in self.d:
            return self.prototype.unassign(name)
        self.d[name] = None

    def curr_ver(self, name):
        assert isinstance(name, str)
        if name not in self.d:
            assert self.prototype, name
            return self.prototype.curr_ver(name)
        assert self.d[name] is not None
        return str(self.d[name])

    def __str__(self):
        return "All: %s, modified: %s" % (self.d, self.modified)

class Type:
    def __init__(self, name):
        self.name = name
    def __str__(self):
        return self.name
    def __eq__(self, o):
        if type(o) is not type(self):
            return False
        return self.real_eq(o)
    def real_eq(self, o):
        return self.name == o.name
    @property
    def itype(self):
        return opr.Type('i32')

class ArrayTy(Type):
    def real_eq(self, o):
        return self.inner == o.inner
    def __init__(self, inner):
        self.inner = inner
        Type.__init__(self, "Array")
    def __str__(self):
        return "Array(%s)" % self.inner

class FnTy(Type):
    def __init__(self):
        Type.__init__(self, "Fn")
    def real_eq(self, o):
        return True
    @property
    def itype(self):
        assert False

class VoidTy(Type):
    def real_eq(self, o):
        return True
    def __init__(self):
        Type.__init__(self, "Void")
    @property
    def itype(self):
        return opr.Type('void')

def pattern_match(table, intype):
    for entry in table:
        if len(intype) != len(entry[0]):
            continue
        for i, ty in enumerate(entry[0]):
            if not (ty == intype[i]):
                break
        else :
            return entry[1]
    return None
