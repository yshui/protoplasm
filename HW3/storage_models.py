from IR import Cell, Var, Register, Load, Store, all_reg
class Registers:
    def __init__(self, M=None):
        self.avail_reg = set(all_reg)
        assert self.avail_reg, "No available register found!!"
        self.vrmap = {}
        self.rvmap = {}
        self.M = M
    def __contains__(self, other):
        if other.is_reg:
            return other in self.rvmap
        elif other.is_var:
            return other in self.vrmap
        return False
    def reserve(self, var, reg):
        assert reg.is_reg
        assert reg not in self.rvmap
        assert reg in self.avail_reg
        var = Var(var.val)
        self.vrmap[var] = reg
        reg = Register(reg.val)
        self.rvmap[reg] = var
        self.avail_reg -= {reg}
    def get(self, var):
        if var in self.vrmap:
            return self.vrmap[var]
        if not self.avail_reg:
            return None
        reg = next(iter(self.avail_reg))
        self.reserve(var, reg)
        return reg
    def _dropv(self, var):
        if var not in self.vrmap:
            return
        reg = self.vrmap[var]
        del self.vrmap[var]
        self.avail_reg |= {reg}
        del self.rvmap[reg]
    def drop(self, o):
        if o.is_var:
            self._dropv(o)
        elif o.is_reg:
            if o not in self.rvmap:
                return
            self._dropv(self.rvmap[o])
        else :
            assert False
    def drop_both(self, o):
        #call when a variable is no longer alive
        assert self.M
        var = o
        if o.is_reg:
            var = self.rvmap[o]
        assert var.is_var, o
        self.drop(var)
        self.M.drop(var)
    def get_may_spill(self, var):
        assert self.M
        if var in self.vrmap:
            #the requested var is already in some register
            return (self.vrmap[var], [])
        ins = []
        reg = self.get(var)
        if not reg:
            #no reg found
            #spill any register, later we might impl LRU policy
            reg = next(iter(self.rvmap))
            var = self.rvmap[reg]
            self.drop(var)
            self.reserve(var, reg)
            e, mcell = self.M.get(var)
            if not e:
                ins.append(Store(mcell, reg))
        #if already in memory
        if var in self.M:
            ins = [Load(reg, self.M.get(var))]
        else :
            #it is not in vrmap before, and it is not in memory either
            #must be a newly defined dst
            assert var.dst
        return (reg, ins)

class Memory:
    def __init__(self):
        self.top = 0
        self.avail = set()
        self.rsrv = set()
        self.vmmap = {}
        self.mvmap = {}
    def __contains__(self, other):
        if other.is_mem:
            return other.val in self.mvmap
        elif other.is_var:
            return other in self.vmmap
        return False
    def __str__(self):
        res = "Range: [0, %s), Available: " % self.top
        for m in self.avail:
            res += "%d, " % m
        res += "Reserved: "
        for m in self.rsrv:
            res += "%d, " % m
        return res
    def reserve(self, var, pos):
        print("Reserve %s -> %s" % (var, pos))
        assert pos.is_mem
        assert pos.val not in self.mvmap, "%s %s %s" % (var, pos, self.mvmap[pos.val])
        var = Var(var.val)
        self.vmmap[var] = Cell(pos.val)
        self.mvmap[pos.val] = var
        pos = pos.val
        if pos < self.top:
            assert pos in self.avail
            self.avail -= {pos}
            return
        self.rsrv |= {pos}
    def get(self, var):
        if var in self.vmmap:
            return (True, self.vmmap[var])
        var = Var(var.val)
        if self.avail:
            self.vmmap[var] = Cell(self.avail.pop(), var)
        else :
            while self.top in self.rsrv:
                self.rsrv -= {self.top}
                self.top += 1
            self.vmmap[var] = Cell(self.top, var)
            self.top += 1
        self.mvmap[self.vmmap[var].val] = var
        return (False, self.vmmap[var])
    def _dropv(self, var):
        if var not in self.vmmap:
            return
        pos = self.vmmap[var].val
        del self.vmmap[var]
        del self.mvmap[pos]
        if pos in self.rsrv:
            self.rsrv -= {pos}
            return
        if pos == self.top-1:
            self.top -= 1
            return
        self.avail |= {pos}
    def drop(self, o):
        if o.is_mem:
            if o.val not in self.mvmap:
                return
            self._dropv(self.mvmap[o.val])
        elif o.is_var:
            self._dropv(o)
        else :
            assert False, o
