import logging
def _str_set(a):
    res = "set("
    for b in a:
        res += str(b)+", "
    res += ")"
    return res
def _str_dict(d):
    res = "{"
    for k, v in d.items():
        res += ", %s: %s" % (k, v)
    res += "}"
    return res
def _dict_print(d):
    logging.debug(_str_dict(d))
def _set_print(a):
    logging.debug(_str_set(a))

class DisjointSet:
    def __init__(self, i):
        self.parent = self
        self.i = i
        self.h = 1
    def union(self, other): #merge other into self
        po = other.get_father()
        ps = self.get_father()
        if po.h > ps.h:
            ps.parent = po
            po.i = ps.i
            ps.i = None
        else :
            po.parent = ps
            po.i = None
            if po.h == ps.h:
                ps.h += 1
    def get_father(self):
        if self.parent != self:
            self.parent = self.parent.get_father()
        return self.parent
