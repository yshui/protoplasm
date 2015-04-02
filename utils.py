def _str_set(a):
    res = "set("
    for b in a:
        res += str(b)+", "
    res += ")"
    return res
def _dict_print(d):
    res = "{"
    for k, v in d.items():
        res += ", %s: %s" % (k, v)
    res += "}"
    print(res)
def _set_print(a):
    print(_str_set(a))

def get_father(x, p):
    if p[x] == x:
        return x
    p[x] = get_father(p[x], p)
    return p[x]
def union(x, y, p, h):
    px = get_father(x, p)
    py = get_father(y, p)
    if h[px] > h[py]:
        p[py] = px
    else:
        p[px] = py
        if h[px] == h[py]:
            h[py] += 1

def link(x, y, p):
    py = get_father(y, p)
    p[py] = get_father(x, p)
