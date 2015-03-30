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
