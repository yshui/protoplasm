from collections import deque
import logging
def _str_bb_list(a):
    res = ""
    for bb in a:
        if isinstance(bb, str):
            res += bb+", "
        else :
            res += bb.name+", "
    if a:
        res = res[:-2]
    return res
def dfa_run(fn, transfer, d, top, reverse=True):
    '''top: Is the top the whole set? top = False means top = empty set'''
    queue = set(fn.bb)

    for bb in fn.bb:
        d[bb] = top

    while queue:
        h = queue.pop()
        changed = transfer(h, d)
        if changed:
            n = h.succs
            if reverse:
                n = h.preds
            queue |= set(n)

def walk_dominator_tree(fn, transfer, d, top):
    queue = deque([fn.bb[0]])
    parent = {}
    parent[fn.bb[0]] = None
    changed = False
    for bb in fn.bb:
        d[bb] = top
    while queue:
        h = queue.popleft()
        if transfer(h, parent[h], d):
            changed = True
        tmp = h.avail | {h}
        for succ in h.sub:
            if succ.avail == tmp:
                #logging.info("Doing %s after %s", succ.name, h.name)
                parent[succ] = h
                queue.append(succ)
                #logging.info("Not doing %s after %s, because %s != %s+%s", succ.name, h.name, _str_bb_list(succ.avail), _str_bb_list(h.avail), h.name)
    return changed
