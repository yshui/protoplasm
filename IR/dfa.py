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

