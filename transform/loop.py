def get_loop(head, tail):
    queue = {tail}
    visited = {tail}
    loop_part = [tail]
    while queue:
        h = queue.pop()
        print(h.name)
        loop_part.append(h)
        for p in h.preds:
            if head not in p.avail:
                continue
            if p in visited:
                continue
            queue |= {p}
            visited |= {p}
    return loop_part
def get_loops(fn):
    loop = {}
    for bb in fn.bb:
        succ_set = set(bb.succs)
        for head in succ_set&bb.avail:
            if head not in loop:
                loop[head] = [head]
            loop[head]+=get_loop(head, bb)
    return loop

