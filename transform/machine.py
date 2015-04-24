#transformation of machin IR
import IR.instruction as IRI
import IR.mod as mod
import IR.operand as opr
from utils import _str_set, _str_dict, get_father, link
import logging
from . import set_log_phase, unset_log_phase
callee_saved = set([opr.Register("s%d" % i) for i in range(0, 10)])
def jump_block_removal(func, fmap):
#    set_log_phase("jbr"+func.name)
    logging.info(func)
    jmap = {}
    changed = False
    assert func.is_machine_ir, "JBR can only be performed on machine IR"
    for bb in func.bb:
        jmap[bb.name] = bb.name
    for bb in func.bb:
        if bb.ins or bb.br.tgt[1]:
            continue
        if not bb.br.tgt[0]:
            continue
        changed = True
        logging.info("Link %s -> %s", bb.name, bb.br.tgt[0])
        link(bb.br.tgt[0], bb.name, jmap)
    if not changed:
        #unset_log_phase()
        return (False, func)
    nfn = mod.Func(func.name, func.param, func.rety)
    b0 = get_father(func.bb[0].name, jmap)
    logging.info("Entry BB is now %s", b0)
    nbb = mod.BB(b0, func.bbmap[b0])
    def redir(br):
        for x in range(0, 2):
            oldtgt = br.tgt[x]
            if not oldtgt:
                continue
            br.tgt[x] = get_father(oldtgt, jmap)
            logging.info("Redirect %s to %s", oldtgt, br.tgt[x])
    redir(nbb.br)
    nfn += [nbb]
    for bb in func.bb:
        rdir = get_father(bb.name, jmap)
        if rdir != bb.name:
            continue
        if bb.name == b0:
            continue
        nbb = mod.BB(bb.name, bb)
        redir(nbb.br)
        nfn += [nbb]
    logging.info(nfn)
    nfn.machine_finish(fmap)
    #unset_log_phase()
    return (True, nfn)

def branch_merge(func, fmap):
    #if both target of a branch instruction is the same
    #replace it with unconditional jump
    #set_log_phase("bm"+func.name)
    logging.info(func)
    nfn = mod.Func(func.name, func.param, func.rety)
    assert func.is_machine_ir
    changed = False
    for bb in func.bb:
        if bb.br.tgt[1] != bb.br.tgt[0]:
            nfn += [mod.BB(bb.name, bb)]
            continue
        if not bb.br.tgt[0]:
            nfn += [mod.BB(bb.name, bb)]
            continue
        changed = True
        logging.info(bb.br)
        nxbb = mod.BB(bb.name)
        nxbb += bb.ins
        nxbb += [IRI.Br(0, None, bb.br.tgt[0], None)]
        nfn += [nxbb]
    nfn.machine_finish(fmap)
    #unset_log_phase()
    return (changed, nfn)

def get_stack_usage(ins):
    reg_sp = opr.Register("sp")
    if isinstance(ins, IRI.Load) and ins.m.is_mem and ins.m.base == reg_sp:
        return ins.m.off
    if isinstance(ins, IRI.Store) and ins.dst.base == reg_sp:
        return ins.dst.off
    return -1

def local_stack_alloc(func, fmap):
    assert func.is_machine_ir
    stack_top = -1
    for bb in func.bb:
        for i in bb.ins:
            su = get_stack_usage(i)
            if su > stack_top:
                stack_top = su
    if stack_top < 0:
        return (False, func)

    stack_top += 4
    #shift stack point upon entry
    nfn = mod.Func(func.name, func.param, func.rety)
    bb = mod.BB(func.name+"_Llocal")
    bb += [IRI.Arithm('-', "$sp", "$sp", stack_top)]
    bb += [IRI.Br(0, None, func.bb[0].name, None)]
    nfn += [bb]
    for bb in func.bb:
        if not isinstance(bb.br, IRI.Ret):
            nxbb = mod.BB(bb.name, bb)
            nfn += [nxbb]
            continue
        nbb = mod.BB(bb.name)
        nbb += bb.ins
        #shift stack pointer back before return
        nbb += [IRI.Arithm('+', "$sp", "$sp", stack_top)]
        nbb += [bb.br]
        nfn += [nbb]
    nfn.machine_finish(fmap)
    return (True, nfn)

def save_registers(func, fmap):
    #must be called after local_stack_alloc
    set_log_phase("save_reg"+func.name)
    reg_changed = {}
    self_reg_changed = {}
    for bb in func.bb:
        self_reg_changed[bb.name] = set()
        for i in bb.ins:
            if isinstance(i, IRI.Invoke):
                self_reg_changed[bb.name] |= {opr.Register("ra")}
            self_reg_changed[bb.name] |= i.get_dfn()&callee_saved
        reg_changed[bb.name] = self_reg_changed[bb.name]

    queue = set([bb.name for bb in func.bb if reg_changed[bb.name]])
    if not queue:
        unset_log_phase()
        return (False, func)

    while queue:
        bbname = queue.pop()
        for succ in func.bbmap[bbname].succs:
            if succ is None:
                continue
            nchanged = reg_changed[bbname]|reg_changed[succ]
            if nchanged != reg_changed[succ]:
                reg_changed[succ] = nchanged
                queue |= {succ}

    all_reg_changed = set()
    for n in self_reg_changed:
        all_reg_changed |= self_reg_changed[n]
    logging.info(_str_set(all_reg_changed))

    nfn = mod.Func(func.name, func.param, func.rety)
    #store everything changed onto stack
    bb = mod.BB(func.name+"_Lsave")
    bb += [IRI.Arithm('-', "$sp", "$sp", len(all_reg_changed)*4)]
    offset = 0
    offsetof = {}
    for reg in all_reg_changed:
        bb += [IRI.Store(opr.Cell(offset), reg)]
        offsetof[reg] = offset
        offset += 4
    bb += [IRI.Br(0, None, func.bb[0].name, None)]

    nfn += [bb]
    for bb in func.bb:
        if not isinstance(bb.br, IRI.Ret):
            nxbb = mod.BB(bb.name, bb)
            nfn += [nxbb]
            continue
        #restore register before return
        nbb = mod.BB(bb.name)
        nbb += bb.ins
        for reg in reg_changed[bb.name]:
            nbb += [IRI.Load(reg, opr.Cell(offsetof[reg]))]
        nbb += [IRI.Arithm('+', "$sp", "$sp", len(all_reg_changed)*4)]
        nbb += [bb.br]
        nfn += [nbb]
    nfn.machine_finish(fmap)
    unset_log_phase()
    return (True, nfn)

def return_value(func, fmap):
    if func.rety == opr.Type('void'):
        return (False, func)
    nfn = mod.Func(func.name, func.param, func.rety)
    for bb in func.bb:
        if not isinstance(bb.br, IRI.Ret):
            nxbb = mod.BB(bb.name, bb)
            nfn += [nxbb]
            continue
        assert not bb.br.retval.is_nil
        assert bb.br.retval.is_reg, bb.br.retval
        nbb = mod.BB(bb.name)
        nbb += bb.ins
        nbb += [IRI.Arithm('+', "$v0", bb.br.retval, 0)]
        nbb += [bb.br]
        nfn += [nbb]
    nfn.machine_finish(fmap)
    return (True, nfn)

