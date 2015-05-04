#transformation of machin IR
import IR.instruction as IRI
import IR.mod as mod
import IR.operand as opr
from utils import _str_set, _str_dict
import logging
from . import set_log_phase, unset_log_phase
callee_saved = set([opr.Register("s%d" % i) for i in range(0, 10)])


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
    bb = mod.BB(func.mangle()+"_Llocal")
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
        self_reg_changed[bb] = set()
        for i in bb.ins:
            if isinstance(i, IRI.Invoke):
                self_reg_changed[bb] |= {opr.Register("ra")}
            self_reg_changed[bb] |= i.get_dfn()&callee_saved
        reg_changed[bb] = self_reg_changed[bb]

    queue = set([bb for bb in func.bb if reg_changed[bb]])
    if not queue:
        unset_log_phase()
        return (False, func)

    while queue:
        bb = queue.pop()
        for succ in bb.succs:
            nchanged = reg_changed[bb]|reg_changed[succ]
            if nchanged != reg_changed[succ]:
                reg_changed[succ] = nchanged
                queue |= {succ}

    all_reg_changed = set()
    for n in self_reg_changed:
        all_reg_changed |= self_reg_changed[n]
    logging.info(_str_set(all_reg_changed))

    nfn = mod.Func(func.name, func.param, func.rety)
    #store everything changed onto stack
    bb = mod.BB(func.mangle()+"_Lsave")
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
        for reg in reg_changed[bb]:
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
        nbb = mod.BB(bb.name)
        nbb += bb.ins
        if bb.br.retval.is_reg:
            nbb += [IRI.Arithm('+', "$v0", bb.br.retval, 0)]
        else :
            assert bb.br.retval.is_imm
            nbb += [IRI.Load("$v0", bb.br.retval.val)]
        nbb += [bb.br]
        nfn += [nbb]
    nfn.machine_finish(fmap)
    return (True, nfn)

