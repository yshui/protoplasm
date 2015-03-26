from IR import IR, BB, Arithm, Phi, Var, Cell, all_reg
from collections import deque
import copy
def empty_block_removal(ir):
    jmap = {}
    stack = []
    nir = IR()
    for bb in ir.bb:
        assert not bb.phi, "Can perform block removal when bb has phinodes"
        if not bb.ins:
            #empty block
            stack.append(bb)
        else :
            while stack:
                ebb = stack.pop()
                jmap[ebb.name] = bb.name
    for bb in ir.bb:
        if not bb.ins:
            continue
        if not bb.br or bb.br.tgt not in jmap:
            nir += [bb]
            continue
        nbb = BB(bb.name)
        nbb += bb.nonbr_ins
        nbr = copy.copy(bb.br)
        nbr.tgt = jmap[nbr.tgt]
        nbb += [nbr]
        nir += [nbb]
    print(nir)
    nir.finish()
    return nir

def block_coalesce(ir):
    removed = set()
    nir = IR()
    for bb in ir.bb:
        if bb.name in removed:
            continue
        if len(bb.successors) != 1:
            nir += [bb]
            continue
        succ, = bb.successors
        succ = ir.bbmap[succ]
        if len(succ.predecessors) > 1:
            nir += [bb]
            continue
        assert bb.name in succ.predecessors
        if succ.phi:
            nir += [bb]
            continue
        nbb = BB(bb.name+succ.name)
        nbb += bb.nonbr_ins
        nbb += succ.ins
        nir += [nbb]
        removed |= {nbb.name}
    nir.finish()

    return nir
def chain_breaker(ir):
    print(ir)
    nir = IR()
    for bb in ir.bb:
        print("======%s======" % bb.name)
        if not bb.In and not bb.phi:
            print("No phi, no in, continue")
            nir += [bb]
            continue
        nbb = BB(bb.name)
        #add phi nodes
        broken = set()
        varmap = {}
        if len(bb.predecessors) > 1:
            #create phi node to grab the replaced
            #variable from different preds
            print("Generate additional phi")
            for v in bb.In:
                nphi = Phi("%"+v+"."+bb.name)
                for p in bb.predecessors:
                    pp = ir.bbmap[p]
                    if v in pp.In:
                        nphi.set_source(p, "%"+v+"."+p)
                    else :
                        nphi.set_source(p, "%"+v)
                print(nphi)
                nbb += [nphi]
                varmap[v] = Var(v+"."+bb.name)
            print("Rewrite original phi")
            for phi in bb.phi:
                print("%s: %s" % (bb.name, phi))
                for srcbb, v in phi.srcs.items():
                    if v.is_imm:
                        continue
                    sbb = ir.bbmap[srcbb]
                    assert v.is_var
                    if v.val in sbb.In:
                        print("%s in %s's In, change name to %s" % (v.val, srcbb, v.val+"."+srcbb))
                        phi.set_source(srcbb, "%"+v.val+"."+srcbb)
                    else :
                        print("%s not in %s's In" % (v.val, srcbb))
                print(phi)
        else :
            #only one pred, but now the in variables might have changed
            print("Single pred, rewrite var name")
            if not bb.predecessors:
                print(bb.In)
                print(bb.phi)
                print(not bb.In and not bb.phi)
            pred, = bb.predecessors
            pred = ir.bbmap[pred]
            varmap = {}
            for v in bb.In:
                if v in pred.In:
                    varmap[v] = Var(v+"."+pred.name)
        for i in bb.nonbr_ins:
            ni = copy.copy(i)
            ni.allocate(varmap)
            nbb += [ni]
        passthrou = bb.In&bb.out
        if len(bb.predecessors) == 1 and passthrou:
            pred, = bb.predecessors
            pred = ir.bbmap[pred]
            for v in passthrou:
                vname = "%"+v
                if v in pred.In:
                    vname += "."+pred.name
                nbb += [Arithm('+', "%"+v+"."+bb.name, vname, 0)]
        if bb.br:
            nbr = copy.copy(bb.br)
            nbr.allocate(varmap)
            nbb += [nbr]
        nir += [nbb]
    nir.finish()
    print(nir)
    for bb in nir.bb:
        assert not bb.In or len(bb.predecessors) == 1
        assert not (bb.In&bb.out), "%s: %s" %(bb.name, bb.In&bb.out)
    return nir

def any_reg(avail_reg):
    'return any register, but prefer registers that are not being used'
    if avail_reg:
        return avail_reg.pop()
    return next(iter(all_reg))

def promote(v, avail_reg, vrmap, rvmap, ret, mem):
    reg = any_reg(avail_reg)
    if not ret[v]:
        ret[v] = deque([reg])
    else :
        ret[v].append(reg)
    if reg in rvmap:
        mem |= {rvmap[reg]}
        vrmap[rvmap[reg]] = Cell(0)
    rvmap[reg] = v
    vrmap[v] = reg

def allocate_bb(bb, bbmap):
    #allocate for phi
    ret = {}
    avail_reg = set(all_reg)
    rvmap = {}
    vrmap = {}
    mem = set()
    only_pred = None
    if len(bb.predecessors)==1:
        only_pred, = bb.predecessors
        only_pred = bbmap[only_pred]
    for v in bb.In:
        assert v in only_pred.out_reg
        vreg = only_pred.out_reg[v]
        vrmap[v] = vreg
        if vreg.is_reg:
            avail_reg -= {vreg}
            rvmap[vreg] = v
        else :
            mem |= {v}
    #register preference:
    #reg in srcs not used > other reg not used > reg in srcs used > other reg used
    for phi in bb.phi:
        reg = None #reg in srcs not used
        reg2 = None #reg in srcs used
        for phibb, v in phi.srcs.items():
            pbb = bbmap[phibb]
            if v not in pbb.out_reg:
                #the pbb is not allocated yet
                continue
            srcreg = pbb.out_reg[v]
            if srcreg.is_reg:
                if srcreg in avail_reg:
                    reg = srcreg
                    break
                else :
                    reg2 = srcreg
        if not reg:
            if avail_reg:
                reg = avail_reg.pop()
            elif reg2:
                reg = reg2
            else :
                reg = next(iter(all_reg))
        ret[phi.dst] = deque([reg])
        avail_reg -= {reg}
        if reg in rvmap:
            mem |= {rvmap[reg]}
            vrmap[rvmap[reg]] = Cell(0)
        rvmap[reg] = phi.dst
        vrmap[phi.dst] = reg
    if bb.phi:
        mem_phi = list(mem)

    for i in bb.ins:
        if i.is_phi:
            continue
        d, = i.get_dfn()
        u = i.get_used()
        for v in u:
            assert(v in vrmap)
            if v in mem:
                promote(v, avail_reg, vrmap, rvmap, ret, mem)

        dreg = None
        for v in i.last_use:
            dreg = vrmap[v]
            avail_reg |= vrmap[v]
            del rvmap[vrmap[v]]
            del vrmap[v]
        if len(i.last_use) == 1:
            #reuse the operand register
            rvmap[dreg] = d
            vrmap[d] = dreg
            ret[d] = deque([dreg])
            avail_reg -= {dreg}
        else :
            #more than one or none, reuse does not make sense
            promote(d, avail_reg, vrmap, rvmap, ret, mem)

    return (ret, mem_phi)

def allocate(ir):
    total_pred = {}
    total_avail = {}
    allocated_pred = {}
    allocated_avail = {}
    allocation = {}
    in_mem_phi = {}
    for bb in ir.bb:
        total_pred[bb.name] = len(bb.predecessors)
        total_avail[bb.name] = len(bb.availbb)
        allocated_pred[bb.name] = 0
        allocated_avail[bb.name] = 0

    queue = set([bb for bb in ir.bb if total_pred[bb.name] == 0])
    queue2 = set([bb for bb in ir.bb if total_avail[bb.name] == 0])
    queue2 -= queue
    while queue:
        h = queue.pop()
        hbb = ir.bbmap[h]
        #allocate bb
        allocation[h], in_mem_phi[h] = allocate_bb(hbb, ir)
        for nbb in hbb.successors:
            allocated_pred[nbb] += 1
            if allocated_pred[nbb] == total_pred[nbb]:
                queue |= {nbb}
        for dbb in hbb.dombb:
            allocated_avail[dbb] += 1
            if allocated_avail[dbb] == total_avail[dbb] and dbb not in queue:
                queue2 |= {dbb}
        if not queue:
            #queue empty, add all bb whose availbb is allocated
            queue = queue2
            queue2 = set()

    nir = IR()
    for bb in ir.bb:
        #generate new ir with registers
        pass
