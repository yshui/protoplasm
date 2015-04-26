from IR.instruction import Arithm, Load, Store
from IR.operand import Register, Cell
from utils import _str_dict, _str_set
from IR.machine import arg_regs
import logging
def arg_passing(nbb, args, R):
    #TODO Make this method more generic, use it on phi as well

    #some explain: one source can conflict with only one target
    #one target can only conflict with only one source. Because
    #all source and target have distinct register/memory. So
    #when the mover can't progress, there must be a circle. More
    #over, if a source variable V with storage S can't be moved,
    #V itself must be in a circle. So move V into a temp storage
    #would break the circle, and everything in the circle will
    #become possible to move. And this temp storage will immediate
    #become free to use. We can use $v0 for this temp storage, and
    #$v1 for memory to memory moves
    logging.info(args)
    crmap = {}
    cv = set()
    for arg in args:
        if arg in R and R.vrmap[arg] in arg_regs:
            crmap[R.vrmap[arg]] = arg
            cv |= {arg}

    #other things is passed via stack
    for n, arg in enumerate(args[3:]):
        tmem = Cell(-4*(n+1))
        if arg.is_imm:
            nbb += [Load("$v0", arg.val)]
            src = Register("v0")
        elif arg not in R:
            nbb += [Load("$v0", R.M.vmmap[arg])]
            src = Register("v0")
        else :
            src = R.vrmap[arg]
        nbb += [Store(tmem, src)]
        if arg in cv:
            del crmap[src]
            cv -= {arg}

    logging.info("Conflict variable: "+_str_set(cv))
    logging.info("Conflict register: "+_str_dict(crmap))

    tgt = {}
    src = {}
    for n, arg in enumerate(args[:4]):
        treg = Register("a%d" % n)
        logging.info("WWWT"+_str_dict(R.vrmap))
        if arg in R:
            tgt[arg] = treg
            src[arg] = R.vrmap[arg]
            continue
        if arg.is_imm:
            nbb += [Load(treg, arg.val)]
        else :
            assert arg in R.M.vmmap, _str_dict(R.M.vmmap)
            nbb += [Load(treg, R.M.vmmap[arg])]

    v0_inuse = False
    while tgt:
        progress = False
        done = set()
        for arg in tgt:
            if tgt[arg] not in crmap:
                logging.info("Move %s(%s) to %s, %s", arg, src[arg], tgt[arg], _str_dict(crmap))
                nbb += [Arithm('+', tgt[arg], src[arg], 0)]
                done |= {arg}
                if src[arg] == Register("v0"):
                    v0_inuse = False
                elif arg in cv:
                    cv -= {arg}
                    del crmap[src[arg]]
                progress = True
            else :
                logging.info("Cannot move %s(%s) to %s, because target conflict with %s", arg, src[arg], tgt[arg], crmap[tgt[arg]])
        if progress:
            for a in done:
                del tgt[a]
            continue
        assert not v0_inuse
        to_move = next(iter(tgt))
        nbb += [Arithm('+', "$v0", src[arg], 0)]
        del crmap[src[arg]]
        src[arg] = Register("v0")
        v0_inuse = True

