import logging
import IR.mod as mod

myhdlr = logging.NullHandler()
logger = logging.getLogger()

def set_log_phase(n):
    global myhdlr
    #if isinstance(myhdlr, logging.NullHandler):
    #    return
    myhdlr.close()
    myhdlr = logging.FileHandler(filename=n+".log")
    logger.addHandler(myhdlr)

def unset_log_phase():
    global myhdlr
    if isinstance(myhdlr, logging.NullHandler):
        return
    logger.removeHandler(myhdlr)

def apply_all(ir, trans):
    logging.debug(ir)
    changed = False
    nir = mod.IR()
    for f in ir.func:
        c, nfn = trans(f, ir.fmap)
        changed |= c
        nir += [nfn]
    if changed:
        nir += ir.builtin
        nir.globs = ir.globs
        return (True, nir)
    else :
        return (False, ir)
