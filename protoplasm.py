from parser import parser
from IR import IR
from ast import VarVer
import transform
import sys
import logging
import re
import pdb

if __name__ == "__main__":
    f = open(sys.argv[1], "r")
    logger = logging.getLogger()
    logger.setLevel(logging.WARNING)
    lhdlr = logging.StreamHandler(stream=sys.stderr)
    logger.addHandler(lhdlr)
    res = parser.parse(f.read(), debug=logger)
    logger.setLevel(logging.INFO)
    logging.info(res)
    wf = res.wellformed(set())
    logging.info(wf)
    if not wf:
        logging.error("Program not wellformed")
        sys.exit(1)
    ir = IR()
    ir.append_bb(None)
    varv = VarVer()
    res.emit(varv, ir)
    logging.info("\n\nFisrt version of IR: ")
    ir.finish()
    logger.removeHandler(lhdlr)
    _, ir = transform.prune_unused(ir)
    _, ir = transform.chain_breaker(ir)
    #changed = True
    #while changed:
    _, ir = transform.allocate(ir)
    _, ir = transform.jump_block_removal(ir)
    _, ir = transform.branch_merge(ir)
    _, ir = transform.block_coalesce(ir)
#    ir.allocate()
#    print(ir)
    outf = re.sub(r'\.[^.]*$', '.asm', sys.argv[1])
    logger.addHandler(lhdlr)
    logging.info("\n\nAfter register allocation:")
    logging.info(ir)
    ir.gencode(outf)
