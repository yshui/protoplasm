from parser import parser
from IR import IR
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
    wf = res.wellformed(None, set())
    logging.info(wf)
    if not wf:
        logging.error("Program not wellformed")
        sys.exit(1)
    ir = IR()
    ir.append_bb(None)
    res.emit(None, ir)
    logging.info("\n\nFisrt version of IR: ")
    ir.finish()
    logging.info(ir);
    logger.removeHandler(lhdlr)
    changed, ir = transform.static_branch_removal(ir)
    if not changed:
        _, ir = transform.prune_unreachable(ir)
    _, ir = transform.prune_unused(ir)
    _, ir = transform.block_coalesce(ir)
    _, ir = transform.variable_rename(ir)
    #changed = True
    #while changed:
    _, ir = transform.allocate(ir)
    _, ir = transform.jump_block_removal(ir)
    _, ir = transform.branch_merge(ir)
    _, ir = transform.block_coalesce(ir, 1)
    outf = re.sub(r'\.[^.]*$', '.asm', sys.argv[1])
    logger.addHandler(lhdlr)
    logging.info("\n\nAfter register allocation:")
    logging.info(ir)
    ir.gencode(outf)
