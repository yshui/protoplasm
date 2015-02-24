#!/usr/bin/env python
import tokenize
import sys
import re

def error(st):
  raise Exception("Unexpected {0}({1}) at {2}, {3}".
                  format(st[1], st[0], st[2][0], st[2][1]))

ins_name = ["INPUT", "ADD", "SUB", "MUL", "DIV", "MOD", "MOVE", "PRINT",
            "STORE", "LOAD"]
ins_realname = [
    "",
    "add",
    "sub",
    "mul",
    "div",
    "rem",
    ]
usable_reg = []
nreg = 2

class Ins:
  rassigned = False
  mem = -1
  mused = set()
  @property
  def idef(self):
    assert(not self.rassigned)
    return self._def
  @property
  def iused(self):
    assert(not self.rassigned)
    return self.used
  @property
  def iin(self):
    assert(not self.rassigned)
    return self._in
  def liveness(self, out):
    assert(not self.rassigned)
    self._in = self.used|out-self._def
  def mliveness(self, out):
    if self.opcode == 9:
      self.mused = out|{self.operands[1]}
    elif self.opcode == 8:
      self.mused = out-{self.operands[1]}
    else :
      self.mused = out
  def transform(self, vmap):
    assert(not self.rassigned)
    self.operands = [vmap[x] if x in vmap else x for x in self.operands]
    self.used = set([vmap[x] if x in vmap else x for x in self.used])
    #vmap should not change _def
    #_in is now invalid
    self._in = None
    return self
  def assign(self, rmap):
    assert(not self.rassigned)
    self.rassigned = True
    nopr = []
    for o in self.operands:
      if isinstance(o, str):
        if o not in rmap:
          rmap[o] = 0
        nopr += [usable_reg[rmap[o]]]
      else :
        nopr += [o]
    self.operands = nopr
  def gencode(self, f):
    opc = self.opcode
    if opc == 0:
      f.write("li $v0, 5\nsyscall\n")
      f.write("move ${0}, $v0\n".format(self.operands[0]))
    elif opc >= 1 and opc <= 5 :
      f.write("{0} ${1}, ${2},".format(ins_realname[opc],
                                      self.operands[0],
                                      self.operands[1]))
      if isinstance(self.operands[2], str):
        f.write(" ${0}\n".format(self.operands[2]))
      else :
        f.write(" {0}\n".format(self.operands[2]))
    elif opc == 6:
      if isinstance(self.operands[1], str):
        f.write("move ${0}, ${1}\n".format(self.operands[0], self.operands[1]))
      else :
        f.write("li ${0}, {1}\n".format(self.operands[0], self.operands[1]))
    elif opc == 7:
      if isinstance(self.operands[0], str):
        f.write("move $a0, ${0}\n".format(self.operands[0]))
      else :
        f.write("li $a0, {0}\n".format(self.operands[0]))
      f.write("li $v0, 1\nsyscall\n")
      f.write("li $v0, 4\nla $a0, nl\nsyscall\n")
    elif opc == 8:
      assert(self.mem >= 0)
      f.write("sw ${0}, {1}($sp)\n".format(self.operands[0], self.mem*4))
    elif opc == 9:
      assert(self.mem >= 0)
      f.write("lw ${0}, {1}($sp)\n".format(self.operands[0], self.mem*4))

  @property
  def useful(self):
    if self.masked:
      return False
    opc = self.opcode
    if opc == 1 or opc == 2 : #ADD, SUB
      if self.operands[0] == self.operands[1] and self.operands[2] == 0:
        return False
    elif opc == 3 or opc == 4 : #DIV, MUL
      if self.operands[0] == self.operands[1] and self.operands[2] == 1:
        return False
    elif opc == 6 and self.operands[0] == self.operands[1]: #MOVE
      return False
    return True

  def __str__(self):
    rst = ins_name[self.opcode]+" "
    for opr in self.operands:
      rst += str(opr)+", "
    if (self.opcode == 8 or self.opcode == 9) and self.rassigned:
      if self.mem == -1 :
        rst += "\t#memory location unassigned"
      else :
        rst += "\t#at stack+{0}".format(self.mem*4)
    if self.masked:
      rst += "(masked)"
    return rst
  def __init__(self, opc, opr, rasgned = False):
    self.opcode = opc
    self.operands = opr
    self._in = None
    self.masked = False
    self.loaded = False
    self._def = None
    self.used = None
    self.rassigned = rasgned
    if opc != 7 and opc != 8:
      self._def = set([opr[0]])
    else :
      self._def = set()
    self.used = set()
    if opc == 0: #INPUT
      assert(len(opr) == 1)
      assert(isinstance(opr[0], str))
    elif opc >= 1 and opc <= 5: #ADD, SUB, DIV, MUL, MOD
      assert(len(opr) == 3)
      assert(isinstance(opr[0], str) and isinstance(opr[1], str))
      assert(isinstance(opr[2], str) or isinstance(opr[2], int))
      self.used |= {opr[1]}
      if isinstance(opr[2], str):
        self.used |= {opr[2]}
    elif opc == 6: #MOVE
      assert(len(opr) == 2)
      assert(isinstance(opr[0], str))
      assert(isinstance(opr[1], int) or isinstance(opr[1], str))
      if isinstance(opr[1], str):
        self.used |= {opr[1]}
    elif opc == 7: #PRINT
      assert(len(opr) == 1)
      assert(isinstance(opr[0], str) or isinstance(opr[0], int))
      if isinstance(opr[0], str):
        self.used |= {opr[0]}
    elif opc == 8 or opc == 9: #LOAD, STORE pseudo instruction
      assert(len(opr)==2)
      assert(isinstance(opr[0], str))
      assert(isinstance(opr[1], int))
      if opc == 8: #STORE
        self.used = set([opr[0]])

class VarVer:
  def __init__(self):
    self.d = {}
  def next_ver(self, name):
    if name not in self.d:
      self.d[name] = 0
    else :
      self.d[name] += 1
    return name+"."+str(self.d[name])
  def curr_ver(self, name):
    assert(name in self.d)
    return name+"."+str(self.d[name])

class IR:
  ins = []
  __liveness = False
  def __init__(self):
    self.ins = []
    self.used = set([])
    self.tempv = {}
    self.scnt = 0
    self.spilt = set()
    self._rassigned = False
    self._massigned = False
    self.mmax = 0
  def liveness(self):
    #start from the last instruction
    out = set()
    g = {}
    for i in reversed(self.ins):
      #edges from used to out-def
      pairs = [(x, y) for x in i.iused for y in out-i.idef if x != y]
      #edges from used to used
      pairs += [(x, y) for x in i.iused for y in i.iused if x < y]
      #print(pairs)
      for x, y in pairs:
        if x not in g:
          g[x] = {y}
        else :
          g[x] |= {y}
        if y not in g:
          g[y] = {x}
        else :
          g[y] |= {x}
      i.liveness(out)
      out = i.iin
    return g
  def __spill(self, tgt):
    g1 = self.liveness()
    assert(len(g1[tgt]) >= nreg and tgt not in self.tempv)
    assert(tgt not in self.spilt)
    nins = []
    self.spilt |= {tgt}
    #create a new variable for each use of tgt
    count = 0
    for i in self.ins:
      if tgt in i.iused:
        neww = "{0}.{1}".format(tgt, count)
        self.tempv[neww] = tgt
        count += 1
        vmap = {}
        vmap[tgt] = neww
        nins += [Ins(9, [neww, self.scnt]), i.transform(vmap)]
      else :
        nins += [i]
      if tgt in i.idef:
        nins += [Ins(8, [tgt, self.scnt])]
    self.ins = nins
    self.scnt += 1
  def __try_alloc_register(self):
    g = self.liveness()
    print("Interference graph:\n\t")
    print(g)
    stack = []
    visited = set()
    d = {}
    for w in g:
      d[w] = len(g[w])
    while True :
      flag = False
      for w in g:
        if d[w] < nreg and w not in visited:
          flag = True
          break
      if not flag:
        if len(visited) != len(g.keys()) :
          #there are leftovers
          maxd = 0
          offending = None
          for w in g:
            if d[w] <= maxd or w in self.tempv:
              continue
            if w in self.spilt:
              continue
            maxd = d[w]
            offending = w
          return (False, offending)
        break
      visited |= {w}
      stack.append(w)
      for ww in g[w]:
        if ww not in visited:
          d[ww] -= 1
    color = {}
    while stack:
      w = stack.pop()
      available_color = set(range(0, nreg))
      for wn in g[w]:
        if wn in color:
          available_color -= {color[wn]}
      color[w] = min(available_color)
    return (True, color)
  def alloc_register(self):
    if self._rassigned:
      return
    self._rassigned = True
    while True:
      print("Trying register allocation with {0} registers...".format(nreg))
      ret, s = self.__try_alloc_register()
      print("Liveness information\nIR\t\t\tin")
      for i in self.ins:
        print("{0}\t\t\t{1}".format(i, i.iin))
      if ret:
        break
      print("Register allocation failed\nspilling {0}".format(s))
      self.__spill(s)
      print("IR after spilling {1}:\n{0}".format(self, s))
    print("Register assignment")
    for w in s:
      print("\t{0} -> {1}".format(w, usable_reg[s[w]]))
    #then assign the register
    for i in self.ins:
      i.assign(s)
    #remove NOPs
    self.ins = [x for x in self.ins if x.useful]
    print("IR after register allocation:\n{0}".format(self))
  def alloc_memory(self):
    if self._massigned:
      return
    if not self._rassigned:
      self.alloc_register()
    self._massigned = True
    mloc = {} #a certain cell's location in memory
    mi = {} #the instruction stored to a memory block
    reg = {} #keep track of what cell a reg hold
    mr = {} #keep track of which reg hold a cell
    nins = []
    def overwrite_store(src, self=self, mi=mi, mloc=mloc, reg=reg):
      purge = None
      for r in reg:
        if reg[r] in mloc:
          #find a register whose value is in memory
          purge = r
          break
      if purge:
        i = mi[mloc[reg[purge]]]
        if not i.loaded:
          i.masked = True
        mloc[reg[src]] = mloc[reg[purge]]
        del mloc[reg[purge]]
      else :
        mloc[reg[src]] = self.mmax
        self.mmax += 1
      i = Ins(8, [src, reg[src]], True)
      i.mem = mloc[reg[src]]
      mi[mloc[reg[src]]] = i
      return i
    #calculate memory cell liveness
    out = set()
    for i in reversed(self.ins):
      i.mliveness(out)
      out = i.mused
    for i in self.ins:
      if i.opcode == 9: #LOAD
        dst = i.operands[0]
        src = i.operands[1]
        if dst in reg and reg[dst] == src:
          continue
        if ((dst in reg) and (reg[dst] not in mloc) and
           (reg[dst] in i.mused) and (len(mr[reg[dst]]) == 1)):
          #the register hold something that is not in memory
          #and the memory cell will be loaded later
          #emit a store
          nins += [overwrite_store(dst)]
        if dst in reg:
          mr[reg[dst]] -= {dst}
        reg[dst] = src
        if mr[src]:
          #held by a register, emit move instead
          x = mr[src].pop()
          assert(dst != x)
          nins += [Ins(6, [dst, x], True)]
          mr[src] |= {x}
        else :
          assert(src in mloc)
          i.mem = mloc[src]
          nins += [i]
          mi[mloc[src]].loaded = True
        mr[src] |= {dst}
      elif i.opcode == 8: #STORE
        src = i.operands[0]
        assert(src not in reg)
        #a new store
        reg[src] = i.operands[1]
        mr[i.operands[1]] = {src}
        #do nothing, we only emit store when necessary
      elif i.opcode >= 0 and i.opcode <= 6: #INPUT, +, -, *, /, %, MOVE
        #now reg is not holding anything
        dst = i.operands[0]
        if dst in reg:
          if (reg[dst] not in mloc and reg[dst] in i.mused and
              len(mr[reg[dst]]) == 1):
            nins += [overwrite_store(dst)]
          mr[reg[dst]] -= {dst}
          del reg[dst]
        nins += [i]
      else : #PRINT
        nins += [i]
#    self.ins = nins
#    print(self)
    self.ins = [x for x in nins if x.useful]
    print("IR after stack memory allocation:\n{0}".format(self))
  def gencode(self, fname):
    while not self._massigned:
      self.alloc_memory()
    print("Generating MIPS code...")
    f = open(fname, 'w')
    f.write(".data\nnl: .asciiz \"\\n\"\n")
    f.write(".text\nmain:\n")
    mmax = -1
    for i in self.ins:
      if i.mem > mmax:
        mmax = i.mem
    #substract %sp for memory space
    if mmax >= 0:
      f.write("sub $sp, $sp, {0}\n".format(4*(mmax+1)))
    for i in self.ins:
      i.gencode(f)
    f.write("li $v0, 10\nsyscall\n")
    f.close()
    print("Done(written to {0})".format(fname))
  def __iadd__(self, ins):
    for i in ins:
      assert(isinstance(i, Ins))
      assert(i.idef & self.used == set())
      self.used |= i.idef
      self.ins += [i]
    return self
  def __str__(self):
    rst = "[\n"
    for i in self.ins:
      rst += "\t"+str(i)+"\n"
    rst += "]"
    return rst

class Asgn:
  lhs = None
  rhs = None
  def __str__(self):
    return "Asgn({0} = {1})".format(self.lhs, self.rhs)
  def __init__(self, lhs, rhs):
    assert(isinstance(lhs, Var))
    self.lhs = lhs
    self.rhs = rhs
  @staticmethod
  def reduce(stack):
    return Asgn(Var(stack[0][1]), Expr.reduce(stack[1:]))
  def emit(self, varv):
    return self.rhs.emit(varv, self.lhs.name)


class Expr:
  lopr = None
  ropr = None
  op = None
  def emit(self, varv, dst):
    opc = {"+": 1, "-": 2, "*": 3, "//": 4, "%": 5}
    if (isinstance(self.lopr, Num)):
      if (isinstance(self.ropr, Num)):
        #Constant expr
        dst = varv.next_ver(dst)
        rst = eval(str(self.lopr.number)+self.op+str(self.ropr.number))
        return [Ins(6, [dst, rst])]
      else :
        src1 = varv.curr_ver(self.ropr.name)
        dst = varv.next_ver(dst)
        return [Ins(opc[self.op], [dst, src1, self.lopr.number])]
    else :
      if (isinstance(self.ropr, Num)):
        src1 = varv.curr_ver(self.lopr.name)
        dst = varv.next_ver(dst)
        return [Ins(opc[self.op], [dst, src1, self.ropr.number])]
      else :
        src1 = varv.curr_ver(self.lopr.name)
        src2 = varv.curr_ver(self.ropr.name)
        dst = varv.next_ver(dst)
        return [Ins(opc[self.op], [dst, src1, src2])]


  def __str__(self):
    return "Expr({0},{1},{2})".format(self.lopr, self.op, self.ropr)
  def __init__(self, opr1, op, opr2, pos):
    self.lopr = opr1
    self.ropr = opr2
    if op != "+" and op != "-" and op != "*" and op != "/" and op != "%":
      raise Exception("Invalid operator {0} at {1}, {2}".
                      format(op, pos[0], pos[1]))
    if op != "/":
      self.op = op
    else :
      self.op = "//"
  @staticmethod
  def reduce(stack):
    if len(stack) == 1:
      if stack[0][0] == tokenize.NUMBER:
        return Num(stack[0][1])
      elif stack[0][0] == tokenize.NAME:
        return Var(stack[0][1])
      else :
        error(stack[0])
    elif len(stack) == 3:
      return Expr(Expr.reduce([stack[0]]),
                  stack[1][1],
                  Expr.reduce([stack[2]]), stack[1][2])
    else :
      raise Exception("Invalid expression at {0}, {1}".format(
        stack[0][2][0], stack[0][2][1]
      ))

class Var:
  name = ""
  def emit(self, varv, dst):
    src = varv.curr_ver(self.name)
    dst = varv.next_ver(dst)
    return [Ins(6, [dst, src])]
  def __init__(self, name):
    self.name = name
  def __str__(self):
    return "Var({0})".format(self.name)
  def __eq__(self, other):
    return self.name == other.name
  def __hash__(self):
    return self.name.__hash__()

class Num:
  number = 0
  def emit(self, varv, dst):
    dst = varv.next_ver(dst)
    return [Ins(6, [dst, self.number])]
  def __str__(self):
    return "Num({0})".format(self.number)
  def __init__(self, num):
    if isinstance(num, str):
      self.number = int(num)
    elif isinstance(num, int):
      self.number = num
    else :
      raise Exception("num is not a number???")

class Inpt:
  lhs = ""
  def __str__(self):
    return "Input({0})".format(self.lhs)
  def __init__(self, lhs):
    self.lhs = lhs
  def emit(self, varv):
    dst = varv.next_ver(self.lhs.name)
    return [Ins(0, [dst])]
  @staticmethod
  def reduce(stack):
    #Some checks
    if stack[1][1] != "(":
      error(stack[1])
    sl = len(stack)
    for n, v in enumerate(stack):
      if v[1] == ")" and n != sl-1:
        raise Exception("Garbage after ')' in a input statement, at {0}, {1}".
                        format(stack[n+1][2][0], stack[n+1][2][1]))
    if len(stack) != 3:
      raise Exception("Arguments passed to input statement, at {0}, {1}".
                      format(stack[2][2][0], stack[2][2][1]))
    return Inpt(Var(stack[0][1]))

class Prnt:
  expr = ""
  def __str__(self):
    return "Print({0})".format(self.expr)
  def __init__(self, expr):
    self.expr = expr
  def emit(self, varv):
    rst = []
    if isinstance(self.expr, Num):
      rst += [Ins(7, [self.expr.number])]
    else :
      rst += self.expr.emit(varv, "print")
      rst += [Ins(7, [varv.curr_ver("print")])]
    return rst

  @staticmethod
  def reduce(stack):
    #Some checks
    if stack[0][1] != "(":
      error(stack[0])
    sl = len(stack)
    for n, v in enumerate(stack):
      if v[1] == ")" and n != sl-1:
        raise Exception("Garbage after ')' in a print statement, at {0}, {1}".
                        format(stack[n+1][2][0], stack[n+1][2][1]))
    if sl != 3 and sl != 5:
      raise Exception("Argument passed to print is not a number, a variable or "
            "a valid expr, line {0}".format(stack[0][2][0]))
    return Prnt(Expr.reduce(stack[1:-1]))

class AST:
  def wellformed(self):
    defined = set([])
    for w, linenum in self.expr_list:
      chk = None
      if isinstance(w, Prnt):
        chk = w.expr
      elif isinstance(w, Asgn):
        defined |= {w.lhs}
        chk = w.rhs
      elif isinstance(w, Inpt):
        defined |= {w.lhs}
      if isinstance(chk, Expr):
        if (isinstance(chk.lopr, Var) and
            chk.lopr not in defined):
          print("{0} not defined before line {1}".format(
            chk.lopr, linenum
          ))
          return False
        if (isinstance(chk.ropr, Var) and
            chk.ropr not in defined):
          print("{0} not defined before line {1}".format(
            chk.ropr, linenum
          ))
          return False
      if isinstance(chk, Var):
        if chk not in defined:
          print("{0} not defined before line {1}".format(
            chk, linenum
          ))
          return False
    return True
  expr_list = []
  def __init__(self, elist):
    self.expr_list = elist
  def gencode(self):
    assert(self.wellformed())
    res = IR()
    varv = VarVer()
    for e, _ in self.expr_list:
      res += e.emit(varv)
    return res
  def __iadd__(self, obj):
    self.expr_list += [obj]
    return self
  def __str__(self):
    res = "["
    for w, _ in self.expr_list:
      res += str(w)
      res += ", "
    res += "]"
    return res


def parse(filename):
  f = open(filename, "rb")
  state = 0
  step = 0
  stack = []
  ast = AST([])
  for toknum, tokval, start, _, _ in tokenize.tokenize(f.readline):
    if toknum == tokenize.ENCODING:
      continue
    if toknum == tokenize.NEWLINE:
      continue
    if toknum == tokenize.ENDMARKER:
      if state != 0:
        raise Exception("Unexpected end of file")
    if tokval == ";" or toknum == tokenize.ENDMARKER:
      if state == 1:
        tmp = Prnt.reduce(stack)
      elif state == 3:
        tmp = Inpt.reduce(stack)
      elif state == 4:
        tmp = Asgn.reduce(stack)
      elif state != 0 :
        raise Exception("Unexpected ';' at line {0}".format(start[0]))
      if state != 0:
        ast += (tmp, start[0])
      state = 0
      stack = []
      continue
    if state == 0:
      #beginning of a line
      if tokval == "print":
        state = 1
      elif toknum == tokenize.NAME:
        state = 2
        step = 0
        stack = [(toknum, tokval, start)]
      else :
        error((toknum, tokval, start))
    elif state == 1:
      stack = stack + [(toknum, tokval, start)]
    elif state == 2:
      if step == 0:
        if tokval == "=":
          step = 1
        else :
          error((toknum, tokval, start))
      elif step == 1:
        if tokval == "input":
          state = 3
        else :
          state = 4
          stack += [(toknum, tokval, start)]
    else :
      stack += [(toknum, tokval, start)]
  return ast

for __i in range(0, 10):
  usable_reg += ["t{0}".format(__i)]

#for __i in range(0, 8):
#  usable_reg += ["s{0}".format(__i)]

nreg = len(usable_reg)
#nreg=6
print("Usable registers: {0}".format(usable_reg))

if __name__ == "__main__":
  try :
    __tmp = parse(sys.argv[1])
  except Exception as _e:
    print("Parse error: {0}".format(_e))
    sys.exit(1)
  outf = re.sub(r'\.[^.]*$', '.asm', sys.argv[1])
  print("AST:\n{0}".format(__tmp))
  wf = __tmp.wellformed()
  print("Is AST well formed?\n{0}".format(wf))
  if not wf :
    sys.exit(1)
  ir = __tmp.gencode()
  print("IR:\n{0}".format(ir))
  ir.gencode(outf)
