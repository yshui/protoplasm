from instruction import Ins
#this is the class for the intermediate code
class IR:
    ins = []
    used = {}
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
        #Calculate the liveness
        #start from the last instruction
        out = set()
        g = {}
        self.used = set()
        for i in reversed(self.ins):
            #add edges from used to out-def
            pairs = [(x, y) for x in i.iused for y in out-i.idef if x != y]
            #add edges from used to used
            pairs += [(x, y) for x in i.iused for y in i.iused if x < y]
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
            self.used |= i.iin
        return g
    def __spill(self, tgt, nreg):
        #spill a given variable to stack
        g1 = self.liveness()
        assert len(g1[tgt]) >= nreg and tgt not in self.tempv
        assert tgt not in self.spilt
        nins = []
        self.spilt |= {tgt}
        #create a new variable for each use of the given variable
        count = 0
        for i in self.ins:
            if tgt in i.iused:
                neww = "{0}.{1}".format(tgt, count)
                self.tempv[neww] = tgt
                count += 1
                vmap = {}
                vmap[tgt] = neww
                #Generate a extra LOAD instruction
                nins += [Ins(9, [neww, self.scnt]), i.transform(vmap)]
            else :
                nins += [i]
            if tgt in i.idef:
                #If the variable is defined in this instruction
                #then store it in to memory after this instruction
                nins += [Ins(8, [tgt, self.scnt])]
        self.ins = nins
        self.scnt += 1
    def __try_alloc_register(self, nreg):
        #Try to allocate register
        #When failed, return the variable with the most edges
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
                    #find a variable with less than nreg edges
                    flag = True
                    break
            if not flag:
                #can't find one, may be done or failure
                if len(visited) != len(g.keys()) :
                    #there are leftovers, we failed
                    maxd = 0
                    offending = None
                    for w in g:
                        #find the one with the maximum number of edges
                        if d[w] <= maxd or w in self.tempv:
                            continue
                        if w in self.spilt:
                            continue
                        maxd = d[w]
                        offending = w
                    return (False, offending)
                break
            #push on to stack
            visited |= {w}
            stack.append(w)
            for ww in g[w]:
                if ww not in visited:
                    d[ww] -= 1
        #assign the color in stack order
        color = {}
        while stack:
            w = stack.pop()
            available_color = set(range(0, nreg))
            for wn in g[w]:
                if wn in color:
                    available_color -= {color[wn]}
            color[w] = min(available_color)
        return (True, color)
    def alloc_register(self, nreg):
        global usable_reg
        if self._rassigned:
            return
        self._rassigned = True
        #Repeat: try allocate, if failed, spill
        while True:
            print("Trying register allocation with {0} registers...".format(nreg))
            ret, s = self.__try_alloc_register(nreg)
            print("Liveness information\nIR\t\t\tin")
            for i in self.ins:
                print("{0}\t\t\t{1}".format(i, i.iin))
            if ret:
                break
            print("Register allocation failed\nspilling {0}".format(s))
            self.__spill(s, nreg)
            print("IR after spilling {1}:\n{0}".format(self, s))
        print("Register assignment")
        #assign registers
        for w in s:
            s[w] = usable_reg[s[w]]
            print("\t{0} -> {1}".format(w, s[w]))
        for w in self.used:
            if w not in s:
                s[w] = usable_reg[0]
        #then assign the register
        for i in self.ins:
            i.assign(s, "0")
        #remove NOPs
        self.ins = [x for x in self.ins if x.useful]
        print("IR after register allocation:\n{0}".format(self))
    def alloc_memory(self):
        #allocate actual memory spaces
        #for variables spilled to memory
        if self._massigned:
            return
        assert self._rassigned
        self._massigned = True
        mloc = {} #a certain cell's location in memory
        reg = {} #keep track of what cell a reg hold
        mr = {} #keep track of which reg hold a cell
        nins = []
        mmax = 0
        def emit_store(src):
            nonlocal mmax
            mloc[reg[src]] = mmax
            mmax += 1
            i = Ins(8, [src, reg[src]], True)
            i.mem = mloc[reg[src]]
            return i
        #calculate memory cell liveness
        out = set()
        for i in reversed(self.ins):
            i.mliveness(out)
            out = i.mused
        for i in self.ins:
            if i.opcode == 9 : #LOAD
                dst = i.operands[0]
                src = i.operands[1]
                if dst in reg and reg[dst] == src:
                    continue
                if ((dst in reg) and (reg[dst] not in mloc) and
                     (reg[dst] in i.mused) and (len(mr[reg[dst]]) == 1)):
                    #this register: 1) hold something that is not in memory
                    #               2) and that thing will be needed later
                    #emit a store
                    nins += [emit_store(dst)]
                if dst in reg:
                    mr[reg[dst]] -= {dst}
                reg[dst] = src
                if mr[src]:
                    #held by a register, emit move instead
                    x = mr[src].pop()
                    assert dst != x
                    nins += [Ins(6, [dst, x], True)]
                    mr[src] |= {x}
                else :
                    assert src in mloc
                    i.mem = mloc[src]
                    nins += [i]
                mr[src] |= {dst}
            elif i.opcode == 8 : #STORE
                #STORE emitted during spilling is only a placehold
                #no STORE will be generated until necessary
                src = i.operands[0]
                assert src not in reg
                #a new store
                reg[src] = i.operands[1]
                mr[i.operands[1]] = {src}
                #do nothing, we only emit store when necessary
            elif i.opcode >= 0 and i.opcode <= 6 : #INPUT, +, -, *, /, %, MOVE
                #now reg is not holding anything
                dst = i.operands[0]
                if dst in reg:
                    if (reg[dst] not in mloc and reg[dst] in i.mused and
                            len(mr[reg[dst]]) == 1):
                        #Same as the LOAD case
                        nins += [emit_store(dst)]
                    mr[reg[dst]] -= {dst}
                    del reg[dst]
                nins += [i]
            else : #PRINT
                nins += [i]
        self.ins = [x for x in nins if x.useful]
        print("IR after stack memory allocation:\n{0}".format(self))
    def gencode(self, nreg, fname):
        #Generate machine code
        self.alloc_register(nreg)
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
        if mmax >= 0 :
            f.write("sub $sp, $sp, {0}\n".format(4*(mmax+1)))
        for i in self.ins:
            i.gencode(f)
        f.write("li $v0, 10\nsyscall\n")
        f.close()
        print("Done(written to {0})".format(fname))
    def __iadd__(self, ins):
        for i in ins:
            assert isinstance(i, Ins)
            assert i.idef & self.used == set()
            self.used |= i.idef
            self.ins += [i]
        return self
    def __str__(self):
        rst = "[\n"
        for i in self.ins:
            rst += "\t"+str(i)+"\n"
        rst += "]"
        return rst

usable_reg = []
for __i in range(0, 10):
    usable_reg += ["t{0}".format(__i)]
nreg = len(usable_reg)
