#!/usr/bin/env python3

"""Register allocation pass, using the linear-scan algorithm.
Assumes that all temporaries can be allocated to any register (because of this,
it does not work with non integer types)."""

from cfg import *

# the register of all spilled temporaries is set to SPILL_FLAG
SPILL_FLAG = 999


class RegisterAllocation(object):
    """Object that contains the information about where each temporary is
    allocated.

    Spill handling is done by reserving 2 machine registers to be filled
    as late as possible, and spilled again as soon as possible. This class is
    responsible for filling these registers."""

    def __init__(self, vartoreg, numspill, nregs):
        self.vartoreg = vartoreg
        self.numspill = numspill
        self.nregs = nregs
        self.vartospillframeoffset = dict()
        self.spillregi = 0
        self.spillframeoffseti = 0

    def update(self, otherra):
        self.vartoreg.update(otherra.vartoreg)
        self.numspill += otherra.numspill

    def spill_room(self):
        return self.numspill * 4

    def dematerialize_spilled_var_if_necessary(self, var):
        """Resets the register used for a spill variable when we know that instance
        of the variable is now dead."""
        if self.vartoreg[var] >= self.nregs - 2:
            self.vartoreg[var] = SPILL_FLAG

    def materialize_spilled_var_if_necessary(self, var):
        """Decide which of the spill-reserved registers to fill with a spilled
        variable. Also, decides to which stack location the variable is spilled
        to, the first time this method is called for that variable.

        Returns True iff the variable was spilled in the register
        allocation phase.

        The algorithm used to decide which register is filled is simple: the
        register chosen is the one that was not chosen the last time. It always
        works and it never needs any information about which registers are live
        at a given time."""

        if self.vartoreg[var] != SPILL_FLAG:
            # already allocated and filled! nothing to do
            if self.vartoreg[var] >= self.nregs - 2:
                return True
            return False

        # decide the register
        self.vartoreg[var] = self.spillregi + self.nregs - 2
        self.spillregi = (self.spillregi + 1) % 2

        # decide the location in the current frame
        if not (var in self.vartospillframeoffset):
            self.vartospillframeoffset[var] = self.spillframeoffseti
            self.spillframeoffseti += 4
        return True

    def __repr__(self):
        return 'vartoreg = ' + repr(self.vartoreg)


class LinearScanRegisterAllocator(object):
    """The register allocator. Produces RegisterAllocation objects from a control
    flow graph."""

    def __init__(self, cfg, nregs):
        self.cfg = cfg
        self.nregs = nregs

        # liveness of a variable on entry to each instruction
        # in order of start point
        self.varliveness = []  # {var=var, liveness=[indexes]}
        # list of all variables
        self.allvars = []
        self.vartoreg = {}

    def compute_liveness_intervals(self):
        """computes liveness intervals for the whole program. Note that the CFG
        is flattened: this is the reason why the linear scan register allocation
        algorithm does not handle liveness holes properly"""
        inst_index = 0
        min_gen = {}
        max_use = {}
        vars = set()

        for bb in self.cfg:
            for i in bb.instrs:
                try:
                    kill = list(i.collect_kills())
                except AttributeError:
                    kill = []
                use = list(i.collect_uses())

                kill = remove_non_regs(kill)
                use = remove_non_regs(use)

                for var in kill:
                    if not var in min_gen:
                        min_gen[var] = inst_index
                        max_use[var] = inst_index
                for var in use:
                    max_use[var] = inst_index

                vars |= kill | use

                inst_index += 1

        for v in vars:
            gen = min_gen[v]
            kill = max_use[v]
            self.varliveness.insert(0, {"var": v, "interv": range(gen, kill)})
        self.varliveness.sort(key=lambda x: x['interv'][0])
        self.allvars = list(vars)

    def __call__(self):
        """Linear-scan register allocation (a variant of the more general
                graph coloring algorithm known as "left-edge")"""

        self.compute_liveness_intervals()
        print('LIVENESS INTERVALS:')
        print(self.varliveness)

        live = []
        freeregs = set(range(0, self.nregs - 2))  # -2 for spill room
        numspill = 0

        for livei in self.varliveness:
            start = livei["interv"][0]

            # expire old intervals
            i = 0
            while i < len(live):
                notlivecandidate = live[i]
                if notlivecandidate["interv"][-1] < start:
                    live.pop(i)
                    freeregs.add(self.vartoreg[notlivecandidate["var"]])
                i += 1

            if len(freeregs) == 0:
                tospill = live[-1]
                # keep the longest interval
                if tospill["interv"][-1] > livei["interv"][-1]:
                    # we have to spill "tospill"
                    self.vartoreg[livei["var"]] = self.vartoreg[tospill["var"]]
                    self.vartoreg[tospill["var"]] = SPILL_FLAG
                    live.pop(-1)  # remove spill from active
                    live.append(livei)  # add i to active
                else:
                    self.vartoreg[livei["var"]] = SPILL_FLAG
                numspill += 1

            else:
                self.vartoreg[livei["var"]] = freeregs.pop()
                live.append(livei)

            # sort the active intervals by increasing end point
            live.sort(key=lambda li: li['interv'][-1])

        return RegisterAllocation(self.vartoreg, numspill, self.nregs)

