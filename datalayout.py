#!/usr/bin/env python3

"""Data layout computation pass. Each symbol whose location (alloct)
is not a register, is allocated in the local stack frame (LocalSymbol) or in
the data section of the executable (GlobalSymbol)."""


class SymbolLayout(object):
    def __init__(self, symname, bsize):
        self.symname = symname
        self.bsize = bsize


class LocalSymbolLayout(SymbolLayout):
    def __init__(self, symname, fpreloff, bsize):
        self.symname = symname
        self.fpreloff = fpreloff
        self.bsize = bsize

    def __repr__(self):
        return self.symname + ": fp + (" + repr(self.fpreloff) + ") [def byte " + \
               repr(self.bsize) + "]"


class GlobalSymbolLayout(SymbolLayout):
    def __init__(self, symname, bsize):
        self.symname = symname
        self.bsize = bsize

    def __repr__(self):
        return self.symname + ": def byte " + repr(self.bsize)


def perform_data_layout(root):
    perform_data_layout_of_program(root)
    for defin in root.defs.children:
        perform_data_layout_of_function(defin)


def perform_data_layout_of_function(funcroot):
    offs = 0  # prev fp
    prefix = "_l_" + funcroot.symbol.name + "_"
    for var in funcroot.body.symtab:
        if var.stype.size == 0:
            continue
        bsize = var.stype.size // 8
        offs -= bsize
        var.set_alloc_info(LocalSymbolLayout(prefix + var.name, offs, bsize))
    funcroot.body.stackroom = -offs


def perform_data_layout_of_program(root):
    prefix = "_g_"
    for var in root.symtab:
        if var.stype.size == 0:
            continue
        var.set_alloc_info(GlobalSymbolLayout(prefix + var.name, var.stype.size // 8))
