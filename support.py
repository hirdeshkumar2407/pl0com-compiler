#!/usr/bin/env python3

"""Support functions for visiting the AST and the IR tree (which are
the same thing in this compiler).
These functions expose high level interfaces (passes) for actions that can be
applied to multiple IR nodes."""


def get_node_list(root):
    """Get a list of all nodes in the AST"""

    def register_nodes(l):
        def r(node):
            if node not in l:
                l.append(node)

        return r

    node_list = []
    root.navigate(register_nodes(node_list))
    return node_list


def get_symbol_tables(root):
    """Get a list of all symtabs in the AST"""

    def register_nodes(l):
        def r(node):
            try:
                if node.symtab not in l:
                    l.append(node.symtab)
            except Exception:
                pass
            try:
                if node.lc_sym not in l:
                    l.append(node.symtab)
            except Exception:
                pass

        return r

    node_list = []
    root.navigate(register_nodes(node_list))
    return node_list


def lowering(node):
    """Lowering action for a node
    (all high level nodes can be lowered to lower-level representation"""
    try:
        check = node.lower()
        print('Lowering', type(node), id(node))
        if not check:
            print('Failed!')
    except Exception as e:
        print('Cannot lower', id(node), type(node), e)
        pass  # lowering not yet implemented for this class


def flattening(node):
    """Flattening action for a node
    (only StatList nodes are actually flattened)"""
    try:
        check = node.flatten()
        print('Flattening', type(node), id(node))
        if not check:
            print('Failed!')
    except Exception as e:
        # print type(node), e
        pass  # this type of node cannot be flattened


def dotty_wrapper(fout):
    """Main function for graphviz dot output generation"""

    def dotty_function(irnode):
        from ir import Stat
        attrs = {'body', 'cond', 'thenpart', 'elsepart', 'call', 'step', 'expr', 'target', 'defs'} & set(
            dir(irnode))

        res = repr(id(irnode)) + ' ['
        if isinstance(irnode, Stat):
            res += 'shape=box,'
        res += 'label="' + repr(type(irnode)) + ' ' + repr(id(irnode))
        try:
            res += ': ' + irnode.value
        except Exception:
            pass
        try:
            res += ': ' + irnode.name
        except Exception:
            pass
        try:
            res += ': ' + getattr(irnode, 'symbol').name
        except Exception:
            pass
        res += '" ];\n'

        if 'children' in dir(irnode) and len(irnode.children):
            for node in irnode.children:
                res += repr(id(irnode)) + ' -> ' + repr(id(node)) + ' [pos=' + repr(
                    irnode.children.index(node)) + '];\n'
                if type(node) == str:
                    res += repr(id(node)) + ' [label=' + node + '];\n'
        for d in attrs:
            node = getattr(irnode, d)
            if d == 'target':
                res += repr(id(irnode)) + ' -> ' + repr(id(node.value)) + ' [label=' + node.name + '];\n'
            else:
                res += repr(id(irnode)) + ' -> ' + repr(id(node)) + ';\n'
        fout.write(res)
        return res

    return dotty_function


def print_dotty(root, filename):
    """Print a graphviz dot representation to file"""
    fout = open(filename, "w")
    fout.write("digraph G {\n")
    node_list = get_node_list(root)
    dotty = dotty_wrapper(fout)
    for n in node_list:
        dotty(n)
    fout.write("}\n")
