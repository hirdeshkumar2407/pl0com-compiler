#!/usr/bin/env python3

__doc__ = '''Control Flow Graph implementation
Includes cfg construction, loop detection (stub for unrolling), and liveness analysis.'''

from functools import reduce
import ir # Make sure ir is imported for type checks
from support import get_node_list # Assuming support.py provides get_node_list

# --- BasicBlock Class ---
class BasicBlock(object):
    def __init__(self, next_bb=None, instrs=None, labels=None):
        """Structure:
        Zero, one (next) or two (next, target_bb) successors
        Keeps information on labels (list of labels that refer to this BB)

        Args:
            next_bb: The next basic block in sequential execution (if any).
            instrs: A list of low-level IR instructions.
            labels: A list of label Symbols pointing to this block.
        """
        self.next = next_bb # Note: Renamed parameter for clarity
        self.instrs = instrs if instrs is not None else []
        self.labels = labels if labels is not None else []
        self.target = None      # Label Symbol this block branches to (if any)
        self.target_bb = None   # BasicBlock object this block branches to (if any)

        # Determine target label from last instruction if it's a non-call branch
        try:
            if self.instrs:
                last_instr = self.instrs[-1]
                if isinstance(last_instr, ir.BranchStat) and not last_instr.returns:
                    self.target = last_instr.target
        except Exception as e:
             # Should not happen with correct IR, but good to note
             print(f"Warning: Exception determining target for BB {id(self)}: {e}")

        # Liveness analysis sets (block level)
        self.live_in = set()
        self.live_out = set()

        # Gen/Kill sets for liveness analysis (calculated once)
        self.kill = set()  # Variables defined/assigned in this block
        self.gen = set()   # Variables used before being defined in this block
        self._compute_gen_kill() # Call helper to calculate

        # Attributes for graph traversal algorithms (like DFS for loop finding)
        self.visited = False
        self.recursion_stack = False

    def _compute_gen_kill(self):
        """Helper to calculate GEN and KILL sets for this block."""
        # Ensure instrs is a list
        if not isinstance(self.instrs, list):
             print(f"Warning: BB {id(self)} instructions is not a list: {type(self.instrs)}")
             return

        temp_kill = set() # Track kills within the block calculation
        for i in self.instrs:
            # Ensure instructions have expected methods or handle gracefully
            current_uses = set()
            try:
                current_uses = set(i.collect_uses())
            except AttributeError:
                print(f"Warning: Instruction {type(i)} lacks collect_uses")
                pass

            current_kills = set()
            try:
                current_kills = set(i.collect_kills())
            except AttributeError:
                print(f"Warning: Instruction {type(i)} lacks collect_kills")
                pass

            # GEN: Uses not killed previously *within this block*
            self.gen.update(current_uses - temp_kill)
            # Update overall KILL set and temporary kill set for block calculation
            self.kill.update(current_kills)
            temp_kill.update(current_kills)

    def __repr__(self):
        """Print in graphviz dot format (improved safety)."""
        # Represent labels safely
        label_reprs = []
        for lbl in self.labels:
            try:
                 label_reprs.append(f"{lbl.name}:")
            except AttributeError:
                 label_reprs.append("[Invalid Label Object]")
        label_str = '\\n'.join(label_reprs) + ('\\n' if label_reprs else '')

        # Represent instructions safely
        instr_reprs = []
        for i in self.instrs:
            try:
                # Use human_repr if available, otherwise default repr
                # Escape quotes and special chars for dot
                if hasattr(i, 'human_repr'):
                     rep = i.human_repr().replace('\\','\\\\').replace('"', '\\"').replace('\n','\\n')
                else:
                     rep = repr(i).replace('\\','\\\\').replace('"', '\\"').replace('\n','\\n')
                instr_reprs.append(rep)
            except Exception as e:
                 instr_reprs.append(f"[Error repr instr: {e}]")
        instr_str = '\\n'.join(instr_reprs)

        # Assemble label content
        # Using an ID-based label for the node name to avoid issues with complex content
        node_name = f"BB_{id(self)}"
        dot_label = f"{label_str}{instr_str}"
        # Limit label length for very large blocks if needed? Dot might handle it.

        res = f'{node_name} [label="{dot_label}"];\n'

        # Successor edges
        node_id_str = node_name # Use the safe node name for edges too

        if self.next:
            next_node_name = f"BB_{id(self.next)}"
            live_in_repr = repr(self.next.live_in).replace('"', '\\"') # Escape for label
            res += f'{node_id_str} -> {next_node_name} [label="{live_in_repr}"];\n'

        if self.target_bb:
            target_node_name = f"BB_{id(self.target_bb)}"
            live_in_repr = repr(self.target_bb.live_in).replace('"', '\\"') # Escape for label
            res += f'{node_id_str} -> {target_node_name} [style=dashed, label="{live_in_repr}"];\n'

        # Edge to exit node if no successors
        if not self.next and not self.target_bb:
            try:
                func = self.get_function()
                # Handle different return types of get_function
                if isinstance(func, ir.FunctionDef):
                    func_id_str = f"Func_{func.symbol.name}" # Use name if available
                elif isinstance(func, str): # Like 'global' or error strings
                    func_id_str = func.replace(" ", "_") # Sanitize
                else:
                    func_id_str = f"Func_{id(func)}" # Fallback to ID
            except Exception:
                func_id_str = "unknown_func"

            exit_node_name = f"exit_{func_id_str}"
            live_out_repr = repr(self.live_out).replace('"', '\\"') # Escape for label
            res += f'{node_id_str} -> {exit_node_name} [label="{live_out_repr}"];\n'

        return res

    def succ(self):
        """Return list of successor BasicBlock objects."""
        return [s for s in [self.target_bb, self.next] if s is not None]

    def liveness_iteration(self):
        """Compute live_in and live_out approximation for one iteration.
        Returns: True if liveness sets changed, False otherwise."""
        old_live_in = self.live_in.copy()  # Keep copy for comparison
        old_live_out = self.live_out.copy()

        # Calculate new live_out by unioning live_in of successors
        new_live_out = set()
        successors = self.succ()
        if successors:
             for s in successors:
                  new_live_out.update(s.live_in)
        else:
            # Handle block with no successors (exit block of a function/program)
            func = self.get_function()
            if isinstance(func, ir.FunctionDef):
                 try:
                      # Globals might be live out if they were modified and could be read later
                      # Or if function has return value used elsewhere (not modeled here)
                      new_live_out = set(func.get_global_symbols()) # Assumption: globals are live out
                 except AttributeError:
                      new_live_out = set() # Fallback
            # For global scope exit, live_out is typically empty
            # unless specific OS interaction is modeled.

        self.live_out = new_live_out

        # Calculate new live_in using the standard dataflow equation
        self.live_in = self.gen.union(self.live_out - self.kill)

        # Check if fixed point reached for this block
        return not (self.live_in == old_live_in and self.live_out == old_live_out)

    def compute_instr_level_liveness(self):
        """Compute live_in and live_out for each instruction within the block."""
        currently_alive = self.live_out.copy() # Start with live out of block

        for instr in reversed(self.instrs):
            # Ensure instructions have live_in/live_out attributes initialized
            if not hasattr(instr, 'live_out'): instr.live_out = set()
            if not hasattr(instr, 'live_in'): instr.live_in = set()

            instr.live_out = currently_alive.copy() # Liveness *after* this instruction

            # Variables killed by this instruction
            current_kills = set()
            try:
                current_kills = set(instr.collect_kills())
            except AttributeError: pass

            # Variables used by this instruction
            current_uses = set()
            try:
                 current_uses = set(instr.collect_uses())
            except AttributeError: pass

            # Update currently_alive *before* this instruction
            # live_in(instr) = use(instr) U (live_out(instr) - kill(instr))
            currently_alive = current_uses.union(currently_alive - current_kills)
            instr.live_in = currently_alive.copy()

        # Sanity check: Liveness at the start of the first instruction should match block's live_in
        if self.instrs and not (self.instrs[0].live_in == self.live_in):
             print(f"Warning: Liveness mismatch in BB {id(self)}:")
             print(f"  First instruction live_in = {self.instrs[0].live_in}")
             print(f"  Block live_in             = {self.live_in}")
             # Consider raising an exception if this indicates a major flaw

    def remove_useless_next(self):
        """If block ends in unconditional branch, remove sequential successor."""
        try:
            if self.instrs:
                last_instr = self.instrs[-1]
                # Check if it's a BranchStat and has the is_unconditional method
                if isinstance(last_instr, ir.BranchStat) and \
                   hasattr(last_instr, 'is_unconditional') and \
                   last_instr.is_unconditional():
                    self.next = None
        except Exception as e:
            print(f"Warning: Error in remove_useless_next for BB {id(self)}: {e}")


    def get_function(self):
        """Find the FunctionDef node containing this block, or 'global'."""
        if not self.instrs:
            # Need context to determine function for empty block
            # This could be improved by passing func context during CFG build
            return 'unknown_empty_block'
        try:
            # Assuming instructions store reference to their function or can find it
            return self.instrs[0].get_function() # Delegate to instruction
        except (AttributeError, IndexError, Exception) as e:
             print(f"Warning: Cannot get function from first instruction of BB {id(self)}: {e}")
             return 'unknown_func_context'

# --- Helper Functions ---

def stat_list_to_bb(sl):
    """Support function for converting a flattened StatList to BasicBlocks."""
    bbs = []
    current_instrs = []
    current_labels = []

    if not sl or not sl.children:
         return [] # Handle empty StatList

    for instr in sl.children:
        if not isinstance(instr, ir.Stat): # Basic check
            print(f"Warning: Non-Stat node {type(instr)} in StatList during BB creation.")
            continue

        is_new_block_start = False
        instr_label = None
        try:
            instr_label = instr.get_label()
            if instr_label:
                is_new_block_start = True
        except (AttributeError, NotImplementedError):
            pass # No label or abstract method

        # If this instruction has a label, it starts a new block.
        # Finish the previous block first.
        if is_new_block_start:
            if current_instrs: # If the previous block had instructions
                bb = BasicBlock(None, current_instrs, current_labels)
                if bbs: bbs[-1].next = bb # Link previous block
                bbs.append(bb)
            elif current_labels:
                 # Block with only labels? Might indicate empty block needed
                 print(f"Warning: Creating block for labels only: {current_labels}")
                 bb = BasicBlock(None, [], current_labels)
                 if bbs: bbs[-1].next = bb
                 bbs.append(bb)

            current_instrs = [] # Reset for the new block
            current_labels = [instr_label] # Start labels for the new block
        else:
            # If no label, add to any existing labels for the current block start
             pass # Labels are handled when a labeled instruction is found

        # Add the instruction to the block being built
        current_instrs.append(instr)

        # Check if this instruction ends the current basic block
        is_block_end = False
        if isinstance(instr, ir.BranchStat) and not instr.returns:
            is_block_end = True
        # Potentially add checks for other terminators like explicit returns

        if is_block_end:
            if current_instrs: # Create the block ending with this instruction
                bb = BasicBlock(None, current_instrs, current_labels)
                if bbs: bbs[-1].next = bb # Link previous (if any)
                bbs.append(bb)
                current_instrs = [] # Reset for next block
                current_labels = [] # Reset labels

    # Handle any remaining instructions after the loop
    if current_instrs:
        bb = BasicBlock(None, current_instrs, current_labels)
        if bbs: bbs[-1].next = bb
        bbs.append(bb)
    elif current_labels:
         # Dangling labels at the very end - often points to an empty exit block
         print(f"Info: Creating final empty block for dangling labels: {current_labels}")
         bb = BasicBlock(None, [], current_labels)
         if bbs: bbs[-1].next = bb
         bbs.append(bb)

    return bbs

def remove_non_regs(var_set):
    """Filters a set of symbols, keeping only those allocated to registers."""
    if not isinstance(var_set, set): return set()
    # Ensure elements are Symbols with 'alloct' attribute
    return {var for var in var_set if isinstance(var, ir.Symbol) and hasattr(var, 'alloct') and var.alloct == 'reg'}


# --- CFG Class ---
class CFG(list):
    """Control Flow Graph representation (as a list of BasicBlocks)."""

    def __init__(self, root_ir_node):
        """
        Constructs the CFG from a lowered, flattened IR tree.
        Args:
            root_ir_node: The root node (usually an ir.Block) of the IR tree.
        """
        super().__init__()
        if not isinstance(root_ir_node, ir.Block):
             print("Warning: CFG Initialized with non-Block root node.")
             # Decide how to handle this - maybe try finding StatLists anyway?
             # For now, proceed assuming structure might allow finding lists.

        # Find all relevant StatLists (typically bodies of functions/global scope)
        # This might need refinement based on exact IR structure after lowering
        stat_lists = [node for node in get_node_list(root_ir_node) if isinstance(node, ir.StatList)]
        # Filter out potentially empty lists inside lowered expressions if they exist?
        # stat_lists = [sl for sl in stat_lists if sl.parent is not None and not isinstance(sl.parent, ir.Expr)]


        if not stat_lists:
             print("Warning: No StatList nodes found to build CFG.")
             return

        # Convert each StatList into a sequence of BasicBlocks
        all_bbs = []
        for sl in stat_lists:
             # Need to handle nested functions - ideally process one func at a time
             # This simple concatenation assumes a single flat list post-lowering
             all_bbs.extend(stat_list_to_bb(sl))

        # Add all generated basic blocks to this CFG (which is a list)
        self.extend(all_bbs)

        # --- Second Pass: Resolve branch targets and links ---
        if not self: return # Nothing to link if no blocks were created

        # Create a map from label Symbol object to the BasicBlock it points to
        label_to_block_map = {}
        for i, bb in enumerate(self):
            if not isinstance(bb, BasicBlock): # Sanity check
                print(f"Warning: Non-BasicBlock element found in CFG at index {i}")
                continue
            for label in bb.labels:
                if not isinstance(label, ir.Symbol): # Sanity check
                     print(f"Warning: Non-Symbol label found in BB {id(bb)}")
                     continue
                if label in label_to_block_map:
                    print(f"Error: Duplicate label '{label.name}' detected. Points to BB {id(label_to_block_map[label])} and BB {id(bb)}. CFG may be incorrect.")
                    # Decide how to handle - overwrite? raise error?
                label_to_block_map[label] = bb

        # Set target_bb pointers for branches and remove redundant 'next' links
        for bb in self:
            if bb.target: # If the block ends in a branch (target label Symbol exists)
                target_label_symbol = bb.target
                if target_label_symbol in label_to_block_map:
                    bb.target_bb = label_to_block_map[target_label_symbol]
                else:
                    # This indicates an issue - branch target label doesn't exist
                    print(f"Error: Branch target label '{target_label_symbol.name}' not found for BB {id(bb)}")
                    # Consider raising an exception
            bb.remove_useless_next() # Clean up sequential link if jump is unconditional


    def heads(self):
        """Get entry BasicBlocks for each function and the global scope."""
        # Find all blocks that are successors of *any* other block
        all_successors = set()
        for bb in self:
            all_successors.update(s for s in bb.succ() if s)

        # Potential heads are blocks *not* in the successor set
        potential_heads = [bb for bb in self if bb not in all_successors]

        # Map these potential heads to their containing function/global scope
        entry_map = {} # Use FunctionDef object or 'global' string as key
        processed_funcs = set()

        for bb in potential_heads:
            func_context = bb.get_function() # Returns FunctionDef, 'global', or error string

            # Skip if context is unknown or already processed
            if not isinstance(func_context, (ir.FunctionDef, str)):
                 print(f"Warning: Skipping potential head BB {id(bb)} with unknown function context {func_context}")
                 continue
            if func_context in processed_funcs:
                 continue

            # Store the first potential head found for each context
            entry_map[func_context] = bb
            processed_funcs.add(func_context)

        return entry_map

    def print_cfg_to_dot(self, filename):
        """Print the CFG in graphviz dot format to file."""
        try:
            with open(filename, "w") as f:
                f.write("digraph G {\n")
                f.write('  rankdir=TB;\n') # Top-to-bottom layout
                f.write('  node [shape=box, fontname="Courier New", fontsize=10];\n')
                f.write('  edge [fontname="Courier New", fontsize=9];\n\n')

                # Define unique exit nodes for each function context found
                exit_nodes_defined = set()
                all_funcs = set(bb.get_function() for bb in self if bb.instrs) # Get unique function contexts

                # Print basic blocks themselves
                for bb in self:
                    f.write(f"  // BasicBlock ID: {id(bb)}\n")
                    f.write(f"  {bb!r}") # Use the updated BasicBlock.__repr__

                    # Define exit node if this block flows to one
                    if not bb.succ():
                        func = bb.get_function()
                        if isinstance(func, ir.FunctionDef): func_id_str = f"Func_{func.symbol.name}"
                        elif isinstance(func, str): func_id_str = func.replace(" ","_")
                        else: func_id_str = f"Func_{id(func)}"
                        exit_node_name = f"exit_{func_id_str}"
                        if exit_node_name not in exit_nodes_defined:
                             f.write(f'  {exit_node_name} [shape=ellipse, label="Return/Exit"];\n')
                             exit_nodes_defined.add(exit_node_name)

                f.write("\n  // Entry Points\n")
                heads_map = self.heads()
                for func_node, entry_bb in heads_map.items():
                     entry_bb_node_name = f"BB_{id(entry_bb)}"
                     if isinstance(func_node, ir.FunctionDef):
                          func_name = func_node.symbol.name
                          entry_node_name = f"Entry_{func_name}"
                          f.write(f'  {entry_node_name} [shape=ellipse, label="{func_name}()"];\n')
                     elif func_node == 'global':
                          entry_node_name = "main"
                          f.write(f'  {entry_node_name} [shape=diamond, label="main (global scope)"];\n')
                     else: # Handle unknown context from get_function
                           entry_node_name = f"Entry_{func_node}"
                           f.write(f'  {entry_node_name} [shape=octagon, label="Unknown Entry: {func_node}"];\n')

                     # Draw edge from entry shape to first basic block
                     entry_label = repr(entry_bb.live_in).replace('"', '\\"')
                     f.write(f'  {entry_node_name} -> {entry_bb_node_name} [label="{entry_label}", weight=10];\n')


                f.write("}\n")
            print(f"CFG graph saved to {filename}")
        except IOError as e:
             print(f"Error writing CFG to {filename}: {e}")
        except Exception as e:
             print(f"Unexpected error generating CFG dot file: {type(e).__name__} - {e}")
             import traceback
             traceback.print_exc() # Print detailed traceback for debugging


    def print_liveness(self):
        """Prints calculated liveness sets for debugging."""
        print('\n--- Liveness Analysis Results ---')
        if not self:
             print("CFG is empty.")
             return

        print('\nBlock Level Liveness:')
        for bb in self:
            print(f"\nBB {id(bb)}:")
            # Format sets for slightly cleaner printing
            gen_str = ', '.join(sorted(repr(s) for s in bb.gen))
            kill_str = ', '.join(sorted(repr(s) for s in bb.kill))
            live_in_str = ', '.join(sorted(repr(s) for s in bb.live_in))
            live_out_str = ', '.join(sorted(repr(s) for s in bb.live_out))
            print(f"  GEN : {{{gen_str}}}")
            print(f"  KILL: {{{kill_str}}}")
            print(f"  IN  : {{{live_in_str}}}")
            print(f"  OUT : {{{live_out_str}}}")

        print('\nInstruction Level Liveness:')
        for bb in self:
            print(f"\n--- BB {id(bb)} Instructions ---")
            for instr in bb.instrs:
                 instr_repr = "[No Repr]"
                 try:
                     instr_repr = instr.human_repr() if hasattr(instr, 'human_repr') else repr(instr)
                 except Exception: pass
                 live_in_str = ', '.join(sorted(repr(s) for s in getattr(instr, 'live_in', set())))
                 live_out_str = ', '.join(sorted(repr(s) for s in getattr(instr, 'live_out', set())))
                 print(f"  INST: {instr_repr}")
                 print(f"    IN : {{{live_in_str}}}")
                 print(f"    OUT: {{{live_out_str}}}")
        print('--- End Liveness ---')

    def find_target_bb(self, label):
        """Find the BasicBlock pointed to by a given label Symbol."""
        for bb in self:
            if label in bb.labels:
                return bb
        # It's generally an error if a branch target doesn't exist
        raise ValueError(f"Target label '{label.name}' not found in any BasicBlock!")

    def liveness(self):
        """Performs iterative live variable analysis until a fixed point."""
        print("--- Starting Liveness Analysis ---")
        if not self:
             print("CFG is empty. Skipping Liveness.")
             return

        changed = True
        iteration = 0
        max_iterations = len(self) * 2 # Heuristic limit based on number of nodes
        while changed:
            changed = False
            iteration += 1
            if iteration > max_iterations:
                 print(f"Warning: Liveness analysis did not converge after {max_iterations} iterations!")
                 # Optionally, you could dump state here for debugging
                 break

            # Iterate backward through blocks for standard liveness dataflow
            for bb in reversed(self):
                if bb.liveness_iteration(): # liveness_iteration returns True if sets changed
                    changed = True

        print(f"Liveness analysis converged after {iteration} iterations.")

        # After convergence, compute instruction-level liveness for all blocks
        for bb in self:
            bb.compute_instr_level_liveness()
        print("--- Liveness Analysis Complete ---")


    # --- Loop Unrolling Section ---

    def _find_loops_dfs(self, node, visited, recursion_stack, parent_map, back_edges, header_map):
        """ DFS helper for loop detection. """
        if node is None or not isinstance(node, BasicBlock): # Basic checks
            return

        node_id = id(node)
        visited.add(node_id)
        recursion_stack.add(node_id)

        for successor in node.succ(): # Iterate through valid successors
            if successor: # Check successor exists
                succ_id = id(successor)
                if succ_id not in visited:
                    parent_map[succ_id] = node_id # Record parent for path (optional)
                    self._find_loops_dfs(successor, visited, recursion_stack, parent_map, back_edges, header_map)
                elif succ_id in recursion_stack:
                    # Cycle detected -> Back Edge
                    header_bb = successor
                    source_bb = node
                    back_edge = (source_bb, header_bb)
                    # Avoid adding duplicate edges if multiple paths exist
                    if back_edge not in {(s,h) for s,h in back_edges}: # More efficient check?
                        print(f"      Found back edge: BB {id(source_bb)} -> BB {id(header_bb)} (Header)")
                        back_edges.append(back_edge)
                        # Map header ID to set of source BB IDs
                        header_id = id(header_bb)
                        if header_id not in header_map:
                             header_map[header_id] = set()
                        header_map[header_id].add(id(source_bb))

        recursion_stack.remove(node_id) # Backtrack

    def _get_loop_body(self, header, back_edge_sources):
        """ Finds nodes in the natural loop body using reverse graph traversal. """
        if not header or not back_edge_sources: return []

        body_nodes = {header} # Header is always part of the loop
        worklist = list(back_edge_sources) # Start from nodes directly pointing back to header
        visited_reverse = {id(header)} # Don't re-enter header from predecessors initially

        # Pre-calculate predecessors for efficient reverse traversal
        predecessors = {id(bb): [] for bb in self}
        for bb in self:
            for succ in bb.succ():
                if succ: predecessors[id(succ)].append(bb)

        processed_in_pass = set() # Track nodes added to body in this call

        queue = list(worklist) # Use a queue for BFS-like reverse exploration
        visited_reverse.update(id(n) for n in worklist) # Mark initial sources as visited

        while queue:
            current_bb = queue.pop(0)
            if current_bb != header: # Add node to body (if not header)
                 if current_bb not in body_nodes:
                      body_nodes.add(current_bb)
                      processed_in_pass.add(current_bb)


            # Explore predecessors of the current node
            current_id = id(current_bb)
            if current_id in predecessors:
                 for pred_bb in predecessors[current_id]:
                      pred_id = id(pred_bb)
                      # If predecessor not visited in reverse AND is not the header (avoid re-adding header path start)
                      if pred_id not in visited_reverse:
                           visited_reverse.add(pred_id)
                           queue.append(pred_bb) # Add predecessor to queue for exploration

        print(f"      Loop body nodes for header {id(header)}: {[id(bb) for bb in body_nodes]}")
        return list(body_nodes)


    def _find_loops(self):
        """ Detects loops using DFS and identifies natural loop bodies. """
        print("   Attempting loop detection using DFS...")
        if not self:
             print("   CFG is empty, no loops to find.")
             return []

        entry_points = self.heads()
        if not entry_points:
             print("   Warning: Could not determine CFG entry points. Using first block as fallback.")
             entry_points = {'fallback_entry': self[0]} if self else {}
             if not entry_points: return []

        visited = set()
        all_back_edges = []
        header_to_sources_map = {} # header_id -> set(source_ids)

        for entry_node in entry_points.values():
            if id(entry_node) not in visited:
                print(f"   Starting DFS from entry point BB {id(entry_node)}")
                recursion_stack = set()
                self._find_loops_dfs(entry_node, visited, recursion_stack, {}, all_back_edges, header_to_sources_map)

        # Group back edges by header and determine loop body
        loops_found = []
        processed_headers = set() # Track headers whose loops we've defined

        for source_bb, header_bb in all_back_edges:
            header_id = id(header_bb)
            if header_id in processed_headers:
                continue # Avoid processing the same loop multiple times

            # Get all source BBs that have a back edge to this header
            if header_id not in header_to_sources_map:
                 print(f"Warning: Header {header_id} found via back edge but not in header_map.")
                 continue
            source_ids = header_to_sources_map[header_id]
            current_loop_sources = [bb for bb in self if id(bb) in source_ids]
            current_loop_back_edges = [(src, header_bb) for src in current_loop_sources]

            # Find the natural loop body associated with this header
            body_blocks = self._get_loop_body(header_bb, current_loop_sources)

            loops_found.append({
                'header': header_bb,       # The header BasicBlock
                'body_blocks': body_blocks, # List of BasicBlocks in the loop
                'back_edges': current_loop_back_edges # List of (source_bb, header_bb) tuples
            })
            processed_headers.add(header_id)

        print(f"   Loop detection complete. Found {len(loops_found)} unique loop header(s).")
        return loops_found

    def _is_loop_suitable_for_unrolling(self, loop_info):
        """ Placeholder for checking if a loop should be unrolled. """
        print(f"      Checking suitability for loop with header {id(loop_info['header'])} (placeholder)...")
        # TODO: Implement actual checks (e.g., loop size, calls, complexity)
        return False # Default to false for now

    def unroll_loops(self, factor=2):
        """ Analyzes CFG, finds loops, and applies unrolling transformation. """
        print(f"\n--- Starting Loop Unrolling Pass (Factor: {factor}) ---")
        if factor < 2:
             print("   Unrolling factor must be >= 2. Skipping.")
             print("--- Loop Unrolling Pass Complete (No changes) ---")
             return

        # 1. Detect Loops
        print("   Step 1: Detecting loops...")
        loops = self._find_loops()

        if not loops:
            print("   No loops detected.")
            print("--- Loop Unrolling Pass Complete (No changes) ---")
            return

        print(f"   Detected {len(loops)} loop(s). Analyzing for unrolling...")
        changes_made = False

        # 2. Analyze and Transform suitable loops
        for loop in loops:
            header = loop['header']
            print(f"   Analyzing loop with header BB {id(header)}...")

            if not self._is_loop_suitable_for_unrolling(loop):
                print(f"      Loop not suitable for unrolling (based on current criteria).")
                continue

            print(f"      Attempting to unroll loop at BB {id(header)}...")
            # --- Actual unrolling transformation implementation needed ---
            # - Requires deep copying/cloning BasicBlocks and instructions.
            # - Careful adjustment of loop counters/variables in cloned blocks.
            # - Rewiring CFG edges (next/target_bb) correctly.
            # - Handling trip count / cleanup loop generation.
            # - Updating the CFG list (self) with new/modified blocks.
            print(f"      ***** Loop Unrolling Transformation NOT IMPLEMENTED *****")
            # changes_made = True # Set to True if unrolling is actually performed

        if changes_made:
             print("   Loops unrolled. CFG structure modified.")
             # Important: After modifying CFG, analyses might need re-running if called after this pass
        else:
             print("   No suitable loops were unrolled.")

        print("--- Loop Unrolling Pass Complete ---")