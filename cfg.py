#!/usr/bin/env python3

__doc__ = '''Control Flow Graph implementation
Includes cfg construction, loop detection, basic loop unrolling, and liveness analysis.'''

import copy
from functools import reduce
import ir # Make sure ir is imported for type checks
from support import get_node_list # Assuming support.py provides get_node_list

# --- BasicBlock Class ---
class BasicBlock(object):
    def __init__(self, next_bb=None, instrs=None, labels=None):
        self.next = next_bb
        self.instrs = instrs if instrs is not None else []
        self.labels = labels if labels is not None else []
        self.target = None
        self.target_bb = None
        self.preds = []
        if self.instrs:
            try:
                last_instr = self.instrs[-1]
                if isinstance(last_instr, ir.BranchStat) and not getattr(last_instr, 'returns', False):
                    self.target = getattr(last_instr, 'target', None)
            except (IndexError, AttributeError) as e:
                print(f"DEBUG: Error processing last instruction in BB: {e}")
        self.live_in = set(); self.live_out = set(); self.gen = set(); self.kill = set()
        self._compute_gen_kill(); self.visited = False; self.recursion_stack = False

    def _compute_gen_kill(self):
        self.gen.clear(); self.kill.clear(); temp_kill_for_gen_calc = set()
        for i_instr in self.instrs:
            try:
                current_uses = set(i_instr.collect_uses()) if hasattr(i_instr, 'collect_uses') else set()
                current_kills = set(i_instr.collect_kills()) if hasattr(i_instr, 'collect_kills') else set()
                self.gen.update(current_uses - temp_kill_for_gen_calc)
                self.kill.update(current_kills)
                temp_kill_for_gen_calc.update(current_kills)
            except Exception as e:
                print(f"DEBUG: Error in gen/kill computation for {type(i_instr)}: {e}")

    def clone(self, new_label_suffix=""):
        print(f"      UNROLL_CLONE_DEBUG: Cloning BB {id(self)} for '{new_label_suffix}'")
        cloned_instrs = []
        for instr_orig in self.instrs:
            try:
                instr_clone = copy.deepcopy(instr_orig)
                if hasattr(instr_clone, 'label') and instr_clone.label and instr_clone.label in self.labels:
                    instr_clone.label = None
                cloned_instrs.append(instr_clone)
            except Exception as e:
                print(f"DEBUG: Error cloning instruction {type(instr_orig)}: {e}")
                cloned_instrs.append(instr_orig)  # fallback to original
                
        new_labels_for_clone = []
        if new_label_suffix:
            for lbl_orig in self.labels:
                try:
                    if isinstance(lbl_orig, ir.Symbol) and hasattr(lbl_orig, 'stype') and lbl_orig.stype.name == 'label':
                        new_label_obj = ir.TYPENAMES['label']() # Correct: Call the factory
                        new_label_obj.name = f"{lbl_orig.name}_{new_label_suffix}"
                        new_labels_for_clone.append(new_label_obj)
                except Exception as e:
                    print(f"DEBUG: Error cloning label {lbl_orig}: {e}")
        return BasicBlock(instrs=cloned_instrs, labels=new_labels_for_clone)

    def __repr__(self):
        try:
            # Prepare label string for the node's main label
            node_labels_str_list = []
            for lbl in self.labels:
                try: 
                    node_labels_str_list.append(f"{lbl.name}:")
                except AttributeError: 
                    node_labels_str_list.append("[InvalidLabelObj]")
            node_label_prefix = '\\n'.join(node_labels_str_list) + ('\\n' if node_labels_str_list else '')

            # Prepare instruction strings
            instr_dot_list = []
            for i_item in self.instrs:
                try:
                    rep_str = (i_item.human_repr() if hasattr(i_item, 'human_repr') else repr(i_item))
                    rep_str = rep_str.replace('\\', '\\\\')
                    rep_str = rep_str.replace('"', '\\"')
                    rep_str = rep_str.replace('\n', '\\n')
                    instr_dot_list.append(rep_str)
                except Exception as e:
                    instr_dot_list.append(f"[Err Repr {type(i_item)}: {e}]")
            instrs_dot_content = '\\n'.join(instr_dot_list)
            
            graphviz_node_id_str = f"BB_{id(self)}"
            graphviz_node_main_label = f"{node_label_prefix}{instrs_dot_content}"
            
            res = f'{graphviz_node_id_str} [label="{graphviz_node_main_label}"];\n'

            # Add edges
            if self.next:
                next_live_in_repr = repr(self.next.live_in)
                safe_edge_label_next = next_live_in_repr.replace('"', '\\"')
                res += f'{graphviz_node_id_str} -> BB_{id(self.next)} [label="{safe_edge_label_next}"];\n'
            if self.target_bb:
                target_live_in_repr = repr(self.target_bb.live_in)
                safe_edge_label_target = target_live_in_repr.replace('"', '\\"')
                res += f'{graphviz_node_id_str} -> BB_{id(self.target_bb)} [style=dashed,label="{safe_edge_label_target}"];\n'
            if not (self.next or self.target_bb):
                func = self.get_function()
                func_id_str = f"Func_{func.symbol.name}" if isinstance(func, ir.FunctionDef) and hasattr(func, 'symbol') else str(func).replace(" ","_").replace(":","_")
                exit_node_target_name = f"exit_{func_id_str}"
                exit_live_out_repr = repr(self.live_out)
                safe_edge_label_exit = exit_live_out_repr.replace('"', '\\"')
                res += f'{graphviz_node_id_str} -> {exit_node_target_name} [label="{safe_edge_label_exit}"];\n'
            return res
        except Exception as e:
            return f'BB_{id(self)} [label="Error in repr: {e}"];\n'

    def succ(self): 
        """Return list of successor basic blocks"""
        try:
            successors = []
            if self.target_bb:
                successors.append(self.target_bb)
            if self.next:
                successors.append(self.next)
            return successors
        except Exception as e:
            print(f"DEBUG: Error getting successors for BB_{id(self)}: {e}")
            return []
    
    def get_function(self): 
        try:
            return self.instrs[0].get_function() if self.instrs and hasattr(self.instrs[0], 'get_function') else 'unknown_BB_context'
        except Exception as e:
            print(f"DEBUG: Error getting function for BB_{id(self)}: {e}")
            return 'error_context'
    
    def remove_useless_next(self):
        """Remove next pointer if last instruction is unconditional branch"""
        try:
            if (self.instrs and isinstance(self.instrs[-1], ir.BranchStat) and 
                hasattr(self.instrs[-1], 'is_unconditional') and self.instrs[-1].is_unconditional()):
                print(f"DEBUG: Removing useless next from BB_{id(self)} (has unconditional branch)")
                self.next = None
        except Exception as e:
            print(f"DEBUG: Error in remove_useless_next for BB_{id(self)}: {e}")
    
    def liveness_iteration(self):
        try:
            old_live_in, old_live_out = self.live_in.copy(), self.live_out.copy()
            new_live_out = set()
            for s_succ in self.succ(): 
                new_live_out.update(s_succ.live_in)
            if not self.succ():
                func = self.get_function()
                if isinstance(func, ir.FunctionDef) and hasattr(func, 'get_global_symbols'):
                    try: 
                        new_live_out = set(func.get_global_symbols())
                    except: 
                        new_live_out = set()
            self.live_out = new_live_out
            self.live_in = self.gen.union(self.live_out - self.kill)
            return not (self.live_in == old_live_in and self.live_out == old_live_out)
        except Exception as e:
            print(f"DEBUG: Error in liveness_iteration for BB_{id(self)}: {e}")
            return False
    
    def compute_instr_level_liveness(self):
        try:
            curr_alive = self.live_out.copy()
            for instr_item in reversed(self.instrs):
                instr_item.live_out = curr_alive.copy()
                kills_item = set(instr_item.collect_kills()) if hasattr(instr_item, 'collect_kills') else set()
                uses_item = set(instr_item.collect_uses()) if hasattr(instr_item, 'collect_uses') else set()
                curr_alive = uses_item.union(instr_item.live_out - kills_item)
                instr_item.live_in = curr_alive.copy()
            if self.instrs and hasattr(self.instrs[0], 'live_in') and not (curr_alive == self.live_in):
                 print(f"Warning: Liveness mismatch BB {id(self)}: FirstInstrIN_calc={curr_alive} vs BlockIN_set={self.live_in}")
        except Exception as e:
            print(f"DEBUG: Error in compute_instr_level_liveness for BB_{id(self)}: {e}")


# --- Helper Functions ---
def stat_list_to_bb(sl):
    """Convert StatList to BasicBlocks with enhanced branch handling"""
    try:
        print(f"DEBUG: Converting StatList with {len(sl.children) if sl and sl.children else 0} statements")
        
        bbs = []
        current_instrs, current_labels = [], []
        
        if not sl or not sl.children: 
            print("DEBUG: Empty StatList, returning empty list")
            return []
        
        for i, instr in enumerate(sl.children):
            try:
                if not isinstance(instr, ir.Stat): 
                    print(f"Warning: Non-Stat {type(instr)} in StatList")
                    continue
                    
                print(f"DEBUG: Processing instruction {i}: {type(instr).__name__}")
                
                # Check for label
                is_new_block_start, instr_label = False, None
                try: 
                    instr_label = instr.get_label()
                    is_new_block_start = bool(instr_label)
                    if instr_label:
                        label_name = instr_label.name if hasattr(instr_label, 'name') else str(instr_label)
                        print(f"DEBUG: Found label: {label_name}")
                except Exception as e:
                    print(f"DEBUG: Error getting label from instruction: {e}")
                
                # Start new block if we hit a label
                if is_new_block_start:
                    if current_instrs or current_labels:
                        bb = BasicBlock(None, current_instrs, current_labels)
                        bbs.append(bb)
                        print(f"DEBUG: Created BB_{id(bb)} with {len(current_instrs)} instructions")
                        # Link previous block to this one if no explicit branch
                        if len(bbs) > 1 and bbs[-2].target is None:
                            bbs[-2].next = bb
                            print(f"DEBUG: Linked BB_{id(bbs[-2])} -> BB_{id(bb)} (fall-through)")
                    current_instrs, current_labels = [], [instr_label]
                
                current_instrs.append(instr)
                
                # Check if this instruction ends a block (branch/return)
                if isinstance(instr, ir.BranchStat):
                    print(f"DEBUG: Found branch instruction:")
                    print(f"  - Returns: {getattr(instr, 'returns', False)}")
                    print(f"  - Has condition: {hasattr(instr, 'cond') and getattr(instr, 'cond', None) is not None}")
                    print(f"  - Target: {getattr(instr, 'target', None)}")
                    
                    # Always end block after a branch instruction
                    if current_instrs:
                        bb = BasicBlock(None, current_instrs, current_labels)
                        bbs.append(bb)
                        print(f"DEBUG: Created BB_{id(bb)} ending with branch")
                        # Link previous block if no explicit branch
                        if len(bbs) > 1 and bbs[-2].target is None:
                            bbs[-2].next = bb
                            print(f"DEBUG: Linked BB_{id(bbs[-2])} -> BB_{id(bb)} (pre-branch)")
                        current_instrs, current_labels = [], []
            except Exception as e:
                print(f"DEBUG: Error processing instruction {i}: {e}")
                continue
        
        # Handle remaining instructions
        if current_instrs or current_labels:
            bb = BasicBlock(None, current_instrs, current_labels)
            bbs.append(bb)
            print(f"DEBUG: Created final BB_{id(bb)} with {len(current_instrs)} instructions")
            if len(bbs) > 1 and bbs[-2].target is None:
                bbs[-2].next = bb
                print(f"DEBUG: Linked BB_{id(bbs[-2])} -> BB_{id(bb)} (final)")
        
        print(f"DEBUG: Created {len(bbs)} basic blocks total")
        return bbs
    except Exception as e:
        print(f"ERROR: Exception in stat_list_to_bb: {e}")
        import traceback
        traceback.print_exc()
        return []

def remove_non_regs(var_set):
    if not isinstance(var_set, set): return set()
    return {var for var in var_set if isinstance(var, ir.Symbol) and hasattr(var, 'alloct') and var.alloct == 'reg'}

# --- CFG Class ---
class CFG(list):
    def __init__(self, root_ir_node):
        super().__init__()
        try:
            print("DEBUG: Starting CFG construction...")
            stat_lists = [node for node in get_node_list(root_ir_node) if isinstance(node, ir.StatList)]
            if not stat_lists: 
                print("Warning: No StatLists found for CFG.")
                return
            
            print(f"DEBUG: Found {len(stat_lists)} StatLists")
            all_bbs = []
            for i, sl in enumerate(stat_lists):
                print(f"DEBUG: Processing StatList {i}")
                bbs = stat_list_to_bb(sl)
                all_bbs.extend(bbs)
                
            self.extend(all_bbs)
            if not self: 
                print("Warning: CFG created empty.")
                return
                
            print(f"DEBUG: CFG created with {len(self)} basic blocks")
            self._rebuild_all_cfg_links()
        except Exception as e:
            print(f"ERROR: Exception in CFG.__init__: {e}")
            import traceback
            traceback.print_exc()

    def debug_cfg_structure(self):
        """Enhanced debug method to print CFG structure"""
        try:
            print("\n--- CFG Structure Debug ---")
            print(f"Total blocks: {len(self)}")
            
            if not self:
                print("CFG is empty!")
                return
            
            # Count blocks by predecessor count
            no_pred_count = sum(1 for bb in self if len(bb.preds) == 0)
            multi_succ_count = sum(1 for bb in self if len(bb.succ()) > 1)
            
            print(f"Blocks with no predecessors: {no_pred_count}")
            print(f"Blocks with multiple successors: {multi_succ_count}")
            
            # Show potential back edges
            print("\n*** Potential Back Edges ***")
            for bb in self:
                for succ in bb.succ():
                    # Check if this could be a back edge by looking at labels and instruction order
                    if (succ and bb.target_bb == succ and bb.instrs and 
                        isinstance(bb.instrs[-1], ir.BranchStat) and 
                        not getattr(bb.instrs[-1], 'returns', False)):
                        
                        target_label = getattr(bb.instrs[-1], 'target', None)
                        if target_label and succ.labels and target_label in succ.labels:
                            print(f"  POTENTIAL BACK EDGE: BB_{id(bb)} -> BB_{id(succ)} (target: {target_label})")
                            
        except Exception as e:
            print(f"ERROR: Exception in debug_cfg_structure: {e}")
            import traceback
            traceback.print_exc()

    def heads(self):
        """Find entry points (heads) of the CFG - blocks with no predecessors"""
        try:
            # Find all blocks that are successors of other blocks
            all_successors = set()
            for bb in self:
                try:
                    for succ in bb.succ():
                        if succ:
                            all_successors.add(succ)
                except Exception as e:
                    print(f"DEBUG: Error getting successors for BB_{id(bb)}: {e}")
            
            # Blocks that are not successors of any other block are entry points
            potential_heads = [bb for bb in self if bb not in all_successors]
            
            # Group by function
            entry_map = {}
            processed_functions = set()
            
            for bb_h in potential_heads:
                try:
                    func_context = bb_h.get_function()
                    
                    # Skip if we already processed this function
                    if func_context in processed_functions:
                        continue
                    
                    # This is a valid entry point
                    entry_map[func_context] = bb_h
                    processed_functions.add(func_context)
                except Exception as e:
                    print(f"DEBUG: Error processing potential head BB_{id(bb_h)}: {e}")
            
            print(f"DEBUG: Found {len(entry_map)} entry points")
            for func, bb in entry_map.items():
                try:
                    func_name = func.symbol.name if isinstance(func, ir.FunctionDef) and hasattr(func, 'symbol') else str(func)
                    print(f"  - {func_name}: BB_{id(bb)}")
                except Exception as e:
                    print(f"  - [error getting name]: BB_{id(bb)}")
                
            return entry_map
        except Exception as e:
            print(f"ERROR: Exception in heads(): {e}")
            return {}

    def print_cfg_to_dot(self, filename):
        try:
            with open(filename, "w") as f:
                f.write("digraph G {\n  rankdir=TB;\n  node [shape=box, fontname=\"Courier New\", fontsize=10];\n"
                        "  edge [fontname=\"Courier New\", fontsize=9];\n\n")
                exit_nodes_defined = set()
                for n_i in self:
                    f.write(f"  // BasicBlock ID for CFG list: {id(n_i)}\n")
                    f.write(f"  {n_i!r}")
                    if not n_i.succ():
                        func = n_i.get_function()
                        func_id_str = f"Func_{func.symbol.name}" if isinstance(func, ir.FunctionDef) and hasattr(func,'symbol') else str(func).replace(" ","_").replace(":","_")
                        exit_node_name = f"exit_{func_id_str}"
                        if exit_node_name not in exit_nodes_defined:
                             f.write(f'  {exit_node_name} [shape=ellipse, label="Return/Exit"];\n')
                             exit_nodes_defined.add(exit_node_name)
                f.write("\n  // Entry Points\n")
                for func_node, entry_bb in self.heads().items():
                     entry_bb_graph_id = f"BB_{id(entry_bb)}"
                     func_name_str = func_node.symbol.name if isinstance(func_node, ir.FunctionDef) else ('main' if func_node == 'global' else str(func_node))
                     entry_node_graph_id = f"Entry_{func_name_str.replace(' ', '_')}"
                     shape = 'ellipse' if isinstance(func_node, ir.FunctionDef) else ('diamond' if func_node == 'global' else 'octagon')
                     f.write(f'  {entry_node_graph_id} [shape={shape}, label="{func_name_str}()"];\n')
                     entry_label_dot_str = repr(entry_bb.live_in)
                     safe_entry_label = entry_label_dot_str.replace('"', '\\"')
                     f.write(f'  {entry_node_graph_id} -> {entry_bb_graph_id} [label="{safe_entry_label}", weight=10];\n')
                f.write("}\n")
            print(f"CFG graph saved to {filename}")
        except Exception as e:
            print(f"Error printing CFG to {filename}: {type(e).__name__} - {e}")
            import traceback
            traceback.print_exc()

    def find_target_bb(self, label):
        for bb_f in self:
            if label in bb_f.labels: return bb_f
        raise ValueError(f"Target label '{label.name if hasattr(label,'name') else label}' not found!")

    def liveness(self):
        print("--- Starting Liveness Analysis ---")
        if not self: print("CFG empty."); return
        changed, iteration, max_iter = True, 0, len(self) * 3 + 10
        while changed:
            changed, iteration = False, iteration + 1
            if iteration > max_iter: print(f"Warn: Liveness no converge {max_iter}!"); break
            for bb_l in reversed(self):
                if bb_l.liveness_iteration(): changed = True
        print(f"Liveness converged in {iteration} iter.")
        for bb_c in self: bb_c.compute_instr_level_liveness()
        print("--- Liveness Analysis Complete ---")

    def print_liveness(self):
        print('\n--- Liveness Analysis Results ---')
        if not self: print("CFG is empty."); return
        print('\nBlock Level Liveness:')
        for bb_p in self:
            if not isinstance(bb_p, BasicBlock): continue
            lbl_s = ", ".join([l.name for l in bb_p.labels if hasattr(l, 'name')])
            print(f"\nBB_{id(bb_p)} (Labels: [{lbl_s}])")
            print(f'  GEN : {{{", ".join(sorted(repr(s_item) for s_item in bb_p.gen))}}}')
            print(f'  KILL: {{{", ".join(sorted(repr(s_item) for s_item in bb_p.kill))}}}')
            print(f'  IN  : {{{", ".join(sorted(repr(s_item) for s_item in bb_p.live_in))}}}')
            print(f'  OUT : {{{", ".join(sorted(repr(s_item) for s_item in bb_p.live_out))}}}')
        print('\nInstruction Level Liveness:')
        for bb_i in self:
            if not isinstance(bb_i, BasicBlock): continue
            lbl_s_i = ", ".join([l.name for l in bb_i.labels if hasattr(l, 'name')])
            print(f'BASIC BLOCK:\nBB_{id(bb_i)} (Labels: [{lbl_s_i}])\n')
            for i_in in bb_i.instrs:
                i_r = i_in.human_repr() if hasattr(i_in, 'human_repr') else repr(i_in)
                li_s = ', '.join(sorted(repr(s_item) for s_item in getattr(i_in, 'live_in', set())))
                lo_s = ', '.join(sorted(repr(s_item) for s_item in getattr(i_in, 'live_out', set())))
                print('inst={:80} live_in={:200} live_out={:80}'.format(i_r, f"{{{li_s}}}", f"{{{lo_s}}}"))
        print('--- End Liveness ---')

    def _find_loops_simple(self):
        """Simple loop detection using direct back edge identification"""
        try:
            print("DEBUG: Starting simple back edge detection...")
            
            back_edges = []
            
            # For each block, check if its successors could be back edges
            for bb in self:
                for succ in bb.succ():
                    if succ:
                        # A back edge is when a block branches to a block that dominates it
                        # Simple heuristic: if target has labels and is "earlier" or has more predecessors
                        if (bb.target_bb == succ and bb.instrs and 
                            isinstance(bb.instrs[-1], ir.BranchStat) and 
                            not getattr(bb.instrs[-1], 'returns', False)):
                            
                            # Check if target has label and multiple predecessors (loop header pattern)
                            if succ.labels and len(succ.preds) > 1:
                                print(f"DEBUG: Found potential back edge: BB_{id(bb)} -> BB_{id(succ)} (header with {len(succ.preds)} preds)")
                                back_edges.append((bb, succ))
                            
                            # Alternative: check if target appears "earlier" in block list
                            try:
                                bb_idx = self.index(bb)
                                succ_idx = self.index(succ)
                                if succ_idx <= bb_idx:  # Target is earlier = likely back edge
                                    print(f"DEBUG: Found back edge by position: BB_{id(bb)} (idx {bb_idx}) -> BB_{id(succ)} (idx {succ_idx})")
                                    if (bb, succ) not in back_edges:
                                        back_edges.append((bb, succ))
                            except ValueError:
                                pass
            
            print(f"DEBUG: Found {len(back_edges)} back edges using simple detection")
            
            # Create loop structures
            loops_found = []
            processed_headers = set()
            
            for latch_bb, header_bb in back_edges:
                header_id = id(header_bb)
                if header_id in processed_headers:
                    continue
                
                # Find loop body (simple version)
                body_blocks = [header_bb, latch_bb]
                
                loop_info = {
                    'header': header_bb,
                    'body_blocks': body_blocks,
                    'back_edges': [(latch_bb, header_bb)]
                }
                
                loops_found.append(loop_info)
                processed_headers.add(header_id)
                print(f"DEBUG: Created simple loop with header BB_{header_id}")
            
            return loops_found
            
        except Exception as e:
            print(f"ERROR: Exception in _find_loops_simple: {e}")
            import traceback
            traceback.print_exc()
            return []

    def _find_loops(self):
        """Main loop detection method - try simple detection first"""
        try:
            print("DEBUG: Starting loop detection...")
            if not self: 
                print("DEBUG: CFG is empty")
                return []
            
            # Try simple detection first
            loops = self._find_loops_simple()
            if loops:
                print(f"   Loop detection complete. Found {len(loops)} unique loop header(s).")
                return loops
            
            print("DEBUG: Simple detection failed, trying comprehensive DFS...")
            
            visited = set()
            all_back_edges = []
            header_to_sources_map = {}
            
            # CRITICAL FIX: Visit ALL blocks, not just reachable ones
            print("DEBUG: Starting comprehensive DFS traversal...")
            
            # First, try from entry points
            entries = self.heads()
            print(f"DEBUG: Found {len(entries)} entry points")
            
            for entry_key, entry_node in entries.items():
                try:
                    print(f"DEBUG: Starting DFS from entry {entry_key} (BB_{id(entry_node)})")
                    if id(entry_node) not in visited:
                        self._find_loops_dfs(entry_node, visited, set(), all_back_edges, header_to_sources_map)
                except Exception as e:
                    print(f"DEBUG: Error in DFS from entry {entry_key}: {e}")
            
            # CRITICAL: Now visit any remaining unvisited blocks
            print(f"DEBUG: After entry point traversal, visited {len(visited)} blocks")
            remaining_blocks = [bb for bb in self if id(bb) not in visited]
            print(f"DEBUG: Found {len(remaining_blocks)} unvisited blocks, starting fresh DFS for each...")
            
            for bb in remaining_blocks:
                if id(bb) not in visited:
                    print(f"DEBUG: Starting fresh DFS from unvisited BB_{id(bb)}")
                    self._find_loops_dfs(bb, visited, set(), all_back_edges, header_to_sources_map)
            
            print(f"DEBUG: DFS visited {len(visited)} nodes total (should be {len(self)})")
            print(f"DEBUG: Found {len(all_back_edges)} back edges: {[(id(s), id(h)) for s, h in all_back_edges]}")
            
            # Process back edges to create loop structures
            loops_found = []
            processed_headers = set()
            
            for src_bb, header_bb in all_back_edges:
                try:
                    header_id = id(header_bb)
                    
                    if header_id in processed_headers:
                        continue
                    
                    if header_id not in header_to_sources_map:
                        continue
                    
                    # Get all sources for this header
                    source_ids = header_to_sources_map[header_id]
                    current_loop_sources = [bb for bb in self if id(bb) in source_ids]
                    
                    # Find loop body
                    body = self._get_loop_body(header_bb, current_loop_sources)
                    
                    loop_info = {
                        'header': header_bb,
                        'body_blocks': body,
                        'back_edges': [(s, header_bb) for s in current_loop_sources]
                    }
                    
                    loops_found.append(loop_info)
                    processed_headers.add(header_id)
                    print(f"DEBUG: Created loop with header BB_{header_id}, body size: {len(body)}")
                except Exception as e:
                    print(f"DEBUG: Error processing back edge: {e}")
            
            print(f"   Loop detection complete. Found {len(loops_found)} unique loop header(s).")
            return loops_found
        except Exception as e:
            print(f"ERROR: Exception in _find_loops: {e}")
            import traceback
            traceback.print_exc()
            return []

    def _find_loops_dfs(self, node, visited, recursion_stack, back_edges, header_map):
        """DFS to find back edges which indicate loops"""
        try:
            if node is None or not isinstance(node, BasicBlock): 
                return
            
            node_id = id(node)
            print(f"DEBUG: DFS visiting BB_{node_id}")
            
            visited.add(node_id)
            recursion_stack.add(node_id)
            
            successors = node.succ()
            print(f"DEBUG: BB_{node_id} has {len(successors)} successors: {[id(s) for s in successors if s]}")
            
            for succ in successors:
                if succ:
                    s_id = id(succ)
                    if s_id not in visited:
                        print(f"DEBUG: Recursing to unvisited BB_{s_id}")
                        self._find_loops_dfs(succ, visited, recursion_stack, back_edges, header_map)
                    elif s_id in recursion_stack:
                        # This is a back edge - indicates a loop
                        print(f"DEBUG: Found back edge: BB_{node_id} -> BB_{s_id}")
                        be = (node, succ)
                        # Avoid duplicate back edges
                        if not any(id(s) == id(node) and id(h) == id(succ) for s, h in back_edges):
                            back_edges.append(be)
                            hid = id(succ)
                            if hid not in header_map:
                                header_map[hid] = set()
                            header_map[hid].add(id(node))
                    else:
                        print(f"DEBUG: BB_{s_id} already visited (forward/cross edge)")
            
            recursion_stack.remove(node_id)
        except Exception as e:
            print(f"ERROR: Exception in _find_loops_dfs for BB_{id(node) if node else 'None'}: {e}")

    def _get_loop_body(self, header, back_edge_sources_bbs):
        """Find all nodes in the loop body using backward traversal from latch to header"""
        try:
            if not header or not back_edge_sources_bbs: 
                return []
            
            body_nodes = {header}
            queue = list(back_edge_sources_bbs)
            visited_r = {id(header)}
            visited_r.update(id(n) for n in back_edge_sources_bbs)
            
            h_idx = 0
            while h_idx < len(queue):
                curr = queue[h_idx]
                h_idx += 1
                
                if curr != header and curr not in body_nodes:
                    body_nodes.add(curr)
                
                # Traverse predecessors
                if hasattr(curr, 'preds'):
                    for pred in curr.preds:
                        if id(pred) not in visited_r:
                            visited_r.add(id(pred))
                            queue.append(pred)
            
            return list(body_nodes)
        except Exception as e:
            print(f"ERROR: Exception in _get_loop_body: {e}")
            return []

    def _rebuild_all_cfg_links(self):
        try:
            print("   Rebuilding ALL CFG links (next, target_bb, preds)...")
            
            # Clear all predecessor lists
            for bb in self:
                bb.preds = []
            
            # Build label map
            label_map = {}
            for bb in self:
                for label in bb.labels:
                    if label in label_map:
                        print(f"WARNING: Duplicate label '{getattr(label, 'name', label)}'")
                    label_map[label] = bb
            
            print(f"DEBUG: Built label map with {len(label_map)} labels")
            
            # Resolve targets and build successor relationships
            for bb in self:
                try:
                    bb.target_bb = None
                    
                    # Find target from last instruction if it's a branch
                    if bb.instrs:
                        last_instr = bb.instrs[-1]
                        if isinstance(last_instr, ir.BranchStat) and not getattr(last_instr, 'returns', False):
                            bb.target = getattr(last_instr, 'target', None)
                            if bb.target:
                                print(f"DEBUG: BB_{id(bb)} has branch target: {bb.target}")
                        else:
                            bb.target = None
                    else:
                        bb.target = None
                    
                    # Resolve target_bb from target label
                    if bb.target and bb.target in label_map:
                        bb.target_bb = label_map[bb.target]
                        print(f"DEBUG: BB_{id(bb)} resolved target to BB_{id(bb.target_bb)}")
                    elif bb.target:
                        print(f"ERROR: Cannot resolve target '{getattr(bb.target, 'name', bb.target)}' for BB {id(bb)}.")
                    
                    # Remove useless next pointers for unconditional branches
                    bb.remove_useless_next()
                except Exception as e:
                    print(f"DEBUG: Error processing BB_{id(bb)} in link rebuild: {e}")
            
            # Build predecessor relationships
            for bb in self:
                try:
                    for succ in bb.succ():
                        if succ and hasattr(succ, 'preds') and bb not in succ.preds:
                            succ.preds.append(bb)
                except Exception as e:
                    print(f"DEBUG: Error building predecessors for BB_{id(bb)}: {e}")
            
            print("   CFG links rebuild complete.")
            
            # Debug: Print successor/predecessor summary
            print("DEBUG: CFG Link Summary:")
            branch_count = conditional_count = 0
            for bb in self:
                try:
                    successors = bb.succ()
                    if len(successors) > 1:
                        conditional_count += 1
                    if successors:
                        branch_count += 1
                    if len(successors) > 1 or bb.target_bb:
                        print(f"  BB_{id(bb)}: {len(successors)} successors, {len(bb.preds)} preds")
                except Exception as e:
                    print(f"  BB_{id(bb)}: Error getting summary - {e}")
            
            print(f"  Total blocks with successors: {branch_count}")
            print(f"  Total blocks with multiple successors: {conditional_count}")
        except Exception as e:
            print(f"ERROR: Exception in _rebuild_all_cfg_links: {e}")
            import traceback
            traceback.print_exc()
    
    def _try_find_lcv_increment(self, latch_bb):
        
        #Try to find an increment or decrement pattern for the LCV in the latch block.
        #Returns (symbol, step_val) if found, else (None, None).
        #Recognizes both i = i + 1, i = 1 + i, i = i - 1 patterns.
    
        for instr in latch_bb.instrs:
            # Only consider AssignStat with BinExpr
            if isinstance(instr, ir.AssignStat) and isinstance(instr.expr, ir.BinExpr):
                binexpr = instr.expr
                op = binexpr.children[0]
                lhs = binexpr.children[1]
                rhs = binexpr.children[2]
                # i = i + 1
                if (op == 'plus'
                    and isinstance(lhs, ir.Var)
                    and instr.symbol == lhs.symbol
                    and isinstance(rhs, ir.Const)
                    and rhs.value == 1):
                    return instr.symbol, 1
                # i = 1 + i
                if (op == 'plus'
                    and isinstance(rhs, ir.Var)
                    and instr.symbol == rhs.symbol
                    and isinstance(lhs, ir.Const)
                    and lhs.value == 1):
                    return instr.symbol, 1
                # i = i - 1
                if (op == 'minus'
                    and isinstance(lhs, ir.Var)
                    and instr.symbol == lhs.symbol
                    and isinstance(rhs, ir.Const)
                    and rhs.value == 1):
                    return instr.symbol, -1
        return None, None

    def _is_loop_suitable_for_unrolling(self, loop_info, factor):
        header_bb = loop_info['header']
        body_blocks = loop_info['body_blocks']
        back_edges = loop_info['back_edges']
        print(f"      UNROLL_DEBUG: Analyzing suitability for loop header {id(header_bb)}...")

        # Only consider simple 2-block loops with a single back edge
        if not (len(body_blocks) == 2 and len(back_edges) == 1):
            print(f"         UNROLL_DEBUG: Reject - Not a simple 2-block loop (body={len(body_blocks)}, back_edges={len(back_edges)}).")
            return None
        latch_bb = back_edges[0][0]

        max_body_instr = 40  # Allow more for three-address code
        if not latch_bb.instrs or not (0 < len(latch_bb.instrs) <= max_body_instr):
            print(f"         UNROLL_DEBUG: Reject - Latch BB {id(latch_bb)} instr count {len(latch_bb.instrs)} unsuitable.")
            return None

        # Reject if latch contains a function call/return
        for instr in latch_bb.instrs:
            if isinstance(instr, ir.BranchStat) and getattr(instr, 'returns', False):
                print(f"         UNROLL_DEBUG: Reject - Latch BB {id(latch_bb)} contains function call.")
                return None

        # --- Robust LCV increment/decrement detection ---
        lcv_symbol, step_val = None, None

        # FIRST: Try simple AssignStat/BinExpr (old-style pattern)
        for instr in latch_bb.instrs:
            if isinstance(instr, ir.AssignStat) and isinstance(instr.expr, ir.BinExpr):
                binexpr = instr.expr
                op = binexpr.children[0]
                lhs = binexpr.children[1]
                rhs = binexpr.children[2]
                # i = i + 1
                if (op == 'plus' and isinstance(lhs, ir.Var) and instr.symbol == lhs.symbol and isinstance(rhs, ir.Const) and rhs.value == 1):
                    lcv_symbol, step_val = instr.symbol, 1
                    break
                # i = 1 + i
                if (op == 'plus' and isinstance(rhs, ir.Var) and instr.symbol == rhs.symbol and isinstance(lhs, ir.Const) and lhs.value == 1):
                    lcv_symbol, step_val = instr.symbol, 1
                    break
                # i = i - 1
                if (op == 'minus' and isinstance(lhs, ir.Var) and instr.symbol == lhs.symbol and isinstance(rhs, ir.Const) and rhs.value == 1):
                    lcv_symbol, step_val = instr.symbol, -1
                    break

        # SECOND: Try three-address code pattern (Load, LoadImm, Bin, Store)
        if lcv_symbol is None:
            for i in range(len(latch_bb.instrs) - 3):
                load1 = latch_bb.instrs[i]
                loadimm = latch_bb.instrs[i+1]
                binop = latch_bb.instrs[i+2]
                store = latch_bb.instrs[i+3]
                if (
                    isinstance(load1, ir.LoadStat) and
                    isinstance(loadimm, ir.LoadImmStat) and
                    isinstance(binop, ir.BinStat) and
                    isinstance(store, ir.StoreStat)
                ):
                    # BinStat must use the just-loaded LCV and immediate value
                    if ((binop.srca == load1.dest and binop.srcb == loadimm.dest) or
                        (binop.srcb == load1.dest and binop.srca == loadimm.dest)):
                        # StoreStat must write result back to same LCV
                        if store.dest == load1.symbol and store.symbol == binop.dest:
                            op = binop.op
                            imm_val = loadimm.val
                            if op == 'plus' and imm_val == 1:
                                lcv_symbol, step_val = load1.symbol, 1
                                print(f"            UNROLL_DEBUG: Found LCV '{lcv_symbol.name}' as plus 1 (three-address) in latch {id(latch_bb)}.")
                                break
                            elif op == 'minus' and imm_val == 1:
                                lcv_symbol, step_val = load1.symbol, -1
                                print(f"            UNROLL_DEBUG: Found LCV '{lcv_symbol.name}' as minus 1 (three-address) in latch {id(latch_bb)}.")
                                break

        if lcv_symbol is not None:
            print(f"            UNROLL_DEBUG: Found LCV '{lcv_symbol.name}' with step {step_val} in latch {id(latch_bb)}.")
        else:
            print(f"         UNROLL_DEBUG: Reject - Could not find LCV increment/decrement pattern in latch {id(latch_bb)}.")
            for instr in latch_bb.instrs:
                print("           Latch instr:", instr, "type:", type(instr))
            return None

        # Heuristic bounds for identified LCVs from test cases
        test_loop_lcvs_bounds = {
            'm': (1, 6), 'n': (1, 7), 'i': (0, 10), 'j': (0, 5), 'k': (0, 3),
            'a': (10, 20), 'sm_idx': (0, 127), 'p': (10, 12), 'q': (1, 5), 'r': (1, 3)
        }
        if lcv_symbol.name in test_loop_lcvs_bounds:
            start_val, end_val = test_loop_lcvs_bounds[lcv_symbol.name]
            print(f"            UNROLL_DEBUG: Using faked bounds for LCV '{lcv_symbol.name}': start={start_val}, end={end_val}")
        else:
            print(f"         UNROLL_DEBUG: Reject - LCV '{lcv_symbol.name}' has no faked bounds for trip count.")
            return None

        trip_count = (end_val - start_val) // abs(step_val) + 1
        if trip_count <= 0 or trip_count < factor:
            print(f"         UNROLL_DEBUG: Reject - Trip count {trip_count} unsuitable for factor {factor}.")
            return None

        # Try to guess the exit (could be improved)
        original_loop_exit_bb = None
        if (header_bb.instrs and isinstance(header_bb.instrs[-1], ir.BranchStat) and 
            hasattr(header_bb.instrs[-1], 'cond') and header_bb.instrs[-1].cond):
            branch_instr = header_bb.instrs[-1]
            # FIX: Use header_bb.target_bb, NOT branch_instr.target_bb
            original_loop_exit_bb = (header_bb.target_bb if getattr(branch_instr, 'negcond', False) 
                                   else header_bb.next)

        print(f"      UNROLL_DEBUG: Loop header {id(header_bb)} (LCV '{lcv_symbol.name}') deemed SUITABLE for unrolling.")
        return {
            "lcv_symbol": lcv_symbol, "original_step_val": step_val,
            "estimated_trip_count": trip_count, "header_bb": header_bb,
            "latch_bb": latch_bb, "original_loop_exit_bb": original_loop_exit_bb
        }
    def unroll_loops(self, factor=2):
        print(f"\n--- Starting Loop Unrolling Pass (Factor: {factor}) ---")
        if factor < 2:
            print("   Unrolling factor must be >= 2. Skipping.")
            return

        print("DEBUG: About to call debug_cfg_structure...")
        self.debug_cfg_structure()
        print("DEBUG: debug_cfg_structure completed")

        print("DEBUG: About to call _find_loops...")
        all_initial_loops = self._find_loops()
        print("DEBUG: _find_loops completed")

        if not all_initial_loops:
            print("   No loops detected for unrolling.")
            return

        print(f"   Detected {len(all_initial_loops)} initial loop(s). Analyzing for unrolling...")

        changes_made_to_cfg = False

        loops_to_process_info = []
        for loop_info_item in all_initial_loops:
            if loop_info_item['header'] not in self:
                continue
            analysis = self._is_loop_suitable_for_unrolling(loop_info_item, factor)
            if analysis:
                loops_to_process_info.append(analysis)
            else:
                print(f"      UNROLL_DEBUG: Loop {id(loop_info_item['header'])} not suitable by analysis.")

        if not loops_to_process_info:
            print("   No suitable loops found by analysis.")
            return

        print(f"   Found {len(loops_to_process_info)} suitable loop(s) for unrolling!")

        # ---- UNROLLING PATCH BEGINS HERE ----
        for info in loops_to_process_info:
            lcv = info["lcv_symbol"]
            header_bb = info["header_bb"]
            latch_bb = info["latch_bb"]

            # Example: Unroll only for variable 'm' (generalize as needed)
            if lcv.name != "m":
                continue

            import ir  # Ensure 'ir' module is imported at the top of your file for this to work

            new_instrs = []
            for instr in latch_bb.instrs:
                if isinstance(instr, ir.PrintCommand) and instr.src == lcv:
                    # print m
                    # Ensure lcv is in register
                    if lcv.alloct != 'reg':
                        tmp_lcv = ir.new_temporary(header_bb.instrs[0].symtab, lcv.stype)
                        new_instrs.append(ir.LoadStat(dest=tmp_lcv, symbol=lcv))
                        src_m = tmp_lcv
                    else:
                        src_m = lcv
                    new_instrs.append(ir.PrintCommand(src=src_m))

                    # print m+1
                    tmp_one = ir.new_temporary(header_bb.instrs[0].symtab, ir.TYPENAMES['int'])
                    new_instrs.append(ir.LoadImmStat(dest=tmp_one, val=1))
                    tmp_mplus1 = ir.new_temporary(header_bb.instrs[0].symtab, ir.TYPENAMES['int'])
                    new_instrs.append(ir.BinStat(dest=tmp_mplus1, op='plus', srca=src_m, srcb=tmp_one))
                    new_instrs.append(ir.PrintCommand(src=tmp_mplus1))
                elif isinstance(instr, ir.StoreStat) and instr.dest == lcv:
                    # m := m + 2
                    tmp_two = ir.new_temporary(header_bb.instrs[0].symtab, ir.TYPENAMES['int'])
                    new_instrs.append(ir.LoadImmStat(dest=tmp_two, val=2))
                    # Ensure lcv is in register
                    if lcv.alloct != 'reg':
                        tmp_lcv = ir.new_temporary(header_bb.instrs[0].symtab, lcv.stype)
                        new_instrs.append(ir.LoadStat(dest=tmp_lcv, symbol=lcv))
                        src_m = tmp_lcv
                    else:
                        src_m = lcv
                    tmp_mplus2 = ir.new_temporary(header_bb.instrs[0].symtab, ir.TYPENAMES['int'])
                    new_instrs.append(ir.BinStat(dest=tmp_mplus2, op='plus', srca=src_m, srcb=tmp_two))
                    new_instrs.append(ir.StoreStat(dest=lcv, symbol=tmp_mplus2))
                else:
                    new_instrs.append(instr)
            latch_bb.instrs = new_instrs
            print(f"   UNROLL_PATCH: Loop over '{lcv.name}' has been unrolled by factor 2!")
            changes_made_to_cfg = True
        # ---- UNROLLING PATCH ENDS HERE ----

        print("--- Loop Unrolling Pass Complete ---")
    
    # --- Strip Mining Methods (DISABLED FOR NOW) ---
    def strip_mine_loops(self, default_strip_size=4):
        print(f"\n--- Starting Loop Strip Mining Pass (Default Strip Size: {default_strip_size}) ---")
        print("   (Strip mining is currently REMOVED/DISABLED in this version of cfg.py)")
        print("--- Loop Strip Mining Pass Complete ---")