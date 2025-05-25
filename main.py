#!/usr/bin/env python3

"""The main function of the compiler, AKA the compiler driver"""

import lexer
import parser
from support import * # Assumes lowering, flattening, print_dotty, get_node_list
from datalayout import perform_data_layout # Specific import
from cfg import CFG # Specific import
from regalloc import LinearScanRegisterAllocator # Specific import
from codegen import generate_code # Specific import
import ir # Often needed for type checking or creating nodes if main does any IR manipulation

# Ensure copy is imported if used anywhere, though typically transformations are in other modules
# import copy

def compile_program(text):
    print("--- Starting Compilation ---")
    lex = lexer.Lexer(text)
    pars = parser.Parser(lex) # Initialize parser

    print("\n--- Parsing Program ---")
    res = pars.program() # Parse and get root IR node
    print("\n--- Initial IR Tree (from Parser) ---")
    print(res) # Print initial IR
    print_dotty(res, "ir_initial.dot") # Visualize initial IR

    # Lowering Pass
    print("\n--- Navigating: Applying Lowering ---")
    res.navigate(lowering) # Apply lowering to all relevant nodes
    print("\n--- IR Tree After Lowering ---")
    print(res)
    print_dotty(res, "ir_after_lowering.dot")

    # Flattening Pass (often after lowering)
    print("\n--- Navigating: Applying Flattening ---")
    res.navigate(flattening) # Flatten StatLists
    print("\n--- IR Tree After Flattening ---")
    print(res)
    print_dotty(res, "ir_after_flattening.dot")

    # Data Layout Pass
    print("\n--- Performing Data Layout ---")
    perform_data_layout(res) # Assign memory locations to symbols
    print("\n--- IR Tree After Data Layout (Symbols might have allocinfo) ---")
    print(res)
    # No specific dotty for data layout unless it changes structure visible to dotty

    # CFG Construction
    print("\n--- Constructing CFG ---")
    cfg = CFG(res) # Build initial CFG from lowered, flattened, data-layout-processed IR
    print(f"Initial CFG constructed with {len(cfg)} basic blocks.")
    cfg.print_cfg_to_dot("cfg_initial.dot")

    # --- OPTIMIZATION: Strip Mining ---
    print("\n--- OPTIMIZATION: Attempting Loop Strip Mining ---")
    cfg.strip_mine_loops(strip_size=4) # Call strip mining
    print("\n--- CFG After Attempting Strip Mining ---")
    cfg.print_cfg_to_dot("cfg_after_strip_mining_attempt.dot")
    # --- End Strip Mining ---

    # --- OPTIMIZATION: Loop Unrolling (Placeholder) ---
    print("\n--- OPTIMIZATION: Attempting Loop Unrolling ---")
    cfg.unroll_loops(factor=2) # Call unrolling placeholder
    print("\n--- CFG After Attempting Unrolling ---")
    cfg.print_cfg_to_dot("cfg_after_unrolling_attempt.dot")
    # --- End Loop Unrolling ---

    # Liveness Analysis
    print("\n--- Performing Liveness Analysis (on potentially modified CFG) ---")
    cfg.liveness()
    # cfg.print_liveness() # This can be very verbose, enable if needed
    cfg.print_cfg_to_dot("cfg_final_with_liveness.dot") # Save CFG with liveness info on edges

    # Register Allocation
    print("\n--- Performing Register Allocation ---")
    # Ensure nregs matches what your codegenhelp/target expects
    # The '11' here is from your original regalloc.py call (0 to 10 usable for general purpose)
    ra = LinearScanRegisterAllocator(cfg, nregs=11)
    reg_alloc_map = ra() # Get the register allocation mapping
    print("\n--- Register Allocation Map ---")
    print(reg_alloc_map)

    # Code Generation
    print("\n--- Generating Code ---")
    # generate_code needs the original IR tree (res) and the register allocation map.
    # The IR tree 'res' might have been modified by lowering/flattening if those
    # passes change it in-place (which navigate() often implies).
    # The 'cfg' object contains the BasicBlocks with instructions that now have
    # register allocation information implicitly through reg_alloc_map.
    # Ensure generate_code can use reg_alloc_map correctly.
    code = generate_code(res, reg_alloc_map)
    print("\n--- Generated Assembly Code ---")
    print(code)
    print("--- Compilation Complete ---")

    return code


def driver_main():
    from lexer import __test_program # Import the test program string
    current_test_program = __test_program # Use a different variable name

    import sys
    print("Compiler arguments:", sys.argv)
    if len(sys.argv) >= 2: # If a filename is provided as an argument
        input_filename = sys.argv[1]
        try:
            with open(input_filename, 'r') as inf:
                current_test_program = inf.read()
            print(f"Successfully read program from file: {input_filename}")
        except FileNotFoundError:
            print(f"ERROR: Input file '{input_filename}' not found. Using default test program.")
        except Exception as e:
            print(f"ERROR: Could not read file '{input_filename}': {e}. Using default test program.")

    print("\n--- Compiling Program ---")
    print("Input Program Snippet:\n" + "-"*20 + "\n" + current_test_program[:200] + "...\n" + "-"*20)

    final_code = compile_program(current_test_program)

    output_filename = None
    if len(sys.argv) > 2: # If a second argument is given, assume it's output file
        # If only one arg was given (input), this won't be true.
        # If input came from file (sys.argv[1]), then sys.argv[2] is output.
        # If input was default, then sys.argv[1] could be output if len(sys.argv) == 2
        # This logic needs to be clear:
        if len(sys.argv) == 2 and sys.argv[1] != __file__: # If one arg, and it's not the script itself, assume it's output
            output_filename = sys.argv[1]
        elif len(sys.argv) > 2: # If two or more args, last one is output
             output_filename = sys.argv[-1]


    if output_filename:
        try:
            with open(output_filename, 'w') as outf:
                outf.write(final_code)
            print(f"Successfully wrote generated code to: {output_filename}")
        except Exception as e:
            print(f"ERROR: Could not write to output file '{output_filename}': {e}")


if __name__ == '__main__':
    driver_main()