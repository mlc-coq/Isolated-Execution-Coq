# Isolated-Execution-Coq
Coq files for isolated execution paper

# FILES
# RuntimeDefinitions.v
Coq definitions from the "Runtime Definitions" diagram (top of file), as well as lemmas and functions that are commonly used through the later files (bottom of file).

# AppendixC.v
Functions for Auxiliary "Definitions Related to Single-Level Physical Cache Units" (currently section A.4). Contains cachelet-related functions (allocation, deallocation, read, write, invalidation, and update).

# AppendixD.v
Function definitions for "Definitions and Auxiliary Functions of the Cache Replacement Logic" (currently section A.5). There are only four functions here:
- equal_enclave_IDs: checks if two enclaves are equal, which happens when both are active with the same ID or both are inactive
- contains_way_ID: in paper, checks if PLRU-tree holds a way ID
- update: in paper, updates PLRU tree after read or write (implemention later in paper)
- replace: in paper, finds which enclave to evict from a PLRU tree

# AppendixE.v
Functions for "Definitions and Auxiliary Functions of the Enclave" (currently section A.6). Contains enclave-related functions (creation, update, and elimination).

# AppendixF.v
Functions for "Auxiliary Defintions of Main Memory" (currently section A.7). Contains functions to reinitialize memory.

# MLCOperations.v
Definitions and functions for the mutli-level cache, separated into two parts:

Cache Hierarchy Tree:
In the paper, the cache hierarchy is represented as a function that operates on this tree.
In coq, the cache hierarchy is represented as a mapping from a node on the tree (the root node, a core, or a cache unit) to the path to the root node.
For example, given a single core cpu with an L1 and L2, we would get some tree structure that looks like:
core -> l1 -> l2 -> root
then, the mapping in coq would look like:
core: [ core, l1, l2, root ]
l1: [ l1, l2, root ]
l2: [ l2, root ]
root: [ root ]

Multi-Level Cache Operations:
Definitions for functions in the paper named MLC Read (currently fig 6), MLC Allocation (currently fig 7), MLC Write (currently fig 17), and MLC Deallocation (currently fig 18).

# Semantics.v
Definition for operational semantics of MLC and TEE. This include two groups of semantics, multi-process semantics and single process semantics.
The multi-process semantics are [MULTI] and [CONTEXTSWITCH], as defined in the paper.
The single process semantics are evaluated during the [MULTI] semantic, as defined in the paper.

This section also contains a definition of "disjoint enclave states", which claims that given any two different enclave states, their domains must be disjoint. This definitions is used in the [MULTI] semantic, and is a necessary condition for well-formedness.

# WellFormed.v
The first part contains "helper lemmas", which is a list of lemmas used in later proofs.

The second part contains definition and preservation proof of the first three conditions of well-formedness. This includes F ⊆ dom(C) (defined as well-formed 1), ran(V(e)) ⊆ dom(C) for any e ∈ dom(V) (defined as well-formed 2).

Well-formed 1 and well-formed 2 preservation are closely linked. This is due to the [CREATE] and [DESTROY] semantics.

# WellFormedEnclaveState.v

# WellFormed2.v
F ∩ ran(V (e)) = ∅ for any e ∈ dom(V) (defined as well-formed 3).

# WellFormed3.v

# Note on induction in coq
In coq, variables can be more or less general in induction proofs depending on which variables are defined in "intros".