From Coq Require Import Lists.List.
From Coq Require Import FSets.FMapList.
From Coq Require Import FSets.FMapFacts.
From Coq Require Import Structures.OrderedTypeEx.
From Coq Require Import Init.Nat.
From Coq Require Import Bool.Bool.
From Coq Require Import Logic.Eqdep_dec.

Module Import NatMap := FMapList.Make(Nat_as_OT).
Module OrderedPair := PairOrderedType Nat_as_OT Nat_as_OT.
Module Import PairMap := FMapList.Make(OrderedPair).
Module Import CacheletMap := PairMap.
Module NatMapProperties := WProperties_fun Nat_as_OT NatMap.
Module PairMapProperties := WProperties_fun OrderedPair PairMap.
Module CacheletMapProperties := PairMapProperties.


(* Identifiers and Atomic Values *)
Definition core_ID := nat.
Definition physical_cache_unit_ID := nat.
Definition way_ID := nat.
Definition set_ID := nat.
Definition block_ID := nat.
Definition register_ID := nat.
Definition raw_enclave_ID := nat.
Definition data_offset := nat.
Definition cache_tag_value := nat.
Inductive memory_address :=
| address : block_ID -> data_offset -> memory_address.
Inductive instruction : Type :=
| create: register_ID -> register_ID -> register_ID -> (list register_ID) -> instruction
| enter: register_ID -> instruction
| exit: instruction
| destroy: register_ID -> instruction
| load: memory_address -> register_ID -> instruction
| store: register_ID -> memory_address -> instruction
| br: register_ID -> register_ID -> instruction.
Definition number := nat.
Definition process_ID := nat.


(* Memory/Register-Related Structures *)
Inductive data : Type :=
| data_value : number -> data
| data_none : data.
Inductive memory_value : Type :=
| memory_value_instruction : instruction -> memory_value
| memory_value_data : data -> memory_value.


(* Enclave-Related Structures *)
Inductive enclave_memory_range_value :=
| enclave_address_and_data : memory_address -> number -> enclave_memory_range_value.
Inductive enclave_ID : Type :=
| enclave_ID_active : raw_enclave_ID -> enclave_ID
| enclave_ID_inactive : enclave_ID.
Definition enclave_memory_range : Type := NatMap.t enclave_memory_range_value.
Inductive enclave_state : Type := 
| enclave_state_value : enclave_ID -> enclave_memory_range -> enclave_state.


(* CC-Related Structures *)
Definition way_mask := list way_ID.
Inductive validity_bit : Type :=
| valid_bit : validity_bit
| dirty_bit : validity_bit.
Definition cachelet_index := (way_ID * set_ID) % type.
Inductive nullable_cachelet_index : Type :=
| cachelet_index_defined : cachelet_index -> nullable_cachelet_index
| cachelet_index_none : nullable_cachelet_index.

Definition data_block := NatMap.t memory_value.
Definition remapping_list := NatMap.t way_mask.
(* Extra structure to hold data in way_set_cache *)
Inductive way_set_cache_value : Type :=
| valid_bit_tag_and_data : validity_bit -> cache_tag_value -> data_block -> way_set_cache_value.
Definition way_set_cache := PairMap.t way_set_cache_value.
Definition VPT := NatMap.t remapping_list.
Definition CAT := list cachelet_index.


(* PLRU-Related Structures *)
Inductive selection_bit : Type :=
| LMRU : selection_bit
| RMRU : selection_bit.
Inductive PLRU_leaf : Type :=
| leaf : way_ID -> enclave_ID -> PLRU_leaf.
Inductive PLRU_tree : Type :=
| subtree : selection_bit -> enclave_ID -> PLRU_tree -> PLRU_tree -> PLRU_tree
| subtree_leaf : PLRU_leaf -> PLRU_tree.
Definition set_indexed_PLRU := NatMap.t PLRU_tree.


(* Multi-Level Cache *)
Inductive single_level_cache_unit : Type :=
| single_level_cache : CAT -> VPT -> way_set_cache -> set_indexed_PLRU -> single_level_cache_unit.
Definition multi_level_cache := NatMap.t single_level_cache_unit.


(* Top-Level Structures *)
Inductive process : Type :=
| process_value : enclave_state -> memory_address -> core_ID -> process.
Definition processes := NatMap.t process.
Definition registers := NatMap.t memory_value.
Definition memory := NatMap.t data_block.
Inductive runtime_state : Type :=
| runtime_state_value : multi_level_cache -> memory -> registers -> processes -> runtime_state.




(* Other *)
(* Observation Trace *)
Inductive access_mode : Type :=
| hit_read: access_mode
| hit_write: access_mode
| miss: access_mode.
Inductive observation : Type :=
| observation_tuple: access_mode -> cachelet_index -> physical_cache_unit_ID -> observation.
Definition observation_trace := list observation.
Inductive process_explicit_observation : Type :=
| process_and_observation: process_ID -> observation -> process_explicit_observation.
Definition process_explicit_observation_trace := list process_explicit_observation.
Definition to_process_observation (p: process_ID) (obs: observation): process_explicit_observation := process_and_observation p obs.
Definition to_p_trace (p: process_ID) (obs: observation_trace) := List.map (to_process_observation p) obs.

(* Cachelet Index Equality *)
Definition eq_cachelet_index (c1: cachelet_index) (c2: cachelet_index): bool :=
  match c1, c2 with
  | (w1, s1), (w2, s2) => andb (Nat.eqb w1 w2) (Nat.eqb s1 s2)
  end.

(* Remove From CAT *)
Fixpoint recursive_remove_from_CAT (c: cachelet_index) (F: CAT): CAT :=
  match F with
  | nil => nil
  | c' :: F' =>
    match eq_cachelet_index c c' with
    | true => F'
    | false => c' :: recursive_remove_from_CAT c F'
    end
  end.
Definition remove_CAT (c: cachelet_index) (F: CAT): CAT := recursive_remove_from_CAT c F.

(* Register List to Values *)
Fixpoint recursive_read_register_list (rho: registers) (r_bar: (list register_ID)): (list nat) :=
  match r_bar with
  | nil => nil
  | r :: rs =>
    match (NatMap.find r rho) with
    | None => nil
    | Some r_val =>
      match r_val with
      | memory_value_instruction _ => nil
      | memory_value_data d =>
        match d with
        | data_none => nil
        | data_value x => x :: (recursive_read_register_list rho rs)
        end
      end
    end
  end.
Fixpoint check_valid_register_list (rho: registers) (r_bar: (list register_ID)): bool :=
  match r_bar with
  | nil => true
  | r :: rs =>
    match (NatMap.find r rho) with
    | None => false
    | Some r_val =>
      match r_val with
      | memory_value_instruction _ => false
      | memory_value_data d =>
        match d with
        | data_none => false
        | data_value x => check_valid_register_list rho rs
        end
      end
    end
  end.
Definition read_register_list (rho: registers) (r_bar: (list register_ID)): option (list nat) :=
  match (check_valid_register_list rho r_bar) with
  | false => None
  | true => Some (recursive_read_register_list rho r_bar)
  end.

(* Number to Memory Address *)
Definition num_to_addr (n: nat) (block_size: nat): memory_address :=
  address (shiftr n (log2 block_size)) (n mod block_size).
Definition number_to_memory_address (mu: memory) (n: nat): option memory_address :=
  match (NatMapProperties.to_list mu) with
  | nil => None
  | (_, x) :: _ => Some (num_to_addr n (length (NatMapProperties.to_list x)))
  end.
Definition addr_to_num (l: memory_address) (block_size: nat): nat :=
  match l with
  | address b delta => ((b * block_size) + delta)
  end.
Definition memory_address_to_number (mu: memory) (l: memory_address): option nat :=
  match (NatMapProperties.to_list mu) with
  | nil => None
  | (_, x) :: _ => Some (addr_to_num l (length (NatMapProperties.to_list x)))
  end.
Definition pc_add (pc: memory_address) (n: nat) (block_size: nat): memory_address :=
  num_to_addr ((addr_to_num pc block_size) + n) block_size.
Definition add_to_memory_address (mu: memory) (pc: memory_address) (n: nat): option memory_address :=
  match (NatMapProperties.to_list mu) with
  | nil => None
  | (_, x) :: _ => Some (pc_add pc n (length (NatMapProperties.to_list x)))
  end.

(* Directly Read from Memory *)
Definition memory_read (mu: memory) (l: memory_address): option memory_value :=
  match l with
  | address b delta =>
    match (NatMap.find b mu) with
    | None => None
    | Some D => NatMap.find delta D
    end
  end.
