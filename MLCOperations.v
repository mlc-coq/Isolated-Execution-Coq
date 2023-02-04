From Coq Require Import Lists.List.
From Coq Require Import Init.Nat.
Require Import AppendixC.
Require Import RuntimeDefinitions.

(* Appendix A, Appendix B, Fig 6, and Fig 7 *)

(* Placeholder Cache Hierarchy Tree *)
Inductive cache_hierarchy_tree : Type :=
| ch_tree: physical_cache_unit_ID -> (list cache_hierarchy_tree) -> cache_hierarchy_tree
| ch_leaf: core_ID -> cache_hierarchy_tree.
Inductive cache_hierarchy_value : Type :=
| cache_node: physical_cache_unit_ID -> cache_hierarchy_value
| core_node: core_ID -> cache_hierarchy_value.
Inductive cache_unit_ID_parent : Type :=
| cache_parent: physical_cache_unit_ID -> cache_unit_ID_parent
| cache_root: cache_unit_ID_parent.

(* Check if val is in heirarchy tree/subtree *)
Fixpoint tree_contains_core_ID (height: nat) (val: core_ID) (heir_tree: cache_hierarchy_tree): bool :=
  match height with
  | 0 => false
  | S n =>
    match heir_tree with
    | ch_tree _ l => fold_left orb (map (tree_contains_core_ID n val) l) false
    | ch_leaf c => eqb val c
    end
  end.
Fixpoint tree_contains_cache_ID (height: nat) (val: physical_cache_unit_ID) (heir_tree: cache_hierarchy_tree): bool :=
  match height with
  | 0 => false
  | S n =>
    match heir_tree with
    | ch_tree p l => fold_left orb (map (tree_contains_cache_ID n val) l) (eqb p val)
    | ch_leaf _ => false
    end
  end.

(* Return subtree with val *)
Fixpoint get_child_with_core_ID (height: nat) (val: core_ID) (l: (list cache_hierarchy_tree)): option cache_hierarchy_tree :=
  match l with
  | nil => None
  | hier_subtree :: l' =>
    match (tree_contains_core_ID height val hier_subtree) with
    | true => Some hier_subtree
    | false => get_child_with_core_ID height val l'
    end
  end.
Fixpoint get_child_with_cache_ID (height: nat) (val: physical_cache_unit_ID) (l: (list cache_hierarchy_tree)): option cache_hierarchy_tree :=
  match l with
  | nil => None
  | hier_subtree :: l' =>
    match (tree_contains_cache_ID height val hier_subtree) with
    | true => Some hier_subtree
    | false => get_child_with_cache_ID height val l'
    end
  end.

(* Get tree height (in number of nodes, which is typical height + 1) *)
Fixpoint get_hierarchy_tree_height (hierarchy_tree: cache_hierarchy_tree): nat :=
  match hierarchy_tree with
  | ch_leaf _ => S 0
  | ch_tree _ l =>
    match l with
    | nil => 0
    | hier_subtree :: _ => S (get_hierarchy_tree_height hier_subtree)
    end
  end.

(* Get parent in cache tree *)
Fixpoint get_cache_parent_core_ID (parent: cache_unit_ID_parent) (height: nat) (val: core_ID) (hierarchy_tree: cache_hierarchy_tree): option cache_unit_ID_parent :=
  match height with
  | 0 => None
  | S n =>
    match hierarchy_tree with
    | ch_leaf c =>
      match (eqb c val) with
      | true => Some parent
      | false => None
      end
    | ch_tree p l =>
      match (get_child_with_core_ID height val l) with
      | None => None
      | Some hier_subtree => get_cache_parent_core_ID (cache_parent p) n val hier_subtree
      end
    end
  end.
Fixpoint get_cache_parent_cache_ID (parent: cache_unit_ID_parent) (height: nat) (val: physical_cache_unit_ID) (hierarchy_tree: cache_hierarchy_tree): option cache_unit_ID_parent :=
  match height with
  | 0 => None
  | S n =>
    match hierarchy_tree with
    | ch_leaf _ => None
    | ch_tree p l =>
      match (eqb p val) with
      | true => Some parent
      | false =>
        match (get_child_with_core_ID height val l) with
        | None => None
        | Some hier_subtree => get_cache_parent_cache_ID (cache_parent p) n val hier_subtree
        end
      end
    end
  end.
Definition get_cache_hierarchy_parent (val: cache_hierarchy_value) (hierarchy_tree: cache_hierarchy_tree): option cache_unit_ID_parent :=
  match val with
  | cache_node x =>
    match (tree_contains_cache_ID (get_hierarchy_tree_height hierarchy_tree) x hierarchy_tree) with
    | true => get_cache_parent_cache_ID cache_root (get_hierarchy_tree_height hierarchy_tree) x hierarchy_tree
    | false => None
    end
  | core_node x =>
    match (tree_contains_core_ID (get_hierarchy_tree_height hierarchy_tree) x hierarchy_tree) with
    | true => get_cache_parent_core_ID cache_root (get_hierarchy_tree_height hierarchy_tree) x hierarchy_tree
    | false => None
    end
  end.

(* Well Formed Cache Hierarchy Tree *)
Fixpoint recursive_uniform_depth (height: nat) (h_tree: cache_hierarchy_tree): bool :=
  match height with
  | 0 => false
  | S 0 =>
    match h_tree with
    | ch_tree _ l => false
    | ch_leaf _ => true
    end
  | S n =>
    match h_tree with
    | ch_tree _ l =>
      match l with
      | nil => false
      | l' => fold_left andb (map (recursive_uniform_depth n) l') true
      end
    | ch_leaf _ => false
    end
  end.
Definition uniform_depth (h_tree: cache_hierarchy_tree): bool :=
  match (get_hierarchy_tree_height h_tree) with
  | n => recursive_uniform_depth n h_tree
  end.
(* Probably want to use a better definition, but will try this for now *)
Definition well_formed_tree (h_tree: cache_hierarchy_tree): Prop := (uniform_depth h_tree = true).


(* MLC Deallocation *)
Fixpoint recursive_mlc_deallocation (e: raw_enclave_ID) (k: multi_level_cache) (lambda: physical_cache_unit_ID) (h_tree: cache_hierarchy_tree) (max_calls: nat): option multi_level_cache :=
  match max_calls with
  | 0 => None
  | S n =>
    match (NatMap.find lambda k) with
    | None => None
    | Some old_psi =>
      match cachelet_deallocation e old_psi with
      | None => None
      | Some psi =>
        match (get_cache_hierarchy_parent (cache_node lambda) h_tree) with
        | None => None
        | Some H =>
          match H with
          | cache_root => None
          | cache_parent x =>
            match (recursive_mlc_deallocation e (NatMap.add lambda psi k) x h_tree n) with
            | None => None
            | Some k'' => Some k''
            end
          end
        end
      end
    end
  end.
Definition mlc_deallocation (state: enclave_state) (k: multi_level_cache) (lambda: physical_cache_unit_ID) (h_tree: cache_hierarchy_tree): option multi_level_cache :=
  match state with
  | enclave_state_value e_id _ =>
    match e_id with
    | enclave_ID_inactive => None
    | enclave_ID_active e => recursive_mlc_deallocation e k lambda h_tree (get_hierarchy_tree_height h_tree)
    end
  end.

(* MLC Write *)
Inductive mlc_write_value : Type :=
| mlc_write_valid: data_block -> observation_trace -> memory -> multi_level_cache -> mlc_write_value
| mlc_write_error: mlc_write_value.
Fixpoint recursive_mlc_write (k: multi_level_cache) (lambda: cache_unit_ID_parent) (state: enclave_state) (mu: memory) (l: memory_address) (v: memory_value) (h_tree: cache_hierarchy_tree) (max_calls: nat): mlc_write_value :=
  match max_calls with
  | 0 => mlc_write_error
  | S n =>
    match lambda with
    | cache_root =>
      match l with
      | address b delta =>
        match (NatMap.find b mu) with
        | None => mlc_write_error
        | Some D' =>
          match v with
          | memory_value_instruction _ => mlc_write_error
          | memory_value_data d => mlc_write_valid (NatMap.add delta (memory_value_data d) D') nil (NatMap.add b (NatMap.add delta (memory_value_data d) D') mu) k
          end
        end
      end
    | cache_parent lambda_value =>
      match (NatMap.find lambda_value k) with
      | None => mlc_write_error
      | Some original_psi =>
        match (cc_hit_write original_psi state l v) with
        | cc_hit_write_valid D c psi =>
          match l with
          | address b delta => mlc_write_valid D ((observation_tuple hit_write c lambda_value) :: nil) mu (NatMap.add lambda_value psi k)
          end
        | cc_hit_write_error =>
          match (get_cache_hierarchy_parent (cache_node lambda_value) h_tree) with
          | None => mlc_write_error
          | Some H =>
            match (recursive_mlc_write k H state mu l v h_tree n) with
            | mlc_write_error => mlc_write_error
            | mlc_write_valid D Obs mu' k' =>
              match (cc_update original_psi state D l) with
              | cc_update_error => mlc_write_error
              | cc_update_valid c psi' => mlc_write_valid D (Obs ++ ((observation_tuple miss c lambda_value) :: nil)) mu' (NatMap.add lambda_value psi' k')
              end
            end
          end
        end
      end
    end
  end.
Definition mlc_write (k: multi_level_cache) (lambda: cache_unit_ID_parent) (state: enclave_state) (mu: memory) (l: memory_address) (v: memory_value) (h_tree: cache_hierarchy_tree): mlc_write_value :=
  recursive_mlc_write k lambda state mu l v h_tree (get_hierarchy_tree_height h_tree).

(* MLC Allocation *)
Fixpoint recursive_mlc_allocation (n: (list nat)) (e: raw_enclave_ID) (k: multi_level_cache) (lambda: physical_cache_unit_ID) (h_tree: cache_hierarchy_tree): option multi_level_cache :=
  match n with
  | nil => Some k
  | n_val :: n' =>
    match (NatMap.find lambda k) with
    | None => None
    | Some current_psi =>
      match (cachelet_allocation n_val e current_psi) with
      | None => None
      | Some psi =>
        match (get_cache_hierarchy_parent (cache_node lambda) h_tree) with
        | None => None
        | Some H =>
          match H with
          | cache_root => None
          | cache_parent x => recursive_mlc_allocation n' e (NatMap.add lambda psi k) x h_tree
          end
        end
      end
    end
  end.
Definition rec_alloc_optional_add (lambda : physical_cache_unit_ID) (psi : single_level_cache_unit) (k : option multi_level_cache) : option multi_level_cache :=
  match k with
  | None => None
  | Some k' => Some (NatMap.add lambda psi k')
  end.
Fixpoint rmlca (n: (list nat)) (e: raw_enclave_ID) (k_opt: option multi_level_cache) (lambda: physical_cache_unit_ID) (h_tree: cache_hierarchy_tree): option multi_level_cache :=
  match n with
  | nil => k_opt
  | n_val :: n' =>
    match k_opt with
    | None => None
    | Some k =>
      match (NatMap.find lambda k) with
      | None => None
      | Some current_psi =>
        match (cachelet_allocation n_val e current_psi) with
        | None => None
        | Some psi =>
          match (get_cache_hierarchy_parent (cache_node lambda) h_tree) with
          | None => None
          | Some H =>
            match H with
            | cache_root => None
            | cache_parent x => rec_alloc_optional_add lambda psi (rmlca n' e (Some k) x h_tree)
            end
          end
        end
      end
    end
  end.
Definition mlc_allocation (n: (list nat)) (state: enclave_state) (k: multi_level_cache) (lambda: physical_cache_unit_ID) (h_tree: cache_hierarchy_tree): option multi_level_cache :=
  match state with
  | enclave_state_value e_id _ =>
    match e_id with
    | enclave_ID_inactive => None
    | enclave_ID_active e => (* rmlca n e (Some k) lambda h_tree *) recursive_mlc_allocation n e k lambda h_tree
    end
  end.

(* MLC Read *)
Inductive mlc_read_value : Type :=
| mlc_read_valid: data_block -> data_offset -> observation_trace -> multi_level_cache -> mlc_read_value
| mlc_read_error: mlc_read_value.
Fixpoint recursive_mlc_read (k: multi_level_cache) (lambda: cache_unit_ID_parent) (state: enclave_state) (mu: memory) (l: memory_address) (h_tree: cache_hierarchy_tree) (max_calls: nat): mlc_read_value :=
  match max_calls with
  | 0 => mlc_read_error
  | S n =>
    match lambda with
    | cache_root =>
      match l with
      | address b delta =>
        match (NatMap.find b mu) with
        | None => mlc_read_error
        | Some D => mlc_read_valid D delta nil k
        end
      end
    | cache_parent lambda_value =>
      match (NatMap.find lambda_value k) with
      | None => mlc_read_error
      | Some original_psi =>
        match (cc_hit_read original_psi state l) with
        | cc_hit_read_valid D delta c psi => mlc_read_valid D delta ((observation_tuple hit_read c lambda_value) :: nil) (NatMap.add lambda_value psi k)
        | cc_hit_read_error =>
          match (get_cache_hierarchy_parent (cache_node lambda_value) h_tree) with
          | None => mlc_read_error
          | Some H =>
            match (recursive_mlc_read k H state mu l h_tree n) with
            | mlc_read_error => mlc_read_error
            | mlc_read_valid D delta Obs k' =>
              match (cc_update original_psi state D l) with
              | cc_update_error => mlc_read_error
              | cc_update_valid c psi' => mlc_read_valid D delta (Obs ++ ((observation_tuple miss c lambda_value) :: nil)) (NatMap.add lambda_value psi' k')
              end
            end
          end
        end
      end
    end
  end.
Definition mlc_read (k: multi_level_cache) (lambda: cache_unit_ID_parent) (state: enclave_state) (mu: memory) (l: memory_address) (h_tree: cache_hierarchy_tree): mlc_read_value :=
  recursive_mlc_read k lambda state mu l h_tree (get_hierarchy_tree_height h_tree).

