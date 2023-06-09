From Coq Require Import Lists.List.
From Coq Require Import Init.Nat.
From Coq Require Import Program.Wf.
Require Import AppendixC.
Require Import RuntimeDefinitions.

(* Appendix A, Appendix B, Fig 6, and Fig 7 *)

(* Cache Hierarchy Tree *)
(* Mapping between root, cache, or core -> path to root *)
Inductive cache_tree_node : Type :=
| root_node : cache_tree_node
| core_node : core_ID -> cache_tree_node
| cache_node : physical_cache_unit_ID -> cache_tree_node.
Definition cache_hierarchy_tree : Type := list (cache_tree_node * (list physical_cache_unit_ID)).

Fixpoint recursive_get_cache_list_root (c: cache_tree_node) (h_tree: cache_hierarchy_tree): option (list physical_cache_unit_ID) :=
  match h_tree with
  | nil => None
  | (node, l) :: h_tree' =>
    match node with
    | root_node => Some l
    | _ => recursive_get_cache_list_root c h_tree'
    end
  end.
Fixpoint recursive_get_cache_list_cache (c: cache_tree_node) (h_tree: cache_hierarchy_tree): option (list physical_cache_unit_ID) :=
  match h_tree with
  | nil => None
  | (node, l) :: h_tree' =>
    match node with
    | cache_node m =>
      match c with
      | cache_node v =>
        match (eqb v m) with
        | true => Some l
        | false => recursive_get_cache_list_cache c h_tree'
        end
      | _ => None
      end
    | _ => recursive_get_cache_list_cache c h_tree'
    end
  end.
Fixpoint recursive_get_cache_list_core (c: cache_tree_node) (h_tree: cache_hierarchy_tree): option (list physical_cache_unit_ID) :=
  match h_tree with
  | nil => None
  | (node, l) :: h_tree' =>
    match node with
    | core_node m =>
      match c with
      | core_node v =>
        match (eqb v m) with
        | true => Some l
        | false => recursive_get_cache_list_core c h_tree'
        end
      | _ => None
      end
    | _ => recursive_get_cache_list_core c h_tree'
    end
  end.
Definition get_cache_ID_path (c: cache_tree_node) (h_tree: cache_hierarchy_tree): option (list physical_cache_unit_ID) :=
  match c with
  | root_node => recursive_get_cache_list_root c h_tree
  | core_node _ => None
  | cache_node _ => recursive_get_cache_list_cache c h_tree
  end.

(* Well-Defined H-Tree *)
Definition well_defined_cache_tree (h_tree : cache_hierarchy_tree): Prop :=
  get_cache_ID_path root_node h_tree = Some nil /\
  (forall c a l, get_cache_ID_path (cache_node c) h_tree = Some (a :: l) -> a :: l = c :: l) /\
  (forall q a l, get_cache_ID_path (core_node q) h_tree = Some (a :: l) ->
    get_cache_ID_path (cache_node a) h_tree = Some (a :: l)) /\
  (forall c a l, get_cache_ID_path (cache_node c) h_tree = Some (c :: a :: l) ->
    get_cache_ID_path (cache_node a) h_tree = Some (a :: l)).

(* MLC Deallocation *)
Fixpoint recursive_mlc_deallocation (e: raw_enclave_ID) (k: multi_level_cache) (L: list physical_cache_unit_ID) {struct L}: option multi_level_cache :=
  match L with
  | nil => Some k
  | lambda :: L' =>
    match (NatMap.find lambda k) with
    | None => None
    | Some old_psi =>
      match cachelet_deallocation e old_psi with
      | None => None
      | Some psi => recursive_mlc_deallocation e (NatMap.add lambda psi k) L'
      end
    end
  end.
Definition mlc_deallocation (e: raw_enclave_ID) (k: multi_level_cache) (lambda: cache_tree_node) (h_tree: cache_hierarchy_tree): option multi_level_cache :=
  match (get_cache_ID_path lambda h_tree) with
  | Some L =>
    match L with
    | nil => None
    | _ => recursive_mlc_deallocation e k L
    end
  | None => None
  end.

(* MLC Write *)
Inductive mlc_write_value : Type :=
| mlc_write_valid: data_block -> observation_trace -> memory -> multi_level_cache -> mlc_write_value
| mlc_write_error: mlc_write_value.
Fixpoint recursive_mlc_write (k: multi_level_cache) (state: enclave_state) (mu: memory) (l: memory_address) (v: memory_value) (L: list physical_cache_unit_ID) {struct L}: mlc_write_value :=
  match L with
  | nil =>
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
  | lambda :: L' =>
    match (NatMap.find lambda k) with
    | None => mlc_write_error
    | Some original_psi =>
      match (cc_hit_write original_psi state l v) with
      | cc_hit_write_valid D c psi =>
        match l with
        | address b delta => mlc_write_valid D ((observation_tuple hit_write c lambda) :: nil) mu (NatMap.add lambda psi k)
        end
      | cc_hit_write_error =>
        match (recursive_mlc_write k state mu l v L') with
        | mlc_write_error => mlc_write_error
        | mlc_write_valid D Obs mu' k' =>
          match (cc_update original_psi state D l) with
          | cc_update_error => mlc_write_error
          | cc_update_valid c psi' => mlc_write_valid D (Obs ++ ((observation_tuple miss c lambda) :: nil)) mu' (NatMap.add lambda psi' k')
          end
        end
      end
    end
  end.
Definition mlc_write (k: multi_level_cache) (state: enclave_state) (mu: memory) (l: memory_address) (v: memory_value) (lambda: cache_tree_node) (h_tree: cache_hierarchy_tree): mlc_write_value :=
  match (get_cache_ID_path lambda h_tree) with
  | Some L => recursive_mlc_write k state mu l v L
  | None => mlc_write_error
  end.

(* MLC Allocation *)
Fixpoint recursive_mlc_allocation (n: (list nat)) (e: raw_enclave_ID) (k: multi_level_cache) (L: list physical_cache_unit_ID) {struct L}: option multi_level_cache :=
  match L with
  | nil => Some k
  | lambda :: L' =>
    match n with
    | nil => None
    | n_val :: n' =>
      match (NatMap.find lambda k) with
      | None => None
      | Some current_psi =>
        match (cachelet_allocation n_val e current_psi) with
        | None => None
        | Some psi => recursive_mlc_allocation n' e (NatMap.add lambda psi k) L'
        end
      end
    end
  end.
Definition mlc_allocation (n: (list nat)) (e: raw_enclave_ID) (k: multi_level_cache) (lambda: cache_tree_node) (h_tree: cache_hierarchy_tree): option multi_level_cache :=
  match (get_cache_ID_path lambda h_tree) with
  | Some L =>
    match L with
    | nil => None
    | _ => recursive_mlc_allocation n e k L
    end
  | None => None
  end.

(* MLC Read *)
Inductive mlc_read_value : Type :=
| mlc_read_valid: data_block -> data_offset -> observation_trace -> multi_level_cache -> mlc_read_value
| mlc_read_error: mlc_read_value.
Fixpoint recursive_mlc_read (k: multi_level_cache) (state: enclave_state) (mu: memory) (l: memory_address) (L: list physical_cache_unit_ID) {struct L}: mlc_read_value :=
  match L with
  | nil =>
    match l with
    | address b delta =>
      match (NatMap.find b mu) with
      | None => mlc_read_error
      | Some D => mlc_read_valid D delta nil k
      end
    end
  | lambda :: L' =>
    match (NatMap.find lambda k) with
    | None => mlc_read_error
    | Some original_psi =>
      match (cc_hit_read original_psi state l) with
      | cc_hit_read_valid D delta c psi => mlc_read_valid D delta ((observation_tuple hit_read c lambda) :: nil) (NatMap.add lambda psi k)
      | cc_hit_read_error =>
        match (recursive_mlc_read k state mu l L') with
        | mlc_read_error => mlc_read_error
        | mlc_read_valid D delta Obs k' =>
          match (cc_update original_psi state D l) with
          | cc_update_error => mlc_read_error
          | cc_update_valid c psi' => mlc_read_valid D delta (Obs ++ ((observation_tuple miss c lambda) :: nil)) (NatMap.add lambda psi' k')
          end
        end
      end
    end
  end.
Definition mlc_read (k: multi_level_cache) (state: enclave_state) (mu: memory) (l: memory_address) (lambda: cache_tree_node) (h_tree: cache_hierarchy_tree): mlc_read_value :=
  match (get_cache_ID_path lambda h_tree) with
  | Some L => recursive_mlc_read k state mu l L
  | None => mlc_read_error
  end.
