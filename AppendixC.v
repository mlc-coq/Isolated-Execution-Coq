From Coq Require Import Lists.List.
From Coq Require Import Init.Nat.
From Coq Require Import Numbers.NatInt.NZDiv.
From Coq Require Import Numbers.NatInt.NZLog.
From Coq Require Import Numbers.NatInt.NZBits.
Require Import RuntimeDefinitions.
Require Import AppendixD.
Require Import AppendixF.

Definition lt_way_ID (c1: nullable_cachelet_index) (c2: nullable_cachelet_index) : nullable_cachelet_index :=
  match c1, c2 with
  | cachelet_index_defined v1, cachelet_index_defined v2 =>
    match v1, v2 with
    | (w1, _), (w2, _) =>
      if ltb w1 w2 then c1 else c2
    end
  | _, cachelet_index_none => c1
  | _, _ => c2
  end.

(* Way First Allocation *)
Fixpoint cachelet_min_way_ID (min: nullable_cachelet_index) (l: list cachelet_index): nullable_cachelet_index :=
  match l with
  | nil => min
  | a :: l' => cachelet_min_way_ID (lt_way_ID min (cachelet_index_defined a)) l'
  end.
Fixpoint contains_cachelet_index (c: cachelet_index) (F: CAT): bool :=
  match F with
  | nil => false
  | x :: F' =>
    match (eq_cachelet_index x c) with
    | true => true
    | false => contains_cachelet_index c F'
    end
  end.
Definition way_first_allocation (F: CAT): nullable_cachelet_index :=
  match (cachelet_min_way_ID cachelet_index_none F) with
  | cachelet_index_none => cachelet_index_none
  | (cachelet_index_defined c) =>
    match (contains_cachelet_index c F) with
    | true => (cachelet_index_defined c)
    | false => cachelet_index_none
    end
  end.

(* Cachelet Invalidation*)
Definition cachelet_invalidation (C: way_set_cache) (ci: cachelet_index): option way_set_cache :=
  match (CacheletMap.find ci C) with
  | Some (valid_bit_tag_and_data _ c d) => Some (CacheletMap.add ci (valid_bit_tag_and_data dirty_bit c d) C)
  | None => None
  end.

(* Beta Function *)
Inductive set_and_tag : Type :=
  | set_and_tag_values: set_ID -> cache_tag_value -> set_and_tag.
Definition block_to_set_and_tag (val: block_ID) (sets: set_indexed_PLRU) : set_and_tag :=
  set_and_tag_values (val mod (length (NatMapProperties.to_list sets))) (shiftr val (log2 (length (NatMapProperties.to_list sets)))).


(* Find Way ID *)
Fixpoint find_way_ID_in_mask (t: cache_tag_value) (s: set_ID) (L: remapping_list) (C: way_set_cache): option way_ID :=
  match L with
  | nil => None
  | (w', s') :: L' =>
    match s =? s' with
    | false => find_way_ID_in_mask t s L' C
    | true =>
      match (CacheletMap.find (w', s) C) with
      | None => find_way_ID_in_mask t s L' C
      | Some cache_value =>
        match cache_value with
        | valid_bit_tag_and_data vb t' D =>
          match t =? t' with
          | true => Some w'
          | false => find_way_ID_in_mask t s L' C
          end
        end
      end
    end
  end.
Definition find_way_ID_with_cache_tag (state: enclave_state) (s: set_ID) (t: cache_tag_value) (V: VPT) (C: way_set_cache): option way_ID :=
  match state with
  | enclave_state_value e_id _ =>
    match e_id with
    | enclave_ID_inactive => None
    | enclave_ID_active e =>
      match (NatMap.find e V) with
      | None => None
      | Some L => find_way_ID_in_mask t s L C
      end
    end
  end.


(* CC 'Unfold' Function(s) *)
Inductive validatable_cc_unfold : Type :=
| cc_unfold_valid: CAT -> VPT -> way_set_cache -> set_indexed_PLRU -> cachelet_index -> way_set_cache_value -> data_offset -> validatable_cc_unfold
| cc_unfold_error: validatable_cc_unfold.
Definition cc_unfold (psi: single_level_cache_unit) (state: enclave_state) (l: memory_address): validatable_cc_unfold :=
  match psi with
  | single_level_cache F V C R =>
    match l with
    | address b delta =>
      match (block_to_set_and_tag b R) with
      | set_and_tag_values s t =>
        match (find_way_ID_with_cache_tag state s t V C) with
        | None => cc_unfold_error
        | Some w =>
          match (CacheletMap.find (w, s) C) with
          | None => cc_unfold_error
          | Some cache_val => cc_unfold_valid F V C R (w, s) cache_val delta
          end
        end
      end
    end
  end.


(* CC Hit Read *)
Inductive validatable_cc_hit_read : Type :=
  | cc_hit_read_valid: data_block -> data_offset -> cachelet_index -> single_level_cache_unit -> validatable_cc_hit_read
  | cc_hit_read_error: validatable_cc_hit_read.
Definition cc_hit_read (psi: single_level_cache_unit) (state: enclave_state) (l: memory_address): validatable_cc_hit_read :=
  match (cc_unfold psi state l) with
  | cc_unfold_error => cc_hit_read_error
  | cc_unfold_valid F V C R (w, s) cache_val delta =>
    match cache_val with
    | valid_bit_tag_and_data _ _ D => 
      match (NatMap.find s R) with
      | None => cc_hit_read_error
      | Some T' => 
        match state with
        | enclave_state_value e _ => cc_hit_read_valid D delta (w, s) (single_level_cache F V C (NatMap.add s (update T' w e) R))
        end
      end
    end
  end.


(* CC Hit Write *)
Inductive validatable_cc_hit_write : Type :=
  | cc_hit_write_valid: data_block -> cachelet_index -> single_level_cache_unit -> validatable_cc_hit_write
  | cc_hit_write_error: validatable_cc_hit_write.
Definition cc_hit_write (psi: single_level_cache_unit) (state: enclave_state) (l: memory_address) (v: memory_value): validatable_cc_hit_write :=
  match (cc_unfold psi state l) with
  | cc_unfold_error => cc_hit_write_error
  | cc_unfold_valid F V C R (w, s) cache_val delta =>
    match cache_val with
    | valid_bit_tag_and_data _ t D =>
      match (NatMap.find s R) with
      | None => cc_hit_write_error
      | Some T' => 
        match v with
        | memory_value_instruction _ => cc_hit_write_error
        | memory_value_data n =>
          match state with
          | enclave_state_value e _ => cc_hit_write_valid D (w, s) (single_level_cache F V (CacheletMap.add (w, s) (valid_bit_tag_and_data dirty_bit t (NatMap.add delta (memory_value_data n) D)) C) (NatMap.add s (update T' w e) R))
          end
        end
      end
    end
  end.


(* CC Update *)
Inductive validatable_cc_update : Type :=
  | cc_update_valid: cachelet_index -> single_level_cache_unit -> validatable_cc_update
  | cc_update_error: validatable_cc_update.
Definition cc_update (psi: single_level_cache_unit) (state: enclave_state) (D: data_block) (l: memory_address): validatable_cc_update :=
  match (cc_unfold psi state l) with
  | cc_unfold_error => cc_update_error
  | cc_unfold_valid F V C R (w, s) cache_val _ =>
    match cache_val with
    | valid_bit_tag_and_data _ t _ =>
      match state with
      | enclave_state_value e _ =>
        match (NatMap.find s R) with
        | None => cc_update_error
        | Some T' =>
          match (replace T' e) with
          | None => cc_update_error
          | Some w' => cc_update_valid (w, s) (single_level_cache F V (CacheletMap.add (w, s) (valid_bit_tag_and_data valid_bit t D) C) (NatMap.add s (update T' w e) R))
          end
        end
      end
    end
  end.


(* Cachelet Allocation *)
Fixpoint recursive_cachelet_allocation (n: nat) (e: raw_enclave_ID) (F: CAT) (V: VPT) (C: way_set_cache) (R: set_indexed_PLRU): option single_level_cache_unit :=
  match n with
  | 0 => Some (single_level_cache F V C R)
  | S n' =>
    match way_first_allocation F with
    | cachelet_index_none => None
    | cachelet_index_defined (w, s) =>
      match (NatMap.find s R) with
      | None => None
      | Some T' =>
        match (remove_CAT (w, s) F) with
        | None => None
        | Some remF =>
          match (NatMap.find e V) with
          | None => recursive_cachelet_allocation n' e remF (NatMap.add e ((w, s) :: nil) V) C (NatMap.add s (update T' w (enclave_ID_active e)) R)
          | Some L => recursive_cachelet_allocation n' e remF (NatMap.add e ((w, s) :: L) V) C (NatMap.add s (update T' w (enclave_ID_active e)) R)
          end
        end
      end
    end
  end.
Definition cachelet_allocation (n: nat) (e: raw_enclave_ID) (psi: single_level_cache_unit): option single_level_cache_unit := 
  match n with
  | 0 => None
  | S _ =>
    match psi with
    | single_level_cache F V C R => recursive_cachelet_allocation n e F V C R
    end
  end.


(* Cachelet Deallocation *)
Fixpoint clear_remapping_list (e: raw_enclave_ID) (L: remapping_list) (F: CAT) (V: VPT) (C: way_set_cache) (R: set_indexed_PLRU): option single_level_cache_unit :=
  match L with
  | nil => Some (single_level_cache F (NatMap.remove e V) C R)
  | (w, s) :: L' =>
    match (NatMap.find s R) with
    | None => None
    | Some T' =>
      match (cachelet_invalidation C (w, s)) with
      | None => None
      | Some C_inv => (clear_remapping_list e L' ((w, s) :: F) (NatMap.add e L' V) C_inv (NatMap.add s (update T' w (enclave_ID_active e)) R))
      end
    end
  end.
Definition cachelet_deallocation (e: raw_enclave_ID) (psi: single_level_cache_unit): option single_level_cache_unit :=
  match psi with
  | single_level_cache F V C R =>
    match (NatMap.find e V) with
    | None => None
    | Some L => clear_remapping_list e L F V C R
    end
  end.
