Require Import RuntimeDefinitions.
From Coq Require Import Bool.Bool.
From Coq Require Import Init.Nat.

(* Enclave ID Equality *)
Definition equal_enclave_IDs (e0 : enclave_ID) (e1 : enclave_ID): bool :=
  match e0, e1 with
  | enclave_ID_active e0_val, enclave_ID_active e1_val => eqb e0_val e1_val
  | enclave_ID_inactive, enclave_ID_inactive => true
  | _, _ => false
  end.
Definition equal_enclave_IDs_prop (e0 : enclave_ID) (e1 : enclave_ID): Prop :=
  match e0, e1 with
  | enclave_ID_active e0_val, enclave_ID_active e1_val => eq e0_val e1_val
  | enclave_ID_inactive, enclave_ID_inactive => True
  | _, _ => False
  end.


(* Contains Way ID *)
Fixpoint recursive_contains_way_ID (w : way_ID) (T : PLRU_tree): bool :=
  match T with
  | subtree sigma e T1 T2 => (recursive_contains_way_ID w T1) || (recursive_contains_way_ID w T2)
  | subtree_leaf L => 
    match L with
    | leaf w' e => eqb w w'
    end
  end.
Definition contains_way_ID (w: way_ID) (T: PLRU_tree): bool := recursive_contains_way_ID w T.

(* Contains Way ID (Prop) *)
Fixpoint recursive_contains_way_ID_prop (w : way_ID) (T : PLRU_tree): Prop :=
  match T with
  | subtree sigma e T1 T2 => (recursive_contains_way_ID_prop w T1) \/ (recursive_contains_way_ID_prop w T2)
  | subtree_leaf L => 
    match L with
    | leaf w' e => eq w w'
    end
  end.
Definition contains_way_ID_prop (w: way_ID) (T: PLRU_tree): Prop := recursive_contains_way_ID_prop w T.



(* Common Enclave *)
Definition common_enclave (T1 : PLRU_tree) (T2 : PLRU_tree): enclave_ID :=
  match T1, T2 with
  | subtree _ e _ _, subtree _ e' _ _ =>
    if equal_enclave_IDs e e'
    then e
    else enclave_ID_inactive
  | _, _ => enclave_ID_inactive
  end.


(* Update *)
Fixpoint recursive_update (T : PLRU_tree) (w : way_ID) (e: enclave_ID): PLRU_tree :=
  match T with
  | subtree select_bit e0 T1 T2 =>
    if equal_enclave_IDs e e0
    then
      if (contains_way_ID w T1) 
      then subtree LMRU e (recursive_update T1 w e) T2
      else
        if (contains_way_ID w T2)
        then subtree RMRU e T1 (recursive_update T2 w e)
        else subtree select_bit e T1 T2
    else subtree select_bit (common_enclave T1 T2) (recursive_update T1 w e) (recursive_update T2 w e)
  | subtree_leaf L =>
    match L with
    | leaf w' e' =>
      match e' with
      | enclave_ID_inactive =>
        if (eqb w w')
        then subtree_leaf (leaf w e)
        else subtree_leaf L
      | enclave_ID_active _ => subtree_leaf L
      end
    end
  end.
Definition update (T: PLRU_tree) (w: way_ID) (e: enclave_ID): PLRU_tree := recursive_update T w e.


(* Contains Enclave *)
Fixpoint contains_enclave (e: enclave_ID) (T: PLRU_tree): bool :=
  match T with
  | subtree _ e0 T1 T2 => (equal_enclave_IDs e e0) || (contains_enclave e T1) || (contains_enclave e T1)
  | subtree_leaf L =>
    match L with
    | leaf _ e0 => equal_enclave_IDs e e0
    end
  end.
Fixpoint contains_enclave_prop (e: enclave_ID) (T: PLRU_tree): Prop :=
  match T with
  | subtree _ e0 T1 T2 => (equal_enclave_IDs_prop e e0) \/ (contains_enclave_prop e T1) \/ (contains_enclave_prop e T1)
  | subtree_leaf L =>
    match L with
    | leaf _ e0 => equal_enclave_IDs_prop e e0
    end
  end.


(* Replace *)
Fixpoint recursive_replace (T: PLRU_tree) (e: enclave_ID): option way_ID :=
  match T with
  | subtree select_bit e0 T1 T2 =>
    match (equal_enclave_IDs e e0) with
    | true =>
      match select_bit with
      | LMRU => recursive_replace T2 e
      | RMRU => recursive_replace T1 e
      end
    | false =>
      match contains_enclave e T1 with
      | true => recursive_replace T1 e
      | false =>
        match contains_enclave e T2 with
        | true => recursive_replace T2 e
        | false => None
        end
      end
    end
  | subtree_leaf L =>
    match L with
    | leaf w e0 =>
      match (equal_enclave_IDs e e0) with
      | true => Some w
      | false => None
      end
    end
  end.
Definition replace (T: PLRU_tree) (e: enclave_ID): option way_ID := recursive_replace T e.