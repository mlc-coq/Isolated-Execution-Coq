From Coq Require Import Lists.List.
From Coq Require Import FSets.FMapList.
From Coq Require Import FSets.FMapFacts.
From Coq Require Import Structures.OrderedTypeEx.
From Coq Require Import Init.Nat.
From Coq Require Import Bool.Bool.
From Coq Require Import Logic.Eqdep_dec.
From Coq Require Import Lia.
From Coq Require Import Arith.PeanoNat.
From Coq Require Import Arith.Arith.

Module Import NatMap := FMapList.Make(Nat_as_OT).
Module OrderedPair := PairOrderedType Nat_as_OT Nat_as_OT.
Module Import PairMap := FMapList.Make(OrderedPair).
Module Import CacheletMap := PairMap.
Module NatMapProperties := WProperties_fun Nat_as_OT NatMap.
Module PairMapProperties := WProperties_fun OrderedPair PairMap.
Module CacheletMapProperties := PairMapProperties.

Module NatMapFacts := NatMapProperties.F.
Module CacheletMapFacts := CacheletMapProperties.F.


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
Inductive validity_bit : Type :=
| valid_bit : validity_bit
| dirty_bit : validity_bit.
Definition cachelet_index := (way_ID * set_ID) % type.
Inductive nullable_cachelet_index : Type :=
| cachelet_index_defined : cachelet_index -> nullable_cachelet_index
| cachelet_index_none : nullable_cachelet_index.

Definition data_block := NatMap.t memory_value.
Definition remapping_list := list cachelet_index.
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
Lemma cmp_to_eq : forall x y, (x =? y) = true -> x = y.
Proof.
  intro x.
  induction x.
  intros y H.
  destruct y. reflexivity. simpl in *. congruence.
  intros y H. destruct y.
  simpl in *. congruence. f_equal ; auto.
Qed.
Lemma cmp_uneq_helper1 : forall n m : nat,
    n <> m -> S n <> S m.
Proof.
  unfold not; intros.
  apply H. injection H0. intro. assumption.
Qed.
Lemma cmp_uneq_helper2 : forall n m : nat,
    S n <> S m -> n <> m.
Proof.
  unfold not; intros.
  apply H. lia.
Qed.
Lemma cmp_to_uneq : forall x y, (x =? y) = false <-> x <> y.
Proof.
  induction x. split.
  simpl. destruct y. discriminate. discriminate.
  simpl. destruct y. intros. contradiction. intros. reflexivity.
  simpl. destruct y.
  split. intros. discriminate. intros. reflexivity.
  split. intros. apply IHx in H. apply cmp_uneq_helper1. exact H.
  intros. apply cmp_uneq_helper2 in H. apply IHx in H. exact H.
Qed.

Lemma eq_to_cmp : forall x, x = x -> (x =? x) = true.
Proof.
  intros x.
  induction x.
  simpl. reflexivity.
  simpl. intros. apply IHx. reflexivity.
Qed.

Lemma cmp_to_eq_and : forall x y z w, (x =? y) && (z =? w) = true -> x = y /\ z = w.
Proof.
  intros.
  apply andb_true_iff in H.
  destruct H.
  split.
  apply cmp_to_eq; exact H.
  apply cmp_to_eq; exact H0.
Qed.

Lemma cmp_to_uneq_and : forall x y z w, (x =? y) && (z =? w) = false -> x <> y \/ z <> w.
Proof.
  intros.
  apply andb_false_iff in H.
  destruct H.
  left. apply cmp_to_uneq in H. exact H.
  right. apply cmp_to_uneq in H. exact H.
Qed.


Lemma pair_equality : forall (x y z w : nat), (x, y) = (z, w) <-> x = z /\ y = w.
Proof.
  split; intros.
  injection H; intros; subst.
  split; reflexivity.
  destruct H; subst; reflexivity.
Qed.
Lemma pair_inequality : forall (x y z w: nat), (x, y) <> (z, w) <-> x <> z \/ y <> w.
Proof.
  intros x y z w. split.
  intros H. destruct (Nat.eq_dec x z) as [H1 | H1]; destruct (Nat.eq_dec y w) as [H2 | H2].
  exfalso. apply H. rewrite H1, H2. reflexivity.
  right; exact H2.
  left; exact H1.
  left; exact H1.
  intros [H1 | H1] H.
  injection H; intros; subst.
  apply H1; reflexivity.
  injection H; intros; subst.
  apply H1; reflexivity.
Qed.
Lemma eq_dec_pair : forall (x y z w : nat), { (x, y) = (z, w) } + { (x, y) <> (z, w) }.
Proof.
  intros.
  assert ((x, y) <> (z, w) <-> x <> z \/ y <> w). apply pair_inequality.
  case_eq (Nat.eqb x z); case_eq (Nat.eqb y w); intros.
  apply cmp_to_eq in H0, H1; subst.
  left; reflexivity.
  apply cmp_to_uneq in H0.
  right. apply H. right; exact H0.
  apply cmp_to_uneq in H1.
  right. apply H. left; exact H1.
  apply cmp_to_uneq in H1.
  right. apply H. left; exact H1.
Qed.

Lemma eq_dec_cachelet : forall (n m : cachelet_index), {n = m} + {n <> m}.
Proof.
  intros.
  destruct n; destruct m.
  apply eq_dec_pair.
Qed.

Fixpoint in_bool (c: cachelet_index) (l: list cachelet_index) : bool :=
  match l with
  | nil => false
  | x :: l' =>
    match (eq_cachelet_index x c) with
    | true => true
    | false => in_bool c l'
    end
  end.

Lemma in_bool_iff : forall c l,
  (in_bool c l = true) <-> List.In c l.
Proof.
  split; intros.
  {
    induction l. unfold in_bool in H; discriminate.
    unfold List.In. unfold in_bool in H.
    case_eq (eq_cachelet_index a c); intros.
    assert (A0 := H0). destruct (eq_cachelet_index a c) in H, A0.
    destruct a; destruct c; unfold eq_cachelet_index in H0.
    apply cmp_to_eq_and in H0; destruct H0; subst w0 s0.
    left; reflexivity. discriminate.
    assert (A0 := H0). destruct (eq_cachelet_index a c) in H, A0.
    discriminate.
    apply IHl in H. right; exact H.
  }
  {
    induction l. unfold List.In in H; destruct H.
    unfold in_bool. unfold List.In in H. destruct H. subst.
    case_eq (eq_cachelet_index c c); intros. reflexivity.
    unfold eq_cachelet_index; destruct c; apply cmp_to_uneq_and in H.
    destruct H.
    assert (w = w). reflexivity. apply H in H0. destruct H0.
    assert (s = s). reflexivity. apply H in H0. destruct H0.
    case_eq (eq_cachelet_index a c); intros. reflexivity.
    apply IHl. exact H.
  }
Qed.

Definition remove_CAT (c: cachelet_index) (F: CAT): option CAT :=
  match (in_bool c F) with
  | true => Some (List.remove eq_dec_cachelet c F)
  | false => None
  end.

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
