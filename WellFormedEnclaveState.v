From Coq Require Import Lists.List.
From Coq Require Import Bool.Bool.
From Coq Require Import FSets.FMapList.
From Coq Require Import FSets.FMapFacts.
From Coq Require Import Init.Nat.
From Coq Require Import Structures.OrderedTypeEx.
Require Import RuntimeDefinitions.
Require Import AppendixD.
Require Import AppendixC.
Require Import AppendixF.
Require Import AppendixE.
Require Import Semantics.
Require Import MLCOperations.

Notation "'<<' sigma ';' obs '>>'" := (state_and_trace sigma obs).

(* Enclave Creation Functions *)
Lemma enclave_creation_mem : forall r mem mu n v0 v1 r0 mem0,
  enclave_creation (enclave_state_value r mem) mu n v0 v1 =
  enclave_state_valid (enclave_state_value r0 mem0) ->
  (forall e, n = e \/ NatMap.In e mem <-> NatMap.In e mem0).
Proof.
  intros.
  unfold enclave_creation in H.
  unfold add_new_enclave_to_enclave_state in H.
  destruct v0. destruct (NatMap.find b mu).
  destruct (is_all_zeroes mu b d (length (NatMapProperties.to_list d0)) v1).
  case_eq (NatMap.find n mem); intros;  assert (A0 := H0);
  destruct (NatMap.find n mem) in H, A0.
  discriminate. discriminate. discriminate. clear A0.
  injection H; intros; subst.
  split; intros. apply NatMapFacts.add_in_iff. exact H1.
  apply NatMapFacts.add_in_iff in H1. exact H1.
  discriminate. discriminate.
Qed.

Lemma enclave_creation_new : forall r mem mu n v0 v1 r0 mem0,
  enclave_creation (enclave_state_value r mem) mu n v0 v1 =
  enclave_state_valid (enclave_state_value r0 mem0) ->
  ~NatMap.In n mem.
Proof.
  intros.
  unfold enclave_creation in H.
  unfold add_new_enclave_to_enclave_state in H.
  destruct v0. destruct (NatMap.find b mu).
  destruct (is_all_zeroes mu b d (length (NatMapProperties.to_list d0)) v1).
  case_eq (NatMap.find n mem); intros;  assert (A0 := H0);
  destruct (NatMap.find n mem) in H, A0.
  discriminate. discriminate. discriminate. clear A0.
  injection H; intros; subst.
  intros contra. apply NatMapFacts.in_find_iff in contra.
  rewrite -> H0 in contra. destruct contra; reflexivity.
  discriminate. discriminate.
Qed.

Lemma enclave_creation_id : forall r mem mu n v0 v1 r0 mem0,
  enclave_creation (enclave_state_value r mem) mu n v0 v1 =
  enclave_state_valid (enclave_state_value r0 mem0) ->
  r = r0.
Proof.
  intros.
  unfold enclave_creation in H.
  destruct v0. destruct (NatMap.find b mu).
  destruct (is_all_zeroes mu b d (length (NatMapProperties.to_list d0)) v1).
  unfold add_new_enclave_to_enclave_state in H.
  destruct (NatMap.find n mem). discriminate.
  injection H; intros; subst. reflexivity.
  discriminate. discriminate.
Qed.

(* Enclave Elimination Functions *)
Lemma enclave_elimination_mem : forall r mem n r0 mem0,
  enclave_elimination (enclave_state_value r mem) n =
  enclave_state_valid (enclave_state_value r0 mem0) ->
  (forall e, NatMap.In e mem <-> NatMap.In e mem0 \/ n = e).
Proof.
  intros.
  unfold enclave_elimination in H.
  case_eq (NatMap.find n mem); intros.
  assert (A0 := H0); destruct (NatMap.find n mem) in H, A0.
  injection A0; intros; subst; clear A0.
  destruct r.
  case_eq (eqb n r); intros.
  assert (A0 := H1); destruct (eqb n r) in H, A0.
  discriminate. discriminate.
  assert (A0 := H1); destruct (eqb n r) in H, A0.
  discriminate.
  apply cmp_to_uneq in H1; clear A0.
  injection H; intros; subst.
  split; intros.
  case_eq (eqb n e); intros.
  apply cmp_to_eq in H3; right; exact H3.
  apply cmp_to_uneq in H3.
  left. apply NatMapFacts.remove_in_iff.
  split. exact H3. exact H2.
  destruct H2. apply NatMapFacts.remove_in_iff in H2.
  destruct H2. exact H3. subst.
  apply NatMapFacts.in_find_iff. intros contra;
  rewrite -> H0 in contra; discriminate.
  injection H; intros; subst.
  split; intros.
  case_eq (eqb n e); intros.
  apply cmp_to_eq in H2; right; exact H2.
  apply cmp_to_uneq in H2.
  left. apply NatMapFacts.remove_in_iff.
  split. exact H2. exact H1.
  destruct H1. apply NatMapFacts.remove_in_iff in H1.
  destruct H1. exact H2. subst.
  apply NatMapFacts.in_find_iff. intros contra;
  rewrite -> H0 in contra; discriminate.
  discriminate.
  destruct (NatMap.find n mem); discriminate.
Qed.

Lemma enclave_elimination_id : forall e0 mem r_val e e1,
  enclave_elimination (enclave_state_value e0 mem) r_val =
  enclave_state_valid (enclave_state_value e e1) ->
  e0 = e.
Proof.
  intros.
  unfold enclave_elimination in H. destruct e0.
  destruct (eqb r_val r).
  destruct (NatMap.find r_val mem).
  discriminate. discriminate.
  destruct (NatMap.find r_val mem).
  injection H; intros; subst. reflexivity.
  discriminate.
  destruct (NatMap.find r_val mem).
  injection H; intros; subst. reflexivity.
  discriminate.
Qed.

Lemma enclave_elimination_neq : forall e0 mem r_val e e1 r,
  enclave_elimination (enclave_state_value e0 mem) r_val =
  enclave_state_valid (enclave_state_value e e1) ->
  e0 = enclave_ID_active r -> r_val <> r.
Proof.
  intros.
  unfold enclave_elimination in H. destruct e0.
  injection H0; intros; subst.
  destruct (NatMap.find r_val mem).
  case_eq (eqb r_val r); intros.
  destruct (eqb r_val r); discriminate.
  apply cmp_to_uneq in H1. exact H1.
  discriminate.
  destruct (NatMap.find r_val mem); discriminate.
Qed.

(* Active Enclave Contained *)
Definition active_enclave_contained (sigma: runtime_state): Prop :=
  forall k mu rho pi p l q e0 E,
  (sigma = runtime_state_value k mu rho pi) ->
  (NatMap.find p pi = Some (process_value (enclave_state_value e0 E) l q)) ->
  ((e0 = enclave_ID_inactive) \/
  (forall e, e0 = enclave_ID_active e -> NatMap.In e E)).

(* Active Enclave Contained Preservation *)
Lemma active_enclave_contained_preservation : forall sigma obs sigma' obs',
  active_enclave_contained sigma -> <<sigma; obs>> ===> <<sigma'; obs'>>
  -> active_enclave_contained sigma'.
Proof.
  destruct sigma; destruct sigma'.
  unfold active_enclave_contained in *.
  intros. injection H1; intros; subst.
  inversion H0. inversion H14; subst.
  - destruct e'.
    case_eq (eqb p0 p1); intros.
    apply cmp_to_eq in H3; subst.
    assert (Some (process_value (enclave_state_value e0 E) l q) =
    Some (process_value (enclave_state_value e e1) l' q0)).
    rewrite <- H2. apply NatMapFacts.add_eq_o; reflexivity.
    injection H3; intros; subst.
    apply (H m mu rho p p1 l0 q0 e e1).
    reflexivity. exact H15.
    apply cmp_to_uneq in H3.
    apply (H m mu rho p p1 l q e0 E).
    reflexivity. rewrite <- H2. apply eq_sym.
    apply NatMapFacts.add_neq_o; exact H3.
  - destruct e; destruct e'.
    assert (forall e, n = e \/ NatMap.In e e1 <-> NatMap.In e e3).
    apply (enclave_creation_mem e e1 mu n r_val2_addr r_val3 e2 e3 H38).
    apply enclave_creation_id in H38. subst.
    case_eq (eqb p0 p1); intros.
    apply cmp_to_eq in H4; subst.
    assert (Some (process_value (enclave_state_value e0 E) l q) =
    Some (process_value (enclave_state_value e2 e3) l' q0)).
    rewrite <- H2. apply NatMapFacts.add_eq_o; reflexivity.
    injection H4; intros; subst.
    assert (e2 = enclave_ID_inactive \/ (forall e,
    e2 = enclave_ID_active e -> NatMap.In e e1)).
    apply (H m mu rho p p1 l0 q0 e2 e1).
    reflexivity. exact H15.
    destruct H5. left; exact H5.
    right. intros. apply H3. right.
    apply H5. exact H6.
    apply cmp_to_uneq in H4.
    apply (H m mu rho p p1 l q e0 E).
    reflexivity. rewrite <- H2. apply eq_sym.
    apply NatMapFacts.add_neq_o; exact H4.
  - destruct e'.
    case_eq (eqb p0 p1); intros.
    apply cmp_to_eq in H3; subst.
    assert (Some (process_value (enclave_state_value e0 E) l q) =
    Some (process_value (enclave_state_value e e1) l' q0)).
    rewrite <- H2. apply NatMapFacts.add_eq_o; reflexivity.
    injection H3; intros; subst.
    apply (H m m0 rho p p1 l0 q0 e e1).
    reflexivity. exact H15.
    apply cmp_to_uneq in H3.
    apply (H m m0 rho p p1 l q e0 E).
    reflexivity. rewrite <- H2. apply eq_sym.
    apply NatMapFacts.add_neq_o; exact H3.
  - destruct e; destruct e'.
    assert (forall e, NatMap.In e e1 <-> NatMap.In e e3 \/ r_val = e).
    apply (enclave_elimination_mem e e1 r_val e2 e3 H36).
    assert (H37 := H36).
    apply enclave_elimination_id in H36. subst.
    case_eq (eqb p0 p1); intros.
    apply cmp_to_eq in H4; subst.
    assert (Some (process_value (enclave_state_value e0 E) l q) =
    Some (process_value (enclave_state_value e2 e3) l' q0)).
    rewrite <- H2. apply NatMapFacts.add_eq_o; reflexivity.
    injection H4; intros; subst.
    assert (e2 = enclave_ID_inactive \/ (forall e,
    e2 = enclave_ID_active e -> NatMap.In e e1)).
    apply (H m m0 rho p p1 l0 q0 e2 e1).
    reflexivity. exact H15.
    destruct H5. left; exact H5.
    destruct e2. right. intros.
    injection H6; intros; subst.
    specialize (H5 e). assert (NatMap.In e e1).
    apply H5. reflexivity. apply H3 in H7.
    destruct H7. exact H7. subst.
    apply (enclave_elimination_neq (enclave_ID_active e) e1 e
    (enclave_ID_active e) e3 e) in H37.
    destruct H37; reflexivity. reflexivity.
    left; reflexivity.
    apply cmp_to_uneq in H4.
    apply (H m m0 rho p p1 l q e0 E).
    reflexivity. rewrite <- H2. apply eq_sym.
    apply NatMapFacts.add_neq_o; exact H4.
  - destruct e'; destruct e.
    unfold active_enclave_update in H33.
    case_eq (NatMap.find r_val e3); intros.
    assert (A0 := H3); destruct (NatMap.find r_val e3) in A0, H33.
    injection A0; injection H33; intros; subst; clear A0.
    assert (NatMap.In r_val e2).
    apply NatMapFacts.in_find_iff.
    intros contra; rewrite -> H3 in contra; discriminate.
    case_eq (eqb p0 p1); intros.
    apply cmp_to_eq in H5; subst.
    assert (Some (process_value (enclave_state_value e0 E) l q) =
    Some (process_value (enclave_state_value (enclave_ID_active r_val) e2) l' q0)).
    rewrite <- H2. apply NatMapFacts.add_eq_o; reflexivity.
    injection H5; intros; subst. right; intros.
    injection H6; intros; subst. exact H4.
    apply cmp_to_uneq in H5.
    apply (H k mu rho p p1 l q e0 E).
    reflexivity. rewrite <- H2. apply eq_sym.
    apply NatMapFacts.add_neq_o; exact H5.
    discriminate.
    destruct (NatMap.find r_val e3); discriminate.
  - destruct e'; destruct e.
    unfold active_enclave_update in H32.
    injection H32; intros; subst.
    case_eq (eqb p0 p1); intros.
    apply cmp_to_eq in H3; subst.
    assert (Some (process_value (enclave_state_value e0 E) l q) =
    Some (process_value (enclave_state_value enclave_ID_inactive e2) l' q0)).
    rewrite <- H2. apply NatMapFacts.add_eq_o; reflexivity.
    injection H3; intros; subst. left; reflexivity.
    apply cmp_to_uneq in H3.
    apply (H k mu rho p p1 l q e0 E).
    reflexivity. rewrite <- H2. apply eq_sym.
    apply NatMapFacts.add_neq_o; exact H3.
  - destruct e'.
    case_eq (eqb p0 p1); intros.
    apply cmp_to_eq in H3; subst.
    assert (Some (process_value (enclave_state_value e0 E) l q) =
    Some (process_value (enclave_state_value e e1) l' q0)).
    rewrite <- H2. apply NatMapFacts.add_eq_o; reflexivity.
    injection H3; intros; subst.
    apply (H k mu rho p p1 l0 q0 e e1).
    reflexivity. exact H15.
    apply cmp_to_uneq in H3.
    apply (H k mu rho p p1 l q e0 E).
    reflexivity. rewrite <- H2. apply eq_sym.
    apply NatMapFacts.add_neq_o; exact H3.
  - destruct e'.
    case_eq (eqb p0 p1); intros.
    apply cmp_to_eq in H3; subst.
    assert (Some (process_value (enclave_state_value e0 E) l q) =
    Some (process_value (enclave_state_value e e1) l' q0)).
    rewrite <- H2. apply NatMapFacts.add_eq_o; reflexivity.
    injection H3; intros; subst.
    apply (H k mu rho p p1 l0 q0 e e1).
    reflexivity. exact H15.
    apply cmp_to_uneq in H3.
    apply (H k mu rho p p1 l q e0 E).
    reflexivity. rewrite <- H2. apply eq_sym.
    apply NatMapFacts.add_neq_o; exact H3.
  - subst. destruct e.
    case_eq (eqb p0 p1); intros.
    apply cmp_to_eq in H3; subst.
    assert (Some (process_value (enclave_state_value e0 E) l q) =
    Some (process_value (enclave_state_value e e1) l0 q')).
    rewrite <- H2. apply NatMapFacts.add_eq_o; reflexivity.
    injection H3; intros; subst.
    apply (H k mu rho p p1 l0 q0 e e1).
    reflexivity. exact H6.
    apply cmp_to_uneq in H3.
    apply (H k mu rho p p1 l q e0 E).
    reflexivity. rewrite <- H2. apply eq_sym.
    apply NatMapFacts.add_neq_o; exact H3.
Qed.

(* Well-Formed Enclave State *)
Definition wf_enclave_state (sigma: runtime_state): Prop :=
  (active_enclave_contained sigma).

(*
Lemma disjoint_enclave_states_preservation : forall sigma obs sigma' obs',
  disjoint_enclave_states sigma -> <<sigma; obs>> ===> <<sigma'; obs'>>
  -> disjoint_enclave_states sigma'.
Proof.
  destruct sigma; destruct sigma'.
  unfold disjoint_enclave_states in *.
  intros. injection H1; intros; subst.
  inversion H0. inversion H16; subst.
  - destruct e'.
    case_eq (eqb p0 p'); case_eq (eqb p0 p1); intros.
    apply cmp_to_eq in H5, H6; subst.
    destruct H4; reflexivity.
    apply cmp_to_uneq in H5; apply cmp_to_eq in H6; subst.
    assert (Some (process_value (enclave_state_value e0' E') l' q') =
    Some (process_value (enclave_state_value e e1) l'0 q0)).
    rewrite <- H3. apply NatMapFacts.add_eq_o; reflexivity.
    injection H6; intros; subst.
    apply (H m mu rho p p1 l q e0 E p' l0 q0 e e1). reflexivity.
    rewrite <- H2. apply eq_sym. apply NatMapFacts.add_neq_o; exact H5.
    exact H17. exact H4.
    apply cmp_to_eq in H5; apply cmp_to_uneq in H6; subst.
    assert (Some (process_value (enclave_state_value e0 E) l q) =
    Some (process_value (enclave_state_value e e1) l'0 q0)).
    rewrite <- H2. apply NatMapFacts.add_eq_o; reflexivity.
    injection H5; intros; subst.
    apply (H m mu rho p p1 l0 q0 e e1 p' l' q' e0' E'). reflexivity.
    rewrite <- H17. reflexivity.
    rewrite <- H3. apply eq_sym.
    apply NatMapFacts.add_neq_o; exact H6. exact H6.
    apply cmp_to_uneq in H5, H6.
    apply (H m mu rho p p1 l q e0 E p' l' q' e0' E'). reflexivity.
    rewrite <- H2. apply eq_sym. apply NatMapFacts.add_neq_o. exact H5.
    rewrite <- H3. apply eq_sym. apply NatMapFacts.add_neq_o. exact H6.
    exact H4.
  - assert (H41 := H39).
    destruct e; destruct e'.
    apply enclave_creation_id in H39. subst e.
    assert (forall e, n = e \/ NatMap.In e e1 <-> NatMap.In e e3).
    apply (enclave_creation_mem e2 e1 mu n r_val2_addr r_val3 e2 e3 H41).

    case_eq (eqb p0 p'); case_eq (eqb p0 p1); intros.
    apply cmp_to_eq in H6, H7; subst.
    destruct H4; reflexivity.
    apply cmp_to_uneq in H6; apply cmp_to_eq in H7; subst.
    assert (Some (process_value (enclave_state_value e0' E') l' q') =
    Some (process_value (enclave_state_value e2 e3) l'0 q0)).
    rewrite <- H3. apply NatMapFacts.add_eq_o; reflexivity.
    injection H7; intros; subst.

(*
    assert ((forall e, NatMap.In e E -> ~NatMap.In e e1) /\
    (forall e, NatMap.In e e1 -> ~NatMap.In e E) ->
    (forall e, NatMap.In e E -> ~NatMap.In e e3) /\
    (forall e, NatMap.In e e3 -> ~NatMap.In e E)).
    intros. destruct H8. split; intros.
    intros contra. apply H8 in H10.
    apply H5 in contra. destruct contra. subst.
    apply enclave_creation_new in H41.
*)


    apply (H m mu rho p p1 l q e0 E p' l0 q0 e2 e3). reflexivity.
    rewrite <- H2. apply eq_sym. apply NatMapFacts.add_neq_o; exact H6.
    exact H17. exact H4.
    apply cmp_to_eq in H5; apply cmp_to_uneq in H6; subst.
    assert (Some (process_value (enclave_state_value e0 E) l q) =
    Some (process_value (enclave_state_value e e1) l'0 q0)).
    rewrite <- H2. apply NatMapFacts.add_eq_o; reflexivity.
    injection H5; intros; subst.
    apply (H m mu rho p p1 l0 q0 e e1 p' l' q' e0' E'). reflexivity.
    rewrite <- H17. reflexivity.
    rewrite <- H3. apply eq_sym.
    apply NatMapFacts.add_neq_o; exact H6. exact H6.
    apply cmp_to_uneq in H5, H6.
    apply (H m mu rho p p1 l q e0 E p' l' q' e0' E'). reflexivity.
    rewrite <- H2. apply eq_sym. apply NatMapFacts.add_neq_o. exact H5.
    rewrite <- H3. apply eq_sym. apply NatMapFacts.add_neq_o. exact H6.
    exact H4.

  - destruct e'.
    case_eq (eqb p0 p'); case_eq (eqb p0 p1); intros.
    apply cmp_to_eq in H5, H6; subst.
    destruct H4; reflexivity.
    apply cmp_to_uneq in H5; apply cmp_to_eq in H6; subst.
    assert (Some (process_value (enclave_state_value e0' E') l' q') =
    Some (process_value (enclave_state_value e e1) l'0 q0)).
    rewrite <- H3. apply NatMapFacts.add_eq_o; reflexivity.
    injection H6; intros; subst.
    apply (H m m0 rho p p1 l q e0 E p' l0 q0 e e1). reflexivity.
    rewrite <- H2. apply eq_sym. apply NatMapFacts.add_neq_o; exact H5.
    exact H17. exact H4.
    apply cmp_to_eq in H5; apply cmp_to_uneq in H6; subst.
    assert (Some (process_value (enclave_state_value e0 E) l q) =
    Some (process_value (enclave_state_value e e1) l'0 q0)).
    rewrite <- H2. apply NatMapFacts.add_eq_o; reflexivity.
    injection H5; intros; subst.
    apply (H m m0 rho p p1 l0 q0 e e1 p' l' q' e0' E'). reflexivity.
    rewrite <- H17. reflexivity.
    rewrite <- H3. apply eq_sym.
    apply NatMapFacts.add_neq_o; exact H6. exact H6.
    apply cmp_to_uneq in H5, H6.
    apply (H m m0 rho p p1 l q e0 E p' l' q' e0' E'). reflexivity.
    rewrite <- H2. apply eq_sym. apply NatMapFacts.add_neq_o. exact H5.
    rewrite <- H3. apply eq_sym. apply NatMapFacts.add_neq_o. exact H6.
    exact H4.
  - give_up.
  - destruct e'. destruct e.
    unfold active_enclave_update in H34.
    destruct (NatMap.find r_val e3).
    injection H34; intros; subst.
    case_eq (eqb p0 p'); case_eq (eqb p0 p1); intros.
    apply cmp_to_eq in H5, H6; subst.
    destruct H4; reflexivity.
    apply cmp_to_uneq in H5; apply cmp_to_eq in H6; subst.
    assert (Some (process_value (enclave_state_value e0' E') l' q') =
    Some (process_value (enclave_state_value (enclave_ID_active r_val) e2) l'0 q0)).
    rewrite <- H3. apply NatMapFacts.add_eq_o; reflexivity.
    injection H6; intros; subst.
    apply (H k mu rho p p1 l q e0 E p' l0 q0 e e2). reflexivity.
    rewrite <- H2. apply eq_sym. apply NatMapFacts.add_neq_o; exact H5.
    exact H17. exact H4.
    apply cmp_to_eq in H5; apply cmp_to_uneq in H6; subst.
    assert (Some (process_value (enclave_state_value e0 E) l q) =
    Some (process_value (enclave_state_value (enclave_ID_active r_val) e2) l'0 q0)).
    rewrite <- H2. apply NatMapFacts.add_eq_o; reflexivity.
    injection H5; intros; subst.
    apply (H k mu rho p p1 l0 q0 e e2 p' l' q' e0' E'). reflexivity.
    rewrite <- H17. reflexivity.
    rewrite <- H3. apply eq_sym.
    apply NatMapFacts.add_neq_o; exact H6. exact H6.
    apply cmp_to_uneq in H5, H6.
    apply (H k mu rho p p1 l q e0 E p' l' q' e0' E'). reflexivity.
    rewrite <- H2. apply eq_sym. apply NatMapFacts.add_neq_o. exact H5.
    rewrite <- H3. apply eq_sym. apply NatMapFacts.add_neq_o. exact H6.
    exact H4. discriminate.
  - destruct e'. destruct e.
    unfold active_enclave_update in H33.
    injection H33; intros; subst.
    case_eq (eqb p0 p'); case_eq (eqb p0 p1); intros.
    apply cmp_to_eq in H5, H6; subst.
    destruct H4; reflexivity.
    apply cmp_to_uneq in H5; apply cmp_to_eq in H6; subst.
    assert (Some (process_value (enclave_state_value e0' E') l' q') =
    Some (process_value (enclave_state_value enclave_ID_inactive e2) l'0 q0)).
    rewrite <- H3. apply NatMapFacts.add_eq_o; reflexivity.
    injection H6; intros; subst.
    apply (H k mu rho p p1 l q e0 E p' l0 q0 e e2). reflexivity.
    rewrite <- H2. apply eq_sym. apply NatMapFacts.add_neq_o; exact H5.
    exact H17. exact H4.
    apply cmp_to_eq in H5; apply cmp_to_uneq in H6; subst.
    assert (Some (process_value (enclave_state_value e0 E) l q) =
    Some (process_value (enclave_state_value enclave_ID_inactive e2) l'0 q0)).
    rewrite <- H2. apply NatMapFacts.add_eq_o; reflexivity.
    injection H5; intros; subst.
    apply (H k mu rho p p1 l0 q0 e e2 p' l' q' e0' E'). reflexivity.
    rewrite <- H17. reflexivity.
    rewrite <- H3. apply eq_sym.
    apply NatMapFacts.add_neq_o; exact H6. exact H6.
    apply cmp_to_uneq in H5, H6.
    apply (H k mu rho p p1 l q e0 E p' l' q' e0' E'). reflexivity.
    rewrite <- H2. apply eq_sym. apply NatMapFacts.add_neq_o. exact H5.
    rewrite <- H3. apply eq_sym. apply NatMapFacts.add_neq_o. exact H6.
    exact H4.
  - destruct e'.
    case_eq (eqb p0 p'); case_eq (eqb p0 p1); intros.
    apply cmp_to_eq in H5, H6; subst.
    destruct H4; reflexivity.
    apply cmp_to_uneq in H5; apply cmp_to_eq in H6; subst.
    assert (Some (process_value (enclave_state_value e0' E') l' q') =
    Some (process_value (enclave_state_value e e1) l'0 q0)).
    rewrite <- H3. apply NatMapFacts.add_eq_o; reflexivity.
    injection H6; intros; subst.
    apply (H k mu rho p p1 l q e0 E p' l0 q0 e e1). reflexivity.
    rewrite <- H2. apply eq_sym. apply NatMapFacts.add_neq_o; exact H5.
    exact H17. exact H4.
    apply cmp_to_eq in H5; apply cmp_to_uneq in H6; subst.
    assert (Some (process_value (enclave_state_value e0 E) l q) =
    Some (process_value (enclave_state_value e e1) l'0 q0)).
    rewrite <- H2. apply NatMapFacts.add_eq_o; reflexivity.
    injection H5; intros; subst.
    apply (H k mu rho p p1 l0 q0 e e1 p' l' q' e0' E'). reflexivity.
    rewrite <- H17. reflexivity.
    rewrite <- H3. apply eq_sym.
    apply NatMapFacts.add_neq_o; exact H6. exact H6.
    apply cmp_to_uneq in H5, H6.
    apply (H k mu rho p p1 l q e0 E p' l' q' e0' E'). reflexivity.
    rewrite <- H2. apply eq_sym. apply NatMapFacts.add_neq_o. exact H5.
    rewrite <- H3. apply eq_sym. apply NatMapFacts.add_neq_o. exact H6.
    exact H4.
  - destruct e'.
    case_eq (eqb p0 p'); case_eq (eqb p0 p1); intros.
    apply cmp_to_eq in H5, H6; subst.
    destruct H4; reflexivity.
    apply cmp_to_uneq in H5; apply cmp_to_eq in H6; subst.
    assert (Some (process_value (enclave_state_value e0' E') l' q') =
    Some (process_value (enclave_state_value e e1) l'0 q0)).
    rewrite <- H3. apply NatMapFacts.add_eq_o; reflexivity.
    injection H6; intros; subst.
    apply (H k mu rho p p1 l q e0 E p' l0 q0 e e1). reflexivity.
    rewrite <- H2. apply eq_sym. apply NatMapFacts.add_neq_o; exact H5.
    exact H17. exact H4.
    apply cmp_to_eq in H5; apply cmp_to_uneq in H6; subst.
    assert (Some (process_value (enclave_state_value e0 E) l q) =
    Some (process_value (enclave_state_value e e1) l'0 q0)).
    rewrite <- H2. apply NatMapFacts.add_eq_o; reflexivity.
    injection H5; intros; subst.
    apply (H k mu rho p p1 l0 q0 e e1 p' l' q' e0' E'). reflexivity.
    rewrite <- H17. reflexivity.
    rewrite <- H3. apply eq_sym.
    apply NatMapFacts.add_neq_o; exact H6. exact H6.
    apply cmp_to_uneq in H5, H6.
    apply (H k mu rho p p1 l q e0 E p' l' q' e0' E'). reflexivity.
    rewrite <- H2. apply eq_sym. apply NatMapFacts.add_neq_o. exact H5.
    rewrite <- H3. apply eq_sym. apply NatMapFacts.add_neq_o. exact H6.
    exact H4.
  - subst. destruct e.
    case_eq (eqb p0 p'); case_eq (eqb p0 p1); intros.
    apply cmp_to_eq in H5, H6; subst.
    destruct H4; reflexivity.
    apply cmp_to_uneq in H5; apply cmp_to_eq in H6; subst.
    assert (Some (process_value (enclave_state_value e0' E') l' q') =
    Some (process_value (enclave_state_value e e1) l0 q'0)).
    rewrite <- H3. apply NatMapFacts.add_eq_o; reflexivity.
    injection H6; intros; subst.
    apply (H k mu rho p p1 l q e0 E p' l0 q0 e e1). reflexivity.
    rewrite <- H2. apply eq_sym. apply NatMapFacts.add_neq_o; exact H5.
    exact H8. exact H4.
    apply cmp_to_eq in H5; apply cmp_to_uneq in H6; subst.
    assert (Some (process_value (enclave_state_value e0 E) l q) =
    Some (process_value (enclave_state_value e e1) l0 q'0)).
    rewrite <- H2. apply NatMapFacts.add_eq_o; reflexivity.
    injection H5; intros; subst.
    apply (H k mu rho p p1 l0 q0 e e1 p' l' q' e0' E'). reflexivity.
    exact H8. rewrite <- H3. apply eq_sym.
    apply NatMapFacts.add_neq_o; exact H6. exact H6.
    apply cmp_to_uneq in H5, H6.
    apply (H k mu rho p p1 l q e0 E p' l' q' e0' E'). reflexivity.
    rewrite <- H2. apply eq_sym. apply NatMapFacts.add_neq_o. exact H5.
    rewrite <- H3. apply eq_sym. apply NatMapFacts.add_neq_o. exact H6.
    exact H4.
Admitted.
*)
