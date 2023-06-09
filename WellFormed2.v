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
Require Import WellFormed.
Require Import WellFormedEnclaveState.

Module NatMapFacts := NatMapProperties.F.
Module CacheletMapFacts := CacheletMapProperties.F.

(* Disjoint VPT (used in wf3) *)
Definition disjoint_VPT (V: VPT): Prop :=
  forall e ranV, NatMap.find e V = Some ranV ->
  (forall e' ranV', e <> e' -> NatMap.find e' V = Some ranV' ->
   (forall c, In c ranV -> ~In c ranV') /\ (forall c, In c ranV' -> ~In c ranV)).

Lemma disjoint_VPT_remove : forall r V,
  disjoint_VPT V -> disjoint_VPT (NatMap.remove r V).
Proof.
  intros.
  unfold disjoint_VPT in *; intros.
  assert (NatMap.find (elt:=remapping_list) r (NatMap.remove r V) = None).
  apply NatMapFacts.remove_eq_o; reflexivity.
  case_eq (eqb e r); intros.
  apply cmp_to_eq in H4; subst.
  rewrite -> H0 in H3; discriminate.
  case_eq (eqb e' r); intros.
  apply cmp_to_eq in H5; subst.
  rewrite -> H2 in H3; discriminate.
  apply cmp_to_uneq in H4, H5.
  assert (NatMap.find (elt:=remapping_list) e (NatMap.remove r V) = NatMap.find e V).
  apply NatMapFacts.remove_neq_o; apply not_eq_sym; exact H4.
  assert (NatMap.find (elt:=remapping_list) e' (NatMap.remove r V) = NatMap.find e' V).
  apply NatMapFacts.remove_neq_o; apply not_eq_sym; exact H5.
  rewrite -> H0 in H6; rewrite -> H2 in H7; apply eq_sym in H6, H7.
  specialize (H e ranV H6 e' ranV' H1 H7).
  exact H.
Qed.

Lemma disjoint_VPT_add : forall r V q l,
  NatMap.find r V = Some (q :: l) ->
  disjoint_VPT V -> disjoint_VPT (NatMap.add r l V).
Proof.
  intros.
  unfold disjoint_VPT in *; intros.
  case_eq (eqb e r); case_eq (eqb e' r); intros.
  apply cmp_to_eq in H4, H5; subst.
  unfold not in H2; destruct H2; reflexivity.
  apply cmp_to_uneq in H4; apply cmp_to_eq in H5; subst.
  assert (NatMap.find (elt:=remapping_list) r (NatMap.add r l V) = Some l).
  apply NatMapFacts.add_eq_o; reflexivity.
  assert (NatMap.find (elt:=remapping_list) e' (NatMap.add r l V)
  = NatMap.find (elt:=remapping_list) e' V).
  apply NatMapFacts.add_neq_o; exact H2.
  rewrite -> H1 in H5; injection H5; intros; subst.
  rewrite -> H3 in H6; apply eq_sym in H6.
  specialize (H0 r (q :: l) H e' ranV' H2 H6); destruct H0.
  split; intros.
  apply (in_cons q c l) in H8. apply H0 in H8. exact H8.
  apply H7 in H8. intros contra. apply (in_cons q c l) in contra.
  apply H8 in contra. exact contra.
  apply cmp_to_uneq in H5; apply cmp_to_eq in H4; subst.
  assert (NatMap.find (elt:=remapping_list) r (NatMap.add r l V) = Some l).
  apply NatMapFacts.add_eq_o; reflexivity.
  assert (NatMap.find (elt:=remapping_list) e (NatMap.add r l V)
  = NatMap.find (elt:=remapping_list) e V).
  apply NatMapFacts.add_neq_o; apply not_eq_sym; exact H2.
  rewrite -> H3 in H4; injection H4; intros; subst.
  rewrite -> H1 in H6; apply eq_sym in H6.
  specialize (H0 e ranV H6 r (q :: l) H2 H); destruct H0.
  split; intros.
  apply H0 in H8. intros contra. apply (in_cons q c l) in contra.
  apply H8 in contra. exact contra.
  apply (in_cons q c l) in H8. apply H7 in H8. exact H8.
  apply cmp_to_uneq in H4, H5.
  assert (NatMap.find (elt:=remapping_list) e (NatMap.add r l V)
  = NatMap.find (elt:=remapping_list) e V).
  apply NatMapFacts.add_neq_o; apply not_eq_sym; exact H5.
  assert (NatMap.find (elt:=remapping_list) e' (NatMap.add r l V)
  = NatMap.find (elt:=remapping_list) e' V).
  apply NatMapFacts.add_neq_o; apply not_eq_sym; exact H4.
  rewrite -> H1 in H6; rewrite -> H3 in H7; apply eq_sym in H6, H7.
  apply (H0 e ranV H6 e' ranV' H2 H7).
Qed.

Lemma disjoint_VPT_add2 : forall r V q l,
  NatMap.find r V = Some l ->
  (forall e l', NatMap.find e V = Some l' -> ~In q l') ->
  disjoint_VPT V -> disjoint_VPT (NatMap.add r (q :: l) V).
Proof.
  intros.
  unfold disjoint_VPT in *; intros.
  case_eq (eqb e r); case_eq (eqb e' r); intros.
  apply cmp_to_eq in H5, H6; subst.
  assert (r = r). reflexivity. apply H3 in H5. destruct H5.
  apply cmp_to_eq in H6. apply cmp_to_uneq in H5. subst e.
  assert (Some ranV = Some (q :: l)).
  rewrite <- H2. apply NatMapFacts.add_eq_o; reflexivity.
  injection H6; intros; subst.
  assert (NatMap.find (elt:=remapping_list) e' V = Some ranV').
  apply eq_sym. rewrite <- H4. apply NatMapFacts.add_neq_o; exact H3.
  split; intros. intros contra. apply in_inv in H8. destruct H8. subst.
  specialize (H0 e' ranV' H7). apply H0 in contra. exact contra.
  specialize (H1 r l H e' ranV' H3 H7). destruct H1. apply H1 in H8.
  apply H8 in contra. exact contra.
  intros contra. apply in_inv in contra. destruct contra. subst.
  specialize (H0 e' ranV' H7). apply H0 in H8. exact H8.
  specialize (H1 r l H e' ranV' H3 H7). destruct H1. apply H1 in H9.
  apply H9 in H8. exact H8.
  apply cmp_to_uneq in H6. apply cmp_to_eq in H5. subst e'.
  assert (Some ranV' = Some (q :: l)).
  rewrite <- H4. apply NatMapFacts.add_eq_o; reflexivity.
  injection H5; intros; subst.
  assert (NatMap.find (elt:=remapping_list) e V = Some ranV).
  apply eq_sym. rewrite <- H2. apply NatMapFacts.add_neq_o; apply not_eq_sym; exact H3.
  split; intros. intros contra. apply in_inv in contra. destruct contra. subst.
  specialize (H0 e ranV H7). apply H0 in H8. exact H8.
  specialize (H1 e ranV H7 r l H3 H). destruct H1. apply H1 in H8.
  apply H8 in H9. exact H9.
  intros contra. apply in_inv in H8. destruct H8. subst.
  specialize (H0 e ranV H7). apply H0 in contra. exact contra.
  specialize (H1 e ranV H7 r l H3 H). destruct H1. apply H9 in H8.
  apply H8 in contra. exact contra.
  apply cmp_to_uneq in H5, H6.
  assert (NatMap.find e V = Some ranV). apply eq_sym.
  rewrite <- H2. apply NatMapFacts.add_neq_o; apply not_eq_sym; exact H6.
  assert (NatMap.find e' V = Some ranV'). apply eq_sym.
  rewrite <- H4. apply NatMapFacts.add_neq_o; apply not_eq_sym; exact H5.
  specialize (H1 e ranV H7 e' ranV' H3 H8). destruct H1.
  split; intros.
  apply H1. exact H10.
  apply H9. exact H10.
Qed.

Lemma disjoint_VPT_add_none : forall r V q,
  NatMap.find r V = None ->
  (forall e l', NatMap.find e V = Some l' -> ~In q l') ->
  disjoint_VPT V -> disjoint_VPT (NatMap.add r (q :: nil) V).
Proof.
  intros.
  unfold disjoint_VPT in *; intros.
  case_eq (eqb e r); case_eq (eqb e' r); intros.
  apply cmp_to_eq in H5, H6; subst.
  assert (r = r). reflexivity. apply H3 in H5. destruct H5.
  apply cmp_to_eq in H6. apply cmp_to_uneq in H5. subst e.
  assert (Some ranV = Some (q :: nil)).
  rewrite <- H2. apply NatMapFacts.add_eq_o; reflexivity.
  injection H6; intros; subst.
  assert (NatMap.find (elt:=remapping_list) e' V = Some ranV').
  apply eq_sym. rewrite <- H4. apply NatMapFacts.add_neq_o; exact H3.
  split; intros. intros contra. apply in_inv in H8. destruct H8. subst.
  specialize (H0 e' ranV' H7). apply H0 in contra. exact contra.
  unfold In in H8. exact H8.
  intros contra. apply in_inv in contra. destruct contra. subst.
  specialize (H0 e' ranV' H7). apply H0 in H8. exact H8.
  unfold In in H9. exact H9.
  apply cmp_to_uneq in H6. apply cmp_to_eq in H5. subst e'.
  assert (Some ranV' = Some (q :: nil)).
  rewrite <- H4. apply NatMapFacts.add_eq_o; reflexivity.
  injection H5; intros; subst.
  assert (NatMap.find (elt:=remapping_list) e V = Some ranV).
  apply eq_sym. rewrite <- H2. apply NatMapFacts.add_neq_o; apply not_eq_sym; exact H3.
  split; intros. intros contra. apply in_inv in contra. destruct contra. subst.
  specialize (H0 e ranV H7). apply H0 in H8. exact H8.
  unfold In in H9. exact H9.
  intros contra. apply in_inv in H8. destruct H8. subst.
  specialize (H0 e ranV H7). apply H0 in contra. exact contra.
  unfold In in H8. exact H8.
  apply cmp_to_uneq in H5, H6.
  assert (NatMap.find e V = Some ranV). apply eq_sym.
  rewrite <- H2. apply NatMapFacts.add_neq_o; apply not_eq_sym; exact H6.
  assert (NatMap.find e' V = Some ranV'). apply eq_sym.
  rewrite <- H4. apply NatMapFacts.add_neq_o; apply not_eq_sym; exact H5.
  specialize (H1 e ranV H7 e' ranV' H3 H8). destruct H1.
  split; intros.
  apply H1. exact H10.
  apply H9. exact H10.
Qed.

(* Well-Formed 3 *)
Definition wf3 (sigma: runtime_state): Prop :=
  (forall k mu rho pi lambda F V C R,
  (sigma = runtime_state_value k mu rho pi) ->
  (NatMap.find lambda k = Some (single_level_cache F V C R)) ->
  (forall e ranV, NatMap.find e V = Some ranV -> (forall c, In c ranV -> ~In c F) /\ (forall c, In c F -> ~In c ranV) /\ NoDup(ranV))
  /\ NoDup(F) /\ disjoint_VPT(V)).

(* WF3 MLC Read *)
Lemma mlc_read_v : forall lambda h_tree k e' m0 l0 D obs1 mu k' index F V C R F' V' C' R',
  well_defined_cache_tree h_tree ->
  mlc_read k e' m0 l0 lambda h_tree = mlc_read_valid D obs1 mu k' ->
  NatMap.find index k = Some (single_level_cache F V C R) ->
  NatMap.find index k' = Some (single_level_cache F' V' C' R') ->
  V = V'.
Proof.
  unfold mlc_read.
  intros lambda h_tree.
  case_eq (get_cache_ID_path lambda h_tree).
  intros l.
  generalize dependent lambda.
  induction l.
  {
    intros.
    unfold recursive_mlc_read in H1.
    destruct l0. destruct (NatMap.find b m0).
    injection H1; intros; subst.
    rewrite -> H2 in H3.
    injection H3; intros; subst F' V' C' R'.
    reflexivity.
    discriminate.
  }
  {
    intros.
    unfold recursive_mlc_read in H1.
    fold recursive_mlc_read in H1.
    case_eq (NatMap.find a k). intros.
    assert (A0 := H4). destruct (NatMap.find a k) in A0, H1.
    injection A0; intros; subst s0.
    case_eq (cc_hit_read s e' l0). intros.
    assert (A1 := H5). destruct (cc_hit_read s e' l0) in A1, H1.
    injection A1; injection H1; intros; subst; clear A0 A1.
    destruct s; destruct s0.
    apply (cc_hit_read_v (single_level_cache c0 v w s) e' l0 d d0 c
    (single_level_cache c1 v0 w0 s0) c0 v w s c1 v0 w0 s0) in H5.
    subst v0.
    {
      case_eq (eqb index a); intros.
      {
        apply cmp_to_eq in H5; subst a.
        rewrite -> H2 in H4.
        injection H4; intros; subst c0 v w s.
        assert (Some (single_level_cache F' V' C' R') = Some (single_level_cache c1 V w0 s0)).
        rewrite <- H3. apply NatMapFacts.add_eq_o; reflexivity.
        injection H5; intros; subst.
        reflexivity.
      }
      {
        apply cmp_to_uneq in H5.
        assert (NatMap.find index k = Some (single_level_cache F' V' C' R')).
        rewrite <- H3. apply eq_sym.
        apply NatMapFacts.add_neq_o; apply not_eq_sym; exact H5.
        rewrite -> H2 in H6.
        injection H6; intros; subst.
        reflexivity.
      }
    }
    reflexivity.
    reflexivity.
    discriminate.
    intros; destruct (cc_hit_read s e' l0).
    discriminate.
    clear A0.
    case_eq (recursive_mlc_read k e' m0 l0 l); intros.
    assert (A0 := H6). destruct (recursive_mlc_read k e' m0 l0 l) in A0, H1.
    case_eq (cc_update s e' d1 l0); intros.
    assert (A1 := H7). destruct (cc_update s e' d1 l0) in A1, H1.
    injection A0; injection A1; injection H1; intros; subst; clear A0 A1.
    {
      case_eq (eqb index a); intros.
      {
        apply cmp_to_eq in H8. subst a.
        destruct s. rewrite -> H2 in H4; injection H4; intros; subst c0 v w s.
        destruct s0.
        apply (cc_update_v (single_level_cache F V C R) e' d l0 c (single_level_cache c0 v w s)
        F V C R c0 v w s) in H7.
        subst v.
        assert (NatMap.find index (NatMap.add index (single_level_cache c0 V w s) m) =
        Some (single_level_cache c0 V w s)).
        apply NatMapFacts.add_eq_o. reflexivity.
        rewrite -> H3 in H7; injection H7; intros; subst c0 V' w s.
        reflexivity.
        reflexivity.
        reflexivity.
      }
      {
        apply cmp_to_uneq in H8.
        assert (WFH := H0).
        unfold well_defined_cache_tree in H0.
        destruct H0 as [ WFH1 ]. destruct H0 as [ WFH2 ]. destruct H0 as [ WFH3 ].
        destruct l.
        {
          apply (IHl root_node WFH1 k e' m0 l0 d d0 o m index F V C R F' V' C' R').
          exact WFH. exact H6. exact H2.
          rewrite <- H3. apply eq_sym.
          apply NatMapFacts.add_neq_o.
          apply not_eq_sym. exact H8.
        }
        {
          destruct lambda.
          rewrite -> WFH1 in H. discriminate.
          specialize (WFH3 c0 a (p :: l) H).
          unfold get_cache_ID_path in H. discriminate.
          specialize (WFH2 p0 a (p :: l) H).
          injection WFH2; intros; subst.
          apply (H0 p0 p l) in H.
          apply (IHl (cache_node p) H k e' m0 l0 d d0 o m index F V C R F' V' C' R').
          exact WFH. exact H6. exact H2.
          rewrite <- H3. apply eq_sym.
          apply NatMapFacts.add_neq_o.
          apply not_eq_sym. exact H8.
        }
      }
    }
    discriminate.
    destruct (cc_update s e' d1 l0); discriminate.
    discriminate.
    destruct (recursive_mlc_read k e' m0 l0 l); discriminate.
    discriminate.
    intros; destruct (NatMap.find a k); discriminate.
  }
  intros; destruct (get_cache_ID_path lambda h_tree); discriminate.
Qed.

Lemma wf3_mlc_read : forall lambda h_tree k e' m0 l0 D obs1 mu k' index psi psi'
  F V C R F' V' C' R',
  well_defined_cache_tree h_tree ->
  mlc_read k e' m0 l0 lambda h_tree = mlc_read_valid D obs1 mu k' ->
  NatMap.find index k = Some psi ->
  NatMap.find index k' = Some psi' ->
  psi = single_level_cache F V C R ->
  psi' = single_level_cache F' V' C' R' ->
  (forall enc ranV, NatMap.find enc V = Some ranV -> (forall c, In c ranV -> ~In c F) /\ (forall c, In c F -> ~In c ranV) /\ NoDup(ranV))
  /\ NoDup(F) /\ disjoint_VPT(V) ->
  (forall enc ranV', NatMap.find enc V' = Some ranV' -> (forall c, In c ranV' -> ~In c F') /\ (forall c, In c F' -> ~In c ranV') /\ NoDup(ranV'))
  /\ NoDup(F') /\ disjoint_VPT(V').
Proof.
  unfold mlc_read.
  intros lambda h_tree.
  case_eq (get_cache_ID_path lambda h_tree).
  intros l.
  generalize dependent lambda.
  induction l.
  {
    intros lambda H k e' m0 l0 D obs1 mu k' index psi psi' F V C R
    F' V' C' R' H0 H1 H2 H3 H4 H5 H8.
    unfold recursive_mlc_read in H1.
    subst.
    destruct l0.
    destruct (NatMap.find b m0).
    injection H1; intros; subst.
    rewrite -> H2 in H3.
    injection H3; intros; subst.
    exact H8. discriminate.
  }
  {
    intros lambda IHTREE k e' m0 l0 D obs1 mu k' index psi psi' F V C R
    F' V' C' R' H H0 H1 H2 H3 H4 H7.
    unfold recursive_mlc_read in H0.
    fold recursive_mlc_read in H0.
    case_eq (NatMap.find a k). intros.
    assert (A0 := H5). destruct (NatMap.find a k) in A0, H0.
    case_eq (cc_hit_read s0 e' l0). intros.
    assert (A1 := H6). destruct (cc_hit_read s0 e' l0) in A1, H0.
    injection H0; injection A0; injection A1; intros; subst; clear A0 A1.
    assert (H8:= H6).
    destruct s; destruct s1.
    apply (cc_hit_read_f (single_level_cache c0 v w s) e' l0 D obs1 c
    (single_level_cache c1 v0 w0 s0) c0 v w s c1 v0 w0 s0) in H6.
    apply (cc_hit_read_v (single_level_cache c0 v w s) e' l0 D obs1 c
    (single_level_cache c1 v0 w0 s0) c0 v w s c1 v0 w0 s0) in H8.
    subst.
    {
      case_eq (eqb a index).
      {
        intros. apply cmp_to_eq in H3. subst.
        rewrite -> H1 in H5.
        injection H5; intros; subst c1 v0 w s.
        assert (NatMap.find index (NatMap.add index (single_level_cache F V w0 s0) k) =
        Some (single_level_cache F V w0 s0)).
        apply NatMapFacts.add_eq_o. reflexivity.
        rewrite -> H3 in H2.
        injection H2; intros; subst F' V' w0 s0.
        exact H7.
      }
      {
        intros. apply cmp_to_uneq in H3.
        assert (NatMap.find index (NatMap.add a (single_level_cache c1 v0 w0 s0) k) = NatMap.find index k).
        apply NatMapFacts.add_neq_o. exact H3.
        rewrite -> H2 in H4.
        rewrite -> H1 in H4.
        injection H4; intros; subst F' V' C' R'.
        exact H7.
      }
    }
    reflexivity.
    reflexivity.
    reflexivity.
    reflexivity.
    discriminate.
    intros; destruct (cc_hit_read s0 e' l0).
    discriminate.
    case_eq (recursive_mlc_read k e' m0 l0 l). intros.
    assert (A1 := H8). destruct (recursive_mlc_read k e' m0 l0 l) in A1, H0.
    case_eq (cc_update s0 e' d1 l0). intros.
    assert (A2 := H9). destruct (cc_update s0 e' d1 l0) in A2, H0.
    injection H0; injection A0; injection A1; injection A2; intros; subst; clear A0 A1 A2.
    {
      case_eq (eqb index a).
      {
        intros. apply cmp_to_eq in H3. subst a.
        destruct s.
        assert (H10 := H9).
        destruct s1.
        apply (cc_update_f (single_level_cache c0 v w s) e' D l0 c (single_level_cache c1 v0 w0 s0)
        c0 v w s c1 v0 w0 s0) in H9.
        apply (cc_update_v (single_level_cache c0 v w s) e' D l0 c (single_level_cache c1 v0 w0 s0)
        c0 v w s c1 v0 w0 s0) in H10.
        subst.
        assert (NatMap.find index (NatMap.add index (single_level_cache c1 v0 w0 s0) m) =
        Some (single_level_cache c1 v0 w0 s0)).
        apply NatMapFacts.add_eq_o. reflexivity.
        rewrite -> H3 in H2.
        rewrite -> H5 in H1.
        injection H1; injection H2; intros; subst.
        exact H7.
        reflexivity.
        reflexivity.
        reflexivity.
        reflexivity.
      }
      {
        intros. apply cmp_to_uneq in H3.
        assert (WFH := H).
        unfold well_defined_cache_tree in H.
        destruct H as [ WFH1 ]. destruct H as [ WFH2 ]. destruct H as [ WFH3 ].
        destruct l.
        {
          apply (IHl root_node WFH1 k e' m0 l0 D obs1 o m index (single_level_cache F V C R)
          (single_level_cache F' V' C' R') F V C R F' V' C' R').
          exact WFH.
          unfold mlc_write. exact H8.
          exact H1.
          rewrite <- H2. apply eq_sym.
          apply NatMapFacts.add_neq_o.
          apply not_eq_sym. exact H3.
          reflexivity.
          reflexivity.
          exact H7.
        }
        {
          destruct lambda.
          rewrite -> WFH1 in IHTREE. discriminate.
          specialize (WFH3 c0 a (p :: l) IHTREE).
          unfold get_cache_ID_path in IHTREE. discriminate.
          specialize (WFH2 p0 a (p :: l) IHTREE).
          injection WFH2; intros; subst.
          apply (H p0 p l) in IHTREE.
          apply (IHl (cache_node p) IHTREE k e' m0 l0 D obs1 o m index (single_level_cache F V C R)
          (single_level_cache F' V' C' R') F V C R F' V' C' R').
          exact WFH.
          unfold mlc_write. exact H8.
          exact H1.
          rewrite <- H2. apply eq_sym.
          apply NatMapFacts.add_neq_o.
          apply not_eq_sym. exact H3.
          reflexivity.
          reflexivity.
          exact H7.
        }
      }
    }
    discriminate.
    intros; destruct (cc_update s0 e' d1 l0).
    discriminate.
    discriminate.
    discriminate.
    intros; destruct (recursive_mlc_read k e' m0 l0 l).
    discriminate.
    discriminate.
    discriminate.
    intros; destruct (NatMap.find a k).
    discriminate.
    discriminate.
  }
  intros; destruct (get_cache_ID_path lambda h_tree).
  discriminate.
  discriminate.
Qed.

(* WF3 MLC Allocation *)
Lemma NoDup_append : forall l l' (c : cachelet_index),
  NoDup(l) /\ NoDup(l') -> l = c :: nil -> ~In c l' -> NoDup(l ++ l').
Proof.
  intros.
  destruct H.
  rewrite -> H0.
  constructor. exact H1. exact H2.
Qed.

Lemma NoDup_remove : forall c F,
  NoDup(F) -> NoDup(remove eq_dec_cachelet c F).
Proof.
  intros.
  induction F.
  assert (~In c nil). unfold In; unfold not; auto.
  apply (notin_remove eq_dec_cachelet nil c) in H0.
  rewrite -> H0. exact H.
  apply NoDup_cons_iff in H. destruct H.
  unfold remove. case_eq (eq_dec_cachelet c a). intros.
  apply IHF. exact H0.
  intros. constructor. intros contra. apply H.
  assert (In a F /\ a <> c -> In a F). intros. destruct H2. exact H2.
  apply H2. apply (in_remove eq_dec_cachelet F a c). exact contra.
  apply IHF. exact H0.
Qed.

Lemma remove_CAT_not_in : forall c F remF,
  remove_CAT c F = Some remF -> ~In c remF.
Proof.
  intros.
  unfold remove_CAT in H.
  destruct (in_bool c F).
  injection H; intros; subst.
  apply remove_In. discriminate.
Qed.

Lemma remove_CAT_in : forall b c F remF,
  remove_CAT b F = Some remF -> b <> c -> In c F -> In c remF.
Proof.
  intros.
  unfold remove_CAT in H.
  case_eq (in_bool b F); intros.
  assert (A0 := H2). destruct (in_bool b F) in A0, H.
  injection H; intros; subst.
  apply in_bool_iff in H2. apply in_in_remove.
  apply not_eq_sym; exact H0. exact H1.
  discriminate.
  assert (A0 := H2).
  destruct (in_bool b F) in A0, H; discriminate.
Qed.

Lemma remove_CAT_inv_subset : forall w s w0 s0 F remF,
  remove_CAT (w, s) F = Some remF ->
  w0 <> w \/ s0 <> s ->
  ~In (w0, s0) F -> ~In (w0, s0) remF.
Proof.
  intros. unfold remove_CAT in H.
  destruct (in_bool (w, s) F).
  injection H; intros; subst.
  intros contra. apply in_remove in contra.
  destruct contra. apply H1 in H2. exact H2.
  discriminate.
Qed.

Lemma wf3_cachelet_allocation : forall n r F V C R F' V' C' R',
  cachelet_allocation n r (single_level_cache F V C R) = Some (single_level_cache F' V' C' R') ->
  (forall e' l', NatMap.find e' V = Some l' -> (forall c, In c l' -> ~ In c F) /\ (forall c, In c F -> ~ In c l')
  /\ NoDup(l')) /\ NoDup(F) /\ disjoint_VPT(V) ->
  (forall e' l', NatMap.find e' V' = Some l' -> (forall c, In c l' -> ~ In c F') /\ (forall c, In c F' -> ~ In c l')
  /\  NoDup(l')) /\ NoDup(F') /\ disjoint_VPT(V').
Proof.
  intros n r.
  unfold cachelet_allocation.
  destruct n.
  intros; discriminate.
  induction (S n).
  {
    intros.
    unfold cachelet_allocation in H.
    unfold recursive_cachelet_allocation in H.
    injection H; intros; subst.
    exact H0.
  }
  {
    intros.
    unfold recursive_cachelet_allocation in H.
    fold recursive_cachelet_allocation in H.
    case_eq (way_first_allocation F); intros.
    assert (A0 := H1); destruct (way_first_allocation F) in H, A0.
    destruct c0.
    case_eq (NatMap.find s R); intros.
    assert (A1 := H2); destruct (NatMap.find s R) in H, A1.
    case_eq (remove_CAT (w, s) F). intros c0 F0.
    assert (A3 := F0). destruct (remove_CAT (w, s) F) in H, A3.
    case_eq (NatMap.find r V). intros r0 H5.
    assert (A2 := H5). destruct (NatMap.find r V) in H, A2.
    injection A0; injection A1; injection A2; injection A3;
    intros X0 X1 X2 X3; subst; clear A0 A1 A2 A3.
    {
      apply (IHn0 c0 (NatMap.add r ((w, s) :: r0) V) C
      (NatMap.add s (update p w (enclave_ID_active r)) R) F' V' C' R').
      exact H.
      split. intros; case_eq (eqb e' r); intros V0.
      {
        apply cmp_to_eq in V0; subst e'.
        assert (NatMap.find (elt:=remapping_list) r (NatMap.add r ((w, s) :: r0) V)
        = Some ((w, s) :: r0)).
        apply NatMapFacts.add_eq_o;  reflexivity.
        rewrite -> H3 in H4; injection H4; intros; subst.
        destruct H0.
        specialize (H0 r r0 H5). destruct H0. destruct H7.
        split. intros. apply in_inv in H9.
        destruct H9. subst.
        apply remove_CAT_not_in in F0. exact F0.
        intros contra. apply (remove_CAT_f c (w, s) F c0 F0) in contra.
        apply H7 in contra. apply contra in H9. exact H9.
        split. intros; intros contra. apply in_inv in contra. destruct contra. subst.
        apply (remove_CAT_not_in (w, s) F c0) in F0. apply F0 in H9. exact H9.
        intros. apply (remove_CAT_f c (w, s) F c0 F0) in H9. apply H7 in H9.
        apply H9 in H10. exact H10.
        constructor. intros contra. unfold remove_CAT in F0.
        case_eq (in_bool (w, s) F). intros.
        apply in_bool_iff in H9. apply H7 in H9. apply H9 in contra. exact contra.
        intros; destruct (in_bool (w, s) F); discriminate. exact H8.
      }
      {
        apply cmp_to_uneq in V0.
        assert (NatMap.find e' V = Some l').
        rewrite <- H3. apply eq_sym. apply NatMapFacts.add_neq_o; apply not_eq_sym; exact V0.
        destruct H0.
        specialize (H0 e' l' H4).
        destruct H0; destruct H7.
        split; intros.
        intros contra. apply (remove_CAT_f c (w, s) F c0 F0) in contra.
        apply H7 in contra. apply contra in H9. exact H9.
        split. intros; intros contra.
        apply (remove_CAT_f c (w, s) F c0 F0) in H9.
        apply H7 in H9. apply H9 in contra. exact contra.
        exact H8.
      }
      destruct H0. destruct H3. split.
      unfold remove_CAT in F0. destruct (in_bool (w, s) F).
      injection F0; intros; subst.
      apply NoDup_remove. exact H3. discriminate.
      apply (disjoint_VPT_add2 r V (w, s) r0). exact H5.
      intros. specialize (H0 e l' H6). destruct H0. destruct H7.
      apply H7. unfold remove_CAT in F0. case_eq (in_bool (w, s) F); intros.
      apply in_bool_iff. exact H9.
      destruct (in_bool (w, s) F); discriminate. exact H4.
    }
    discriminate.
    intros H5; assert (A2 := H5); destruct (NatMap.find r V) in A2, H.
    discriminate.
    assert (L0 := H2).
    injection A0; injection A1; injection A3; intros X0 X1 X2; subst; clear A0 A1 A2 A3.
    {
      apply (IHn0 c0 (NatMap.add r ((w, s) :: nil) V) C
      (NatMap.add s (update p w (enclave_ID_active r)) R) F' V' C' R').
      unfold cachelet_allocation; exact H.
      destruct H0.
      split. intros.
      case_eq (eqb e' r); intros V1.
      {
        apply cmp_to_eq in V1; subst e'.
        assert (Some l' = Some ((w, s) :: nil)).
        rewrite <- H4. apply NatMapFacts.add_eq_o; reflexivity.
        injection H6; intros; subst.
        split. intros. intros contra.
        apply in_inv in H7. destruct H7. subst c.
        apply remove_CAT_not_in in F0.
        apply F0 in contra; exact contra.
        unfold In in H7; exact H7.
        split. intros. intros contra. apply in_inv in contra.
        destruct contra. subst c.
        apply remove_CAT_not_in in F0.
        apply F0 in H7. exact H7.
        unfold In in H8. exact H8.
        constructor. unfold In. auto. constructor.
      }
      {
        apply cmp_to_uneq in V1.
        assert (NatMap.find e' V = Some l').
        apply eq_sym; rewrite <- H4; apply NatMapFacts.add_neq_o; apply not_eq_sym; exact V1.
        specialize (H0 e' l' H6). destruct H0. destruct H7.
        split. intros. intros contra.
        apply (remove_CAT_f c (w, s) F c0 F0) in contra.
        apply H7 in contra. apply contra in H9. exact H9.
        split. intros. apply H7. apply (remove_CAT_f c (w, s) F c0 F0).
        exact H9. exact H8.
      }
      destruct H3. split.
      unfold remove_CAT in F0. destruct (in_bool (w, s) F).
      injection F0; intros; subst.
      apply NoDup_remove. exact H3. discriminate.
      apply (disjoint_VPT_add_none r V (w, s)). exact H5.
      intros. specialize (H0 e l' H6). destruct H0. destruct H7.
      apply H7. unfold remove_CAT in F0. case_eq (in_bool (w, s) F); intros.
      apply in_bool_iff; exact H9.
      destruct (in_bool (w, s) F); discriminate. exact H4.
    }
    discriminate.
    intros; destruct (remove_CAT (w, s) F).
    discriminate.
    discriminate.
    discriminate.
    intros; destruct (NatMap.find s R).
    discriminate.
    discriminate.
    discriminate.
    intros; destruct (way_first_allocation F).
    discriminate.
    discriminate.
  }
Qed.

Lemma wf3_mlc_alloc : forall lambda h_tree n state k k' index psi psi' F V C R F' V' C' R',
  well_defined_cache_tree h_tree ->
  mlc_allocation n state k lambda h_tree = Some k' ->
  NatMap.find index k = Some psi ->
  NatMap.find index k' = Some psi' ->
  psi = single_level_cache F V C R ->
  psi' = single_level_cache F' V' C' R' ->
  (forall e' l', NatMap.find e' V = Some l' -> (forall c, In c l' -> ~ In c F) /\ (forall c, In c F -> ~ In c l')
  /\ NoDup(l')) /\ NoDup(F) /\ disjoint_VPT(V) ->
  (forall enc l', NatMap.find enc V' = Some l' -> (forall c, In c l' -> ~ In c F') /\ (forall c, In c F' -> ~ In c l')
  /\  NoDup(l')) /\ NoDup(F') /\ disjoint_VPT(V').
Proof.
  unfold mlc_allocation.
  intros lambda h_tree.
  case_eq (get_cache_ID_path lambda h_tree).
  intros l0.
  generalize dependent lambda.
  destruct l0 as [|x].
  { intros; discriminate. }
  induction (x :: l0).
  {
    intros lambda IHTREE n r k k' index psi psi' F V C R
    F' V' C' R' WFH H H0 H1 H4 H5 H6.
    unfold recursive_mlc_allocation in H.
    injection H; intros; subst k'.
    rewrite -> H0 in H1.
    injection H1; intros; subst psi psi'.
    injection H2; intros; subst F' V' C' R'.
    exact H6.
  }
  {
    intros lambda IHTREE n r k k' index psi psi' F V C R
    F' V' C' R' WFH H H0 H1 H4 H5 H6.
    unfold recursive_mlc_allocation in H.
    fold recursive_mlc_allocation in H.
    destruct n. discriminate.
    case_eq (NatMap.find a k). intros.
    assert (A0 := H2). destruct (NatMap.find a k) in A0, H.
    case_eq (cachelet_allocation n r s0). intros.
    assert (A1 := H3). destruct (cachelet_allocation n r s0) in A1, H.
    injection A0; injection A1; intros; subst s0 s2; clear A0 A1.
    assert (WFH1 := WFH).
    unfold well_defined_cache_tree in WFH1.
    destruct WFH1 as [ WFH1 WFH2 ]. destruct WFH2 as [ WFH2 WFH3 ]. destruct WFH3 as [ WFH3 WFH4 ].
    case_eq (eqb index a).
    {
      intros; apply cmp_to_eq in H7; subst a.
      rewrite -> H2 in H0.
      injection H0; intros; subst s.
      destruct s1.
      destruct l.
      {
        apply (IHl root_node WFH1 n0 r (NatMap.add index (single_level_cache c v w s) k)
        k' index (single_level_cache c v w s) psi' c v w s F' V' C' R').
        exact WFH.
        exact H.
        apply NatMapFacts.add_eq_o. reflexivity.
        exact H1.
        reflexivity.
        exact H5.
        apply (wf3_cachelet_allocation n r F V C R c v w s).
        subst psi; exact H3. exact H6.
      }
      {
        destruct lambda.
        rewrite -> WFH1 in IHTREE. discriminate.
        specialize (WFH3 c0 index (p :: l) IHTREE).
        unfold get_cache_ID_path in IHTREE. discriminate.
        specialize (WFH2 p0 index (p :: l) IHTREE).
        injection WFH2; intros; subst p0.
        apply (WFH4 index p l) in IHTREE.
        apply (IHl (cache_node p) IHTREE n0 r (NatMap.add index (single_level_cache c v w s) k)
        k' index (single_level_cache c v w s) psi' c v w s F' V' C' R').
        exact WFH.
        exact H.
        apply NatMapFacts.add_eq_o. reflexivity.
        exact H1.
        reflexivity.
        exact H5.
        apply (wf3_cachelet_allocation n r F V C R c v w s).
        subst psi; exact H3. exact H6.
      }
    }
    {
      intros; apply cmp_to_uneq in H7.
      destruct l.
      {
        apply (IHl root_node WFH1 n0 r (NatMap.add a s1 k) k' index psi psi' F V C R F' V' C' R').
        exact WFH.
        unfold mlc_allocation. exact H.
        rewrite <- H0. apply NatMapFacts.add_neq_o.
        apply not_eq_sym. exact H7.
        exact H1.
        exact H4.
        exact H5.
        exact H6.
      }
      {
        destruct lambda.
        rewrite -> WFH1 in IHTREE. discriminate.
        specialize (WFH3 c a (p :: l) IHTREE).
        unfold get_cache_ID_path in IHTREE. discriminate.
        specialize (WFH2 p0 a (p :: l) IHTREE).
        injection WFH2; intros; subst p0.
        apply (WFH4 a p l) in IHTREE.
        apply (IHl (cache_node p) IHTREE n0 r (NatMap.add a s1 k) k' index psi psi' F V C R F' V' C' R').
        exact WFH.
        unfold mlc_allocation. exact H.
        rewrite <- H0. apply NatMapFacts.add_neq_o.
        apply not_eq_sym. exact H7.
        exact H1.
        exact H4.
        exact H5.
        exact H6.
      }
    }
    discriminate.
    intros; destruct (cachelet_allocation n r s0).
    discriminate.
    discriminate.
    discriminate.
    intros; destruct (NatMap.find a k).
    discriminate.
    discriminate.
  }
  intros; destruct (get_cache_ID_path lambda h_tree); discriminate.
Qed.

(* WF3 MLC Write *)
Lemma wf3_mlc_write : forall lambda h_tree k e' m0 l0 v D obs1 mu k' index psi psi'
  F V C R F' V' C' R',
  well_defined_cache_tree h_tree ->
  mlc_write k e' m0 l0 v lambda h_tree = mlc_write_valid D obs1 mu k' ->
  NatMap.find index k = Some psi ->
  NatMap.find index k' = Some psi' ->
  psi = single_level_cache F V C R ->
  psi' = single_level_cache F' V' C' R' ->
  (forall e' l', NatMap.find e' V = Some l' -> (forall c, In c l' -> ~ In c F) /\ (forall c, In c F -> ~ In c l')
  /\ NoDup(l')) /\ NoDup(F) /\ disjoint_VPT(V) ->
  (forall e' l', NatMap.find e' V' = Some l' -> (forall c, In c l' -> ~ In c F') /\ (forall c, In c F' -> ~ In c l')
  /\ NoDup(l')) /\ NoDup(F') /\ disjoint_VPT(V').
Proof.
  unfold mlc_write.
  intros lambda h_tree.
  case_eq (get_cache_ID_path lambda h_tree).
  intros l.
  generalize dependent lambda.
  induction l.
  {
    intros lambda IHTREE k e' m0 l0 v D obs1 mu k' index psi psi'
    F V C R F' V' C' R' WFH1 H H0 H1 H2 H3 H6.
    destruct (get_cache_ID_path lambda h_tree).
    injection IHTREE; intros; subst.
    unfold recursive_mlc_write in H.
    subst. destruct l0.
    destruct (NatMap.find b m0). destruct v.
    discriminate.
    injection H; intros; subst.
    rewrite -> H0 in H1.
    injection H1; intros; subst.
    exact H6.
    discriminate.
    discriminate.
  }
  {
    intros lambda IHTREE k e' m0 l0 v D obs1 mu k' index psi psi'
    F V C R F' V' C' R' WFH1 H H0 H1 H2 H3 H6.
    unfold recursive_mlc_write in H.
    fold recursive_mlc_write in H.
    case_eq (NatMap.find a k); intros.
    assert (A0 := H4). destruct (NatMap.find a k) in A0, H.
    case_eq (cc_hit_write s0 e' l0 v); intros.
    assert (A1 := H5). destruct (cc_hit_write s0 e' l0 v) in A1, H. destruct l0.
    injection H; injection A0; injection A1; intros; subst; clear A0 A1.
    assert (H7 := H5).
    destruct s; destruct s1.
    apply (cc_hit_write_f (single_level_cache c0 v0 w s) e' (address b d1) v D c
    (single_level_cache c1 v1 w0 s0) c0 v0 w s c1 v1 w0 s0) in H5.
    apply (cc_hit_write_v (single_level_cache c0 v0 w s) e' (address b d1) v D c
    (single_level_cache c1 v1 w0 s0) c0 v0 w s c1 v1 w0 s0) in H7.
    subst.
    {
      case_eq (eqb a index).
      {
        intros. apply cmp_to_eq in H2. subst.
        rewrite -> H0 in H4.
        injection H4; intros; subst c1 v1 w s.
        assert (NatMap.find index (NatMap.add index (single_level_cache F V w0 s0) k) =
        Some (single_level_cache F V w0 s0)).
        apply NatMapFacts.add_eq_o. reflexivity.
        rewrite -> H2 in H1.
        injection H1; intros; subst F' V' w0 s0.
        exact H6.
      }
      {
        intros. apply cmp_to_uneq in H2.
        assert (NatMap.find index (NatMap.add a (single_level_cache c1 v1 w0 s0) k) = NatMap.find index k).
        apply NatMapFacts.add_neq_o. exact H2.
        rewrite -> H1 in H3.
        rewrite -> H0 in H3.
        injection H3; intros; subst F' V' C' R'.
        exact H6.
      }
    }
    reflexivity.
    reflexivity.
    reflexivity.
    reflexivity.
    discriminate.
    intros; destruct (cc_hit_write s0 e' l0).
    discriminate.
    case_eq (recursive_mlc_write k e' m0 l0 v l). intros.
    assert (A1 := H7). destruct (recursive_mlc_write k e' m0 l0 v l) in A1, H.
    case_eq (cc_update s0 e' d0 l0). intros.
    assert (A2 := H8). destruct (cc_update s0 e' d0 l0) in A2, H.
    injection H; injection A0; injection A1; injection A2; intros; subst; clear A0 A1 A2.
    {
      case_eq (eqb index a).
      {
        intros. apply cmp_to_eq in H2. subst a.
        destruct s.
        assert (H9 := H8).
        destruct s1.
        apply (cc_update_f (single_level_cache c0 v0 w s) e' D l0 c (single_level_cache c1 v1 w0 s0)
        c0 v0 w s c1 v1 w0 s0) in H8.
        apply (cc_update_v (single_level_cache c0 v0 w s) e' D l0 c (single_level_cache c1 v1 w0 s0)
        c0 v0 w s c1 v1 w0 s0) in H9.
        subst.
        assert (NatMap.find index (NatMap.add index (single_level_cache c1 v1 w0 s0) m1) =
        Some (single_level_cache c1 v1 w0 s0)).
        apply NatMapFacts.add_eq_o. reflexivity.
        rewrite -> H2 in H1.
        rewrite -> H4 in H0.
        injection H0; injection H1; intros; subst.
        exact H6.
        reflexivity.
        reflexivity.
        reflexivity.
        reflexivity.
      }
      {
        intros. apply cmp_to_uneq in H2.
        assert (WFH := WFH1).
        unfold well_defined_cache_tree in WFH1.
        destruct WFH1 as [ WFH1 WFH2 ]. destruct WFH2 as [ WFH2 WFH3 ]. destruct WFH3 as [ WFH3 WFH4 ].
        destruct l.
        {
          apply (IHl root_node WFH1 k e' m0 l0 v D o mu m1 index (single_level_cache F V C R)
          (single_level_cache F' V' C' R') F V C R F' V' C' R').
          exact WFH.
          unfold mlc_write. exact H7.
          exact H0.
          rewrite <- H1. apply eq_sym.
          apply NatMapFacts.add_neq_o.
          apply not_eq_sym. exact H2.
          reflexivity.
          reflexivity.
          exact H6.
        }
        {
          destruct lambda.
          rewrite -> WFH1 in IHTREE. discriminate.
          specialize (WFH3 c0 a (p :: l) IHTREE).
          unfold get_cache_ID_path in IHTREE. discriminate.
          specialize (WFH2 p0 a (p :: l) IHTREE).
          injection WFH2; intros; subst.
          apply (WFH4 p0 p l) in IHTREE.
          apply (IHl (cache_node p) IHTREE k e' m0 l0 v D o mu m1 index (single_level_cache F V C R)
          (single_level_cache F' V' C' R') F V C R F' V' C' R').
          exact WFH.
          unfold mlc_write. exact H7.
          exact H0.
          rewrite <- H1. apply eq_sym.
          apply NatMapFacts.add_neq_o.
          apply not_eq_sym. exact H2.
          reflexivity.
          reflexivity.
          exact H6.
        }
      }
    }
    discriminate.
    intros; destruct (cc_update s0 e' d0 l0); discriminate.
    discriminate.
    intros; destruct (recursive_mlc_write k e' m0 l0 v l); discriminate.
    discriminate.
    intros; destruct (NatMap.find a k); discriminate.
  }
  intros; destruct (get_cache_ID_path lambda h_tree); discriminate.
Qed.

(* WF3 MLC Deallocation *)
Lemma clear_remapping_list_ranV : forall r l F V C R F' V' C' R' e ranV ranV',
  r <> e -> clear_remapping_list r l F V C R = Some (single_level_cache F' V' C' R') ->
  NatMap.find e V = Some ranV ->
  NatMap.find e V' = Some ranV' ->
  ranV = ranV'.
Proof.
  intros r l.
  induction l.
  {
    intros.
    unfold clear_remapping_list in H0.
    injection H0; intros; subst.
    assert (NatMap.find e (NatMap.remove r V) = NatMap.find e V).
    apply NatMapFacts.remove_neq_o; exact H.
    rewrite -> H1 in H3; rewrite -> H2 in H3;
    injection H3; intros; subst.
    reflexivity.
  }
  {
    intros.
    unfold clear_remapping_list in H0.
    fold clear_remapping_list in H0.
    destruct a.
    destruct (NatMap.find s R). destruct (cachelet_invalidation C (w, s)).
    apply (IHl ((w, s) :: F) (NatMap.add r l V) w0 (NatMap.add s (update p w
    (enclave_ID_active r)) R) F' V' C' R' e ranV ranV').
    exact H. exact H0.
    rewrite <- H1.
    apply NatMapFacts.add_neq_o; exact H.
    exact H2.
    discriminate.
    discriminate.
  }
Qed.

Lemma wf3_clear_remapping_list : forall r l F V C R F' V' C' R',
  clear_remapping_list r l F V C R = Some (single_level_cache F' V' C' R') ->
  NatMap.find r V = Some l ->
  (forall e' l', NatMap.find e' V = Some l' -> (forall c, In c l' -> ~ In c F) /\ (forall c, In c F -> ~ In c l')
  /\ NoDup(l')) /\ NoDup(F) /\ disjoint_VPT(V) ->
  (forall e' l', NatMap.find e' V' = Some l' -> (forall c, In c l' -> ~ In c F') /\ (forall c, In c F' -> ~ In c l')
  /\ NoDup(l')) /\ NoDup(F') /\ disjoint_VPT(V').
Proof.
  intros r l.
  induction l.
  {
    intros F V C R F' V' C' R' H H0 H3.
    unfold clear_remapping_list in H.
    injection H; intros; subst.
    destruct H3. split. intros.
    case_eq (eqb e' r); intros V0.
    {
      apply cmp_to_eq in V0; subst.
      assert (NatMap.find r (NatMap.remove r V) = None).
      apply NatMapFacts.remove_eq_o; reflexivity.
      rewrite -> H3 in H4. discriminate.
    }
    {
      apply cmp_to_uneq in V0.
      assert (NatMap.find (elt:=remapping_list) e' (NatMap.remove r V) = NatMap.find e' V).
      apply NatMapFacts.remove_neq_o; apply not_eq_sym; exact V0.
      rewrite -> H3 in H4; apply eq_sym in H4.
      apply (H1 e' l' H4).
    }
    destruct H2. split. exact H2.
    apply disjoint_VPT_remove. exact H3.
  }
  {
    intros F V C R F' V' C' R' H H0 H3.
    unfold clear_remapping_list in H.
    fold clear_remapping_list in H.
    destruct a.
    case_eq (NatMap.find s R). intros p H4.
    assert (A0 := H4). destruct (NatMap.find s R) in A0, H.
    case_eq (cachelet_invalidation C (w, s)). intros w0 H5.
    assert (A1 := H5). destruct (cachelet_invalidation C (w, s)) in A1, H.
    injection A0; injection A1; intros X Y; subst w1 p; clear A0 A1.
    {
      apply (IHl ((w, s) :: F) (NatMap.add r l V) w0 (NatMap.add s (update p0 w
      (enclave_ID_active r)) R) F' V' C' R').
      exact H.
      apply NatMapFacts.add_eq_o; reflexivity.
      split. intros.
      case_eq (eqb e' r); intros.
      {
        apply cmp_to_eq in H2; subst e'.
        assert (Some l' = Some l). rewrite <- H1.
        apply NatMapFacts.add_eq_o; reflexivity.
        destruct H3.
        specialize (H3 r ((w, s) :: l) H0).
        destruct H3; destruct H7.
        injection H2; intros; subst l'.
        split. intros. intros contra.
        apply in_inv in contra. destruct contra. subst c.
        apply NoDup_cons_iff in H8. destruct H8. apply H8 in H9. exact H9.
        apply H7 in H10. apply (in_cons (w, s) c l) in H9.
        apply H10 in H9. exact H9.
        split. intros. intros contra.
        apply in_inv in H9. destruct H9. subst c.
        apply NoDup_cons_iff in H8. destruct H8. apply H8 in contra. exact contra.
        apply H7 in H9. apply (in_cons (w, s) c l) in contra.
        apply H9 in contra. exact contra.
        apply NoDup_cons_iff in H8. destruct H8. exact H9.
      }
      {
        apply cmp_to_uneq in H2.
        assert (NatMap.find (elt:=remapping_list) e' (NatMap.add r l V) = NatMap.find e' V).
        apply NatMapFacts.add_neq_o; apply not_eq_sym; exact H2.
        destruct H3. rewrite -> H1 in H6. apply eq_sym in H6.
        specialize (H3 e' l' H6).
        destruct H3; destruct H8. destruct H7.
        unfold disjoint_VPT in H10.
        specialize (H10 e' l' H6 r ((w, s) :: l) H2 H0). destruct H10.
        split. intros. intros contra.
        apply in_inv in contra. destruct contra. subst c.
        apply H10 in H12.
        assert (In (w, s) ((w, s) :: l)). apply in_eq; reflexivity.
        apply H12 in H13. exact H13.
        apply H8 in H13. apply H13 in H12. exact H12.
        split. intros. intros contra.
        apply in_inv in H12. destruct H12. subst c.
        apply H10 in contra.
        assert (In (w, s) ((w, s) :: l)). apply in_eq; reflexivity.
        apply contra in H12. exact H12.
        apply H8 in H12. apply H12 in contra. exact contra. exact H9.
      }
      destruct H3; destruct H2. split. constructor.
      specialize (H1 r ((w, s) :: l) H0). destruct H1; destruct H6.
      apply H1. apply in_eq; reflexivity. exact H2.
      apply (disjoint_VPT_add r V (w, s) l). exact H0. exact H3.
    }
    discriminate.
    intros; destruct (cachelet_invalidation C (w, s)); discriminate.
    discriminate.
    intros; destruct (NatMap.find s R); discriminate.
  }
Qed.

Lemma wf3_mlc_dealloc : forall lambda h_tree state k k' index psi psi' F V C R F' V' C' R',
  well_defined_cache_tree h_tree ->
  mlc_deallocation state k lambda h_tree = Some k' ->
  NatMap.find index k = Some psi ->
  NatMap.find index k' = Some psi' ->
  psi = single_level_cache F V C R ->
  psi' = single_level_cache F' V' C' R' ->
  (forall e' l', NatMap.find e' V = Some l' -> (forall c, In c l' -> ~ In c F) /\ (forall c, In c F -> ~ In c l')
  /\ NoDup(l')) /\ NoDup(F) /\ disjoint_VPT(V) ->
  (forall e' l', NatMap.find e' V' = Some l' -> (forall c, In c l' -> ~ In c F') /\ (forall c, In c F' -> ~ In c l')
  /\ NoDup(l')) /\ NoDup(F') /\ disjoint_VPT(V').
Proof.
  unfold mlc_deallocation.
  intros lambda h_tree r.
  case_eq (get_cache_ID_path lambda h_tree).
  intros l0.
  generalize dependent lambda.
  destruct l0 as [|x].
  { intros; discriminate. }
  induction (x :: l0).
  {
    intros lambda IHTREE k k' index psi psi' F V C R
    F' V' C' R' WFH H H0 H1 H2 H3 H6.
    unfold recursive_mlc_deallocation in H.
    injection H; intros; subst k'.
    rewrite -> H0 in H1. subst psi psi'.
    injection H1; intros; subst.
    exact H6.
  }
  {
    intros lambda IHTREE k k' index psi psi' F V C R
    F' V' C' R' WFH H H0 H1 H2 H3 H6.
    unfold recursive_mlc_deallocation in H.
    fold recursive_mlc_deallocation in H.
    case_eq (NatMap.find a k). intros s H7.
    assert (A0 := H7). destruct (NatMap.find a k) in A0, H.
    case_eq (cachelet_deallocation r s0). intros s1 H8.
    assert (A1 := H8). destruct (cachelet_deallocation r s0) in A1, H.
    injection A0; injection A1; intros; subst s0 s2; clear A0 A1.
    assert (WFH1 := WFH).
    unfold well_defined_cache_tree in WFH1.
    destruct WFH1 as [ WFH1 WFH2 ]. destruct WFH2 as [ WFH2 WFH3 ]. destruct WFH3 as [ WFH3 WFH4 ].
    case_eq (eqb index a).
    {
      intros H9; apply cmp_to_eq in H9; subst a.
      rewrite -> H7 in H0.
      injection H0; intros; subst s.
      destruct s1.
      destruct l.
      {
        apply (IHl root_node WFH1 (NatMap.add index (single_level_cache c v w s) k) k' index
        (single_level_cache c v w s) psi' c v w s F' V' C' R').
        exact WFH.
        unfold mlc_deallocation. exact H.
        apply NatMapFacts.add_eq_o. reflexivity.
        exact H1.
        reflexivity.
        exact H3.
        unfold cachelet_deallocation in H8. destruct psi.
        case_eq (NatMap.find r v0). intros r1 H10.
        assert (A0 := H10). destruct (NatMap.find r v0) in A0, H8.
        injection A0; injection H2; intros X0 X1 X2 X3 X4; subst c0 v0 w0 s0 r1; clear A0.
        apply (wf3_clear_remapping_list r r0 F V C R c v w s).
        exact H8. exact H10. exact H6.
        discriminate.
        intros; destruct (NatMap.find r v0).
        discriminate.
        discriminate.
      }
      {
        destruct lambda.
        rewrite -> WFH1 in IHTREE. discriminate.
        specialize (WFH3 c0 index (p :: l) IHTREE).
        unfold get_cache_ID_path in IHTREE. discriminate.
        specialize (WFH2 p0 index (p :: l) IHTREE).
        injection WFH2; intros; subst p0.
        apply (WFH4 index p l) in IHTREE.
        apply (IHl (cache_node p) IHTREE (NatMap.add index (single_level_cache c v w s) k) k' index
        (single_level_cache c v w s) psi' c v w s F' V' C' R').
        exact WFH.
        unfold mlc_deallocation. exact H.
        apply NatMapFacts.add_eq_o. reflexivity.
        exact H1.
        reflexivity.
        exact H3.
        unfold cachelet_deallocation in H8. destruct psi.
        case_eq (NatMap.find r v0). intros r1 H10.
        assert (A0 := H10). destruct (NatMap.find r v0) in A0, H8.
        injection A0; injection H2; intros X0 X1 X2 X3 X4; subst c0 v0 w0 s0 r1; clear A0.
        apply (wf3_clear_remapping_list r r0 F V C R c v w s).
        exact H8. exact H10. exact H6.
        discriminate.
        intros; destruct (NatMap.find r v0).
        discriminate.
        discriminate.
      }
    }
    {
      intros; apply cmp_to_uneq in H4.
      destruct l.
      {
        apply (IHl root_node WFH1 (NatMap.add a s1 k) k' index
        psi psi' F V C R F' V' C' R').
        exact WFH.
        unfold mlc_deallocation. exact H.
        rewrite <- H0. apply NatMapFacts.add_neq_o.
        apply not_eq_sym. exact H4.
        exact H1.
        exact H2.
        exact H3.
        exact H6.
      }
      {
        destruct lambda.
        rewrite -> WFH1 in IHTREE. discriminate.
        specialize (WFH3 c a (p :: l) IHTREE).
        unfold get_cache_ID_path in IHTREE. discriminate.
        specialize (WFH2 p0 a (p :: l) IHTREE).
        injection WFH2; intros; subst p0.
        apply (WFH4 a p l) in IHTREE.
        apply (IHl (cache_node p) IHTREE (NatMap.add a s1 k) k' index
        psi psi' F V C R F' V' C' R').
        exact WFH.
        unfold mlc_deallocation. exact H.
        rewrite <- H0. apply NatMapFacts.add_neq_o.
        apply not_eq_sym. exact H4.
        exact H1.
        exact H2.
        exact H3.
        exact H6.
      }
    }
    discriminate.
    intros; destruct (cachelet_deallocation r s0); discriminate.
    discriminate.
    intros; destruct (NatMap.find a k); discriminate.
  }
  intros; destruct (get_cache_ID_path lambda h_tree); discriminate.
Qed.

(* WF3 Preservation *)
Lemma wf3_preservation : forall sigma obs sigma' obs',
  wf3 sigma -> <<sigma; obs>> ===> <<sigma'; obs'>> -> wf3 sigma'.
Proof.
  destruct sigma; destruct sigma'.
  unfold wf3 in *.
  intros; injection H1; intros.
  inversion H0. inversion H18; subst.
  - case_eq (NatMap.find lambda m); intros; subst.
    destruct s.
    apply (wf3_mlc_read lambda0 h_tree m e' mu l0 D delta obs0 k lambda (single_level_cache c v w s)
    (single_level_cache F V C R) c v w s F V C R).
    exact H26. exact H37. exact H3. exact H2.
    reflexivity. reflexivity.
    apply (H m mu rho p lambda c v w s).
    reflexivity. exact H3.
    apply (wf_mlc_read_none lambda0 h_tree m e' mu l0 D delta obs0 k lambda) in H3.
    rewrite -> H2 in H3.
    discriminate. exact H26. exact H37.
  - case_eq (NatMap.find lambda m); intros; subst.
    destruct s.
    apply (wf3_mlc_alloc lambda0 h_tree r_bar_val n m k lambda (single_level_cache c v w s)
    (single_level_cache F V C R) c v w s F V C R).
    exact H33. exact H43. exact H3. exact H2.
    reflexivity. reflexivity.
    apply (H m mu rho p lambda c v w s).
    reflexivity. exact H3.
    apply (wf_mlc_alloc_none lambda0 h_tree r_bar_val n m k lambda) in H43.
    rewrite -> H43 in H2.
    discriminate. exact H33. exact H3.
  - case_eq (NatMap.find lambda m); intros; subst.
    destruct s.
    apply (wf3_mlc_write lambda0 h_tree m e' m0 l0 v D obs1 mu k lambda (single_level_cache c v0 w s)
    (single_level_cache F V C R) c v0 w s F V C R).
    exact H26. exact H37. exact H3. exact H2.
    reflexivity. reflexivity.
    apply (H m m0 rho p lambda c v0 w s).
    reflexivity. exact H3.
    apply (wf_mlc_write_none lambda0 h_tree m e' m0 l0 v D obs1 mu k lambda) in H3.
    rewrite -> H2 in H3.
    discriminate. exact H26. exact H37.
  - case_eq (NatMap.find lambda m); intros; subst.
    destruct s.
    apply (wf3_mlc_dealloc lambda0 h_tree r_val m k lambda (single_level_cache c v w s)
    (single_level_cache F V C R) c v w s F V C R).
    exact H30. exact H38. exact H3. exact H2. reflexivity. reflexivity.
    apply (H m m0 rho p lambda c v w s).
    reflexivity. exact H3.
    apply (wf_mlc_dealloc_none lambda0 h_tree r_val m k lambda) in H38.
    rewrite -> H38 in H2.
    discriminate. exact H30. exact H3.
  - apply (H k mu rho p lambda F V C R).
    reflexivity. exact H2.
  - apply (H k mu rho p lambda F V C R).
    reflexivity. exact H2.
  - apply (H k mu rho p lambda F V C R).
    reflexivity. exact H2.
  - apply (H k mu rho p lambda F V C R).
    reflexivity. exact H2.
  - subst; apply (H k mu rho p lambda F V C R).
    reflexivity. exact H2.
Qed.

(* Well-Formed 4 *)
Definition wf4 (sigma: runtime_state): Prop :=
  forall k mu rho pi p l q e E,
  (sigma = runtime_state_value k mu rho pi) ->
  (NatMap.find p pi = Some (process_value (enclave_state_value e E) l q)) ->
  (e = enclave_ID_inactive \/ (exists raw_e, e = enclave_ID_active raw_e /\ NatMap.In raw_e E)).

(* WF4 Active Enclave Update *)
Lemma wf4_active_enclave_update : forall e E e' E' r,
  active_enclave_update (enclave_state_value e E) r = 
  enclave_state_valid (enclave_state_value e' E') ->
  (e = enclave_ID_inactive \/ (exists raw_e, e = enclave_ID_active raw_e /\ NatMap.In raw_e E)) ->
  (e' = enclave_ID_inactive \/ (exists raw_e', e' = enclave_ID_active raw_e' /\ NatMap.In raw_e' E')).
Proof.
  intros.
  destruct r.
  unfold active_enclave_update in H.
  case_eq (NatMap.find r E). intros. assert (A1 := H1).
  destruct (NatMap.find r E) in A1, H.
  injection A1; injection H; intros; subst; clear A1.
  right. eexists r. split.
  reflexivity.
  assert (NatMap.find r E' <> None).
  intros contra. rewrite -> H1 in contra. discriminate.
  apply NatMapFacts.in_find_iff in H2. exact H2.
  discriminate.
  intros; destruct (NatMap.find r E).
  discriminate.
  discriminate.
  unfold active_enclave_update in H.
  injection H; intros; subst.
  left; reflexivity.
Qed.

(* WF4 Enclave Creation *)
Lemma wf4_enclave_creation : forall e E e' E' mu n x y,
  enclave_creation (enclave_state_value e E) mu n x y = enclave_state_valid (enclave_state_value e' E') ->
  (e = enclave_ID_inactive \/ (exists raw_e, e = enclave_ID_active raw_e /\ NatMap.In raw_e E)) ->
  (e' = enclave_ID_inactive \/ (exists raw_e', e' = enclave_ID_active raw_e' /\ NatMap.In raw_e' E')).
Proof.
  intros.
  unfold enclave_creation in H.
  destruct x.
  case_eq (NatMap.find b mu). intros.
  assert (A0 := H1). destruct (NatMap.find b mu) in A0 , H.
  case_eq (is_all_zeroes mu b d (length (NatMapProperties.to_list d1)) y).
  intros. assert (DIS := H2).
  destruct (is_all_zeroes mu b d (length (NatMapProperties.to_list d1)) y) in DIS, H.
  unfold add_new_enclave_to_enclave_state in H.
  case_eq (NatMap.find n E). intros.
  assert (A1 := H3). destruct (NatMap.find n E) in A1, H.
  discriminate.
  discriminate.
  intros; destruct (NatMap.find n E).
  discriminate.
  injection A0; injection H; intros; subst; clear A0.
  destruct H0.
  left; exact H0.
  destruct H0. right.
  eexists x.
  destruct H0; split. exact H0.
  case_eq (eqb n x).
  intros; apply cmp_to_eq in H5; subst.
  apply NatMapFacts.add_in_iff; left; reflexivity.
  intros; apply cmp_to_uneq in H5.
  apply NatMapFacts.add_in_iff; right; exact H4.
  discriminate.
  intros; destruct (is_all_zeroes mu b d (length (NatMapProperties.to_list d1)) y).
  discriminate.
  discriminate.
  discriminate.
  intros; destruct (NatMap.find b mu).
  discriminate.
  discriminate.
Qed.

(* WF4 Enclave Elimination *)
Lemma wf4_enclave_elimination : forall e E e' E' r,
  ((enclave_elimination (enclave_state_value e E) r) = enclave_state_valid (enclave_state_value e' E')) ->
  (e = enclave_ID_inactive \/ (exists raw_e, e = enclave_ID_active raw_e /\ NatMap.In raw_e E)) ->
  (e = enclave_ID_inactive \/ (exists raw_e', e' = enclave_ID_active raw_e' /\ NatMap.In raw_e' E')).
Proof.
  intros.
  destruct H0. left. exact H0.
  destruct e'.
  {
    right.
    unfold enclave_elimination in H.
    destruct (NatMap.find r E).
    destruct e.
    case_eq (r =? r1); intros.
    assert (A0 := H1). destruct (r =? r1) in H, A0; discriminate.
    assert (A0 := H1). destruct (r =? r1) in H, A0. discriminate.
    intros. assert (H2 := H1). apply cmp_to_uneq in H1.
    destruct (r =? r1).
    discriminate.
    injection H; intros; subst.
    destruct H0.
    destruct H0.
    injection H0; intros; subst.
    eexists x.
    split. reflexivity.
    apply NatMapFacts.remove_in_iff.
    split. exact H1. exact H3.
    destruct H0.
    destruct H0.
    discriminate.
    discriminate.
  }
  {
    unfold enclave_elimination in H.
    destruct (NatMap.find r E).
    destruct e.
    destruct (r =? r0).
    discriminate.
    discriminate.
    left. reflexivity.
    discriminate.
  }
Qed.

Lemma enclave_elimination_state : forall e E e' E' r,
  ((enclave_elimination (enclave_state_value e E) r) = enclave_state_valid (enclave_state_value e' E')) ->
  e = e'.
Proof.
  intros.
  unfold enclave_elimination in H.
  destruct (NatMap.find r E).
  destruct e.
  destruct (r =? r0).
  discriminate.
  injection H; intros; subst; reflexivity.
  injection H; intros; subst; reflexivity.
  discriminate.
Qed.

Lemma enclave_elimination_in : forall e E e' E' r,
  ((enclave_elimination (enclave_state_value e E) r) = enclave_state_valid (enclave_state_value e' E')) ->
  NatMap.In r E.
Proof.
  intros. unfold enclave_elimination in H.
  case_eq (NatMap.find r E); intros.
  apply NatMapFacts.in_find_iff. intros contra.
  rewrite -> H0 in contra; discriminate.
  destruct (NatMap.find r E); discriminate.
Qed.

(* WF4 Preservation *)
Lemma wf4_preservation : forall sigma obs sigma' obs',
  wf4 sigma -> <<sigma; obs>> ===> <<sigma'; obs'>> -> wf4 sigma'.
Proof.
  destruct sigma; destruct sigma'.
  unfold wf4 in *.
  intros; injection H1; intros.
  inversion H0. inversion H18.
  - subst. case_eq (eqb p1 p2).
    intros. apply cmp_to_eq in H3. subst.
    assert (NatMap.find p2 (NatMap.add p2 (process_value e' l' q0) p)
    = Some (process_value e' l' q0)).
    apply NatMapFacts.add_eq_o; reflexivity.
    rewrite -> H2 in H3.
    injection H3; intros; subst.
    apply (H m mu rho p p2 l0 q0 e E).
    reflexivity.
    exact H19.
    intros; apply cmp_to_uneq in H3.
    assert (NatMap.find p1 (NatMap.add p2 (process_value e' l' q0) p) = NatMap.find p1 p).
    apply NatMapFacts.add_neq_o; apply not_eq_sym; exact H3.
    apply (H m mu rho p p1 l q e E).
    reflexivity.
    rewrite <- H4. exact H2.
  - subst. case_eq (eqb p1 p2).
    intros. apply cmp_to_eq in H3. subst.
    assert (NatMap.find p2 (NatMap.add p2 (process_value e' l' q0) p)
    = Some (process_value e' l' q0)).
    apply NatMapFacts.add_eq_o; reflexivity.
    rewrite -> H2 in H3.
    injection H3; intros; subst.
    destruct e0.
    assert (e0 = enclave_ID_inactive \/ (exists raw_e : raw_enclave_ID,
    e0 = enclave_ID_active raw_e /\ NatMap.In raw_e e1)).
    apply (H m mu rho p p2 l0 q0 e0 e1).
    reflexivity.
    exact H19.
    apply (wf4_enclave_creation e0 e1 e E mu n r_val2_addr r_val3).
    exact H42.
    exact H4.
    intros; apply cmp_to_uneq in H3.
    assert (NatMap.find p1 (NatMap.add p2 (process_value e' l' q0) p) = NatMap.find p1 p).
    apply NatMapFacts.add_neq_o; apply not_eq_sym; exact H3.
    apply (H m mu rho p p1 l q e E).
    reflexivity.
    rewrite <- H4. exact H2.
  - subst. case_eq (eqb p1 p2).
    intros. apply cmp_to_eq in H3. subst.
    assert (NatMap.find p2 (NatMap.add p2 (process_value e' l' q0) p)
    = Some (process_value e' l' q0)).
    apply NatMapFacts.add_eq_o; reflexivity.
    rewrite -> H2 in H3.
    injection H3; intros; subst.
    apply (H m m0 rho p p2 l0 q0 e E).
    reflexivity.
    exact H19.
    intros; apply cmp_to_uneq in H3.
    assert (NatMap.find p1 (NatMap.add p2 (process_value e' l' q0) p) = NatMap.find p1 p).
    apply NatMapFacts.add_neq_o; apply not_eq_sym; exact H3.
    apply (H m m0 rho p p1 l q e E).
    reflexivity.
    rewrite <- H4. exact H2.
  - subst. case_eq (eqb p1 p2).
    intros. apply cmp_to_eq in H3. subst.
    assert (NatMap.find p2 (NatMap.add p2 (process_value e' l' q0) p)
    = Some (process_value e' l' q0)).
    apply NatMapFacts.add_eq_o; reflexivity.
    rewrite -> H2 in H3.
    injection H3; intros; subst.
    assert (H41 := H40). destruct e0.
    apply (enclave_elimination_state e0 e1 e E r_val) in H40. subst e.
    assert (e0 = enclave_ID_inactive \/ (exists raw_e : raw_enclave_ID,
    e0 = enclave_ID_active raw_e /\ NatMap.In raw_e e1)).
    apply (H m m0 rho p p2 l0 q0 e0 e1).
    reflexivity.
    exact H19.
    apply (wf4_enclave_elimination e0 e1 e0 E r_val).
    exact H41. exact H4.
    intros; apply cmp_to_uneq in H3.
    assert (NatMap.find p1 (NatMap.add p2 (process_value e' l' q0) p) = NatMap.find p1 p).
    apply NatMapFacts.add_neq_o; apply not_eq_sym; exact H3.
    apply (H m m0 rho p p1 l q e E).
    reflexivity.
    rewrite <- H4. exact H2.
  - subst. case_eq (eqb p1 p2).
    intros. apply cmp_to_eq in H3. subst.
    assert (NatMap.find p2 (NatMap.add p2 (process_value e' l' q0) p)
    = Some (process_value e' l' q0)).
    apply NatMapFacts.add_eq_o; reflexivity.
    rewrite -> H2 in H3.
    injection H3; intros; subst.
    destruct e0.
    assert (e0 = enclave_ID_inactive \/ (exists raw_e : raw_enclave_ID,
    e0 = enclave_ID_active raw_e /\ NatMap.In raw_e e1)).
    apply (H k mu rho p p2 l0 q0 e0 e1).
    reflexivity.
    exact H19.
    apply (wf4_active_enclave_update e0 e1 e E (enclave_ID_active r_val)).
    exact H37.
    exact H4.
    intros; apply cmp_to_uneq in H3.
    assert (NatMap.find p1 (NatMap.add p2 (process_value e' l' q0) p) = NatMap.find p1 p).
    apply NatMapFacts.add_neq_o; apply not_eq_sym; exact H3.
    apply (H k mu rho p p1 l q e E).
    reflexivity.
    rewrite <- H4. exact H2.
  - subst. case_eq (eqb p1 p2).
    intros. apply cmp_to_eq in H3. subst.
    assert (NatMap.find p2 (NatMap.add p2 (process_value e' l' q0) p)
    = Some (process_value e' l' q0)).
    apply NatMapFacts.add_eq_o; reflexivity.
    rewrite -> H2 in H3.
    injection H3; intros; subst.
    destruct e0.
    assert (e0 = enclave_ID_inactive \/ (exists raw_e : raw_enclave_ID,
    e0 = enclave_ID_active raw_e /\ NatMap.In raw_e e1)).
    apply (H k mu rho p p2 l0 q0 e0 e1).
    reflexivity.
    exact H19.
    apply (wf4_active_enclave_update e0 e1 e E enclave_ID_inactive).
    exact H36.
    exact H4.
    intros; apply cmp_to_uneq in H3.
    assert (NatMap.find p1 (NatMap.add p2 (process_value e' l' q0) p) = NatMap.find p1 p).
    apply NatMapFacts.add_neq_o; apply not_eq_sym; exact H3.
    apply (H k mu rho p p1 l q e E).
    reflexivity.
    rewrite <- H4. exact H2.
  - subst. case_eq (eqb p1 p2).
    intros. apply cmp_to_eq in H3. subst.
    assert (NatMap.find p2 (NatMap.add p2 (process_value e' l' q0) p)
    = Some (process_value e' l' q0)).
    apply NatMapFacts.add_eq_o; reflexivity.
    rewrite -> H2 in H3.
    injection H3; intros; subst.
    apply (H k mu rho p p2 l0 q0 e E).
    reflexivity.
    exact H19.
    intros; apply cmp_to_uneq in H3.
    assert (NatMap.find p1 (NatMap.add p2 (process_value e' l' q0) p) = NatMap.find p1 p).
    apply NatMapFacts.add_neq_o; apply not_eq_sym; exact H3.
    apply (H k mu rho p p1 l q e E).
    reflexivity.
    rewrite <- H4. exact H2.
  - subst. case_eq (eqb p1 p2).
    intros. apply cmp_to_eq in H3. subst.
    assert (NatMap.find p2 (NatMap.add p2 (process_value e' l' q0) p)
    = Some (process_value e' l' q0)).
    apply NatMapFacts.add_eq_o; reflexivity.
    rewrite -> H2 in H3.
    injection H3; intros; subst.
    apply (H k mu rho p p2 l0 q0 e E).
    reflexivity.
    exact H19.
    intros; apply cmp_to_uneq in H3.
    assert (NatMap.find p1 (NatMap.add p2 (process_value e' l' q0) p) = NatMap.find p1 p).
    apply NatMapFacts.add_neq_o; apply not_eq_sym; exact H3.
    apply (H k mu rho p p1 l q e E).
    reflexivity.
    rewrite <- H4. exact H2.
  - subst. case_eq (eqb p1 p2).
    intros. apply cmp_to_eq in H3. subst.
    assert (NatMap.find p2 (NatMap.add p2 (process_value e0 l0 q') p)
    = Some (process_value e0 l0 q')).
    apply NatMapFacts.add_eq_o; reflexivity.
    rewrite -> H2 in H3.
    injection H3; intros; subst.
    apply (H k mu rho p p2 l0 q0 e E).
    reflexivity. exact H10.
    intros; apply cmp_to_uneq in H3.
    assert (NatMap.find p1 (NatMap.add p2 (process_value e0 l0 q') p) = NatMap.find p1 p).
    apply NatMapFacts.add_neq_o; apply not_eq_sym; exact H3.
    apply (H k mu rho p p1 l q e E).
    reflexivity.
    rewrite <- H4. exact H2.
Qed.

(* Well-Formed 5 *)
Definition wf5 (sigma: runtime_state): Prop :=
  forall k mu rho pi p l q e0 E,
  (sigma = runtime_state_value k mu rho pi) ->
  (NatMap.find p pi = Some (process_value (enclave_state_value e0 E) l q)) ->
  (exists index F V C R, NatMap.find index k = Some (single_level_cache F V C R) /\
  (forall e, e0 = enclave_ID_active e -> NatMap.In e V)).

(* WF5 MLC Read *)
Lemma wf_mlc_read_some : forall lambda h_tree k e' m0 l0 D obs1 mu k' index,
  well_defined_cache_tree h_tree ->
  mlc_read k e' m0 l0 lambda h_tree = mlc_read_valid D obs1 mu k' ->
  NatMap.find index k <> None ->
  NatMap.find index k' <> None.
Proof.
  unfold mlc_read.
  intros lambda h_tree.
  case_eq (get_cache_ID_path lambda h_tree).
  intros l.
  generalize dependent lambda.
  induction l.
  {
    intros lambda IHTREE k e' m0 l0 D obs1 mu k' index WFH; intros.
    unfold recursive_mlc_read in H.
    destruct l0.
    destruct (NatMap.find b m0).
    injection H; intros; subst.
    exact H0.
    discriminate.
  }
  {
    intros lambda IHTREE k e' m0 l0 D obs1 mu k' index WFH; intros.
    unfold recursive_mlc_read in H.
    fold recursive_mlc_read in H.
    case_eq (NatMap.find a k). intros.
    assert (A0 := H1). destruct (NatMap.find a k) in A0, H.
    case_eq (cc_hit_read s0 e' l0). intros.
    assert (A1 := H2). destruct (cc_hit_read s0 e' l0) in A1, H.
    injection H; injection A0; injection A1; intros; subst; clear A0 A1.
    assert (H3 := H2).
    destruct s; destruct s1.
    {
      case_eq (eqb a index).
      {
        intros. apply cmp_to_eq in H4. subst.
        intros contra.
        assert (None = Some (single_level_cache c1 v0 w0 s0)).
        rewrite <- contra. apply NatMapFacts.add_eq_o; reflexivity.
        discriminate.
      }
      {
        intros. apply cmp_to_uneq in H4.
        intros contra. assert (NatMap.find index (NatMap.add a (single_level_cache
        c1 v0 w0 s0) k) = NatMap.find index k).
        apply NatMapFacts.add_neq_o; exact H4.
        rewrite <- H5 in H0. rewrite -> contra in H0. apply H0; reflexivity.
      }
    }
    discriminate.
    intros; destruct (cc_hit_read s0 e' l0).
    discriminate.
    case_eq (recursive_mlc_read k e' m0 l0 l). intros.
    assert (A1 := H3). destruct (recursive_mlc_read k e' m0 l0 l) in A1, H.
    case_eq (cc_update s0 e' d1 l0). intros.
    assert (A2 := H4). destruct (cc_update s0 e' d1 l0) in A2, H.
    injection H; injection A0; injection A1; injection A2; intros; subst; clear A0 A1 A2.
    {
      case_eq (eqb index a).
      {
        intros. apply cmp_to_eq in H5. subst a.
        intros contra.
        assert (None = Some s1).
        rewrite <- contra. apply NatMapFacts.add_eq_o; reflexivity.
        discriminate.
      }
      {
        intros. apply cmp_to_uneq in H5.
        assert (WFH1 := WFH).
        unfold well_defined_cache_tree in WFH1.
        destruct WFH1 as [ WFH1 WFH2 ]. destruct WFH2 as [ WFH2 WFH3 ]. destruct WFH3 as [ WFH3 WFH4 ].
        destruct l.
        {
          assert (NatMap.find index m <> None).
          apply (IHl root_node WFH1 k e' m0 l0 D obs1 o m index).
          exact WFH.
          unfold mlc_write; exact H3.
          exact H0.
          intros contra. assert (NatMap.find index (NatMap.add a s1 m) = NatMap.find index m).
          apply NatMapFacts.add_neq_o; apply not_eq_sym; exact H5.
          rewrite <- H7 in H6. rewrite -> contra in H6. apply H6; reflexivity.
        }
        {
          destruct lambda.
          rewrite -> WFH1 in IHTREE. discriminate.
          specialize (WFH3 c0 a (p :: l) IHTREE).
          unfold get_cache_ID_path in IHTREE. discriminate.
          specialize (WFH2 p0 a (p :: l) IHTREE).
          injection WFH2; intros; subst p0.
          apply (WFH4 a p l) in IHTREE.
          assert (NatMap.find index m <> None).
          apply (IHl (cache_node p) IHTREE k e' m0 l0 D obs1 o m index).
          exact WFH.
          unfold mlc_write; exact H3.
          exact H0.
          intros contra. assert (NatMap.find index (NatMap.add a s1 m) = NatMap.find index m).
          apply NatMapFacts.add_neq_o; apply not_eq_sym; exact H5.
          rewrite <- H7 in H6. rewrite -> contra in H6. apply H6; reflexivity.
        }
      }
    }
    discriminate.
    intros; destruct (cc_update s0 e' d1 l0).
    discriminate.
    discriminate.
    discriminate.
    intros; destruct (recursive_mlc_read k e' m0 l0 l).
    discriminate.
    discriminate.
    discriminate.
    intros; destruct (NatMap.find a k).
    discriminate.
    discriminate.
  }
  intros; destruct (get_cache_ID_path lambda h_tree).
  discriminate.
  discriminate.
Qed.

(* WF5 MLC Allocation *)
Lemma non_empty_list_induction : forall (x : nat) (l : list nat),
  exists a l', x :: l = l' ++ (a :: nil).
Proof.
  intros x l.
  eexists (last (x :: l) 0); eexists (removelast (x :: l)).
  apply app_removelast_last.
  intros contra; discriminate.
Qed.

Lemma non_empty_list_inductive_case : forall (a : nat) x1 x0,
  exists l, a :: x1 ++ x0 :: nil = a :: l.
Proof.
  intros. eexists (x1 ++ x0 :: nil). reflexivity.
Qed.

Lemma wf5_mlc_alloc : forall lambda h_tree r_bar_val n k k' r,
  well_defined_cache_tree h_tree ->
  mlc_allocation r_bar_val n k lambda h_tree = Some k' ->
  (exists index F V C R, NatMap.find index k = Some (single_level_cache F V C R) /\
  (forall e', r = enclave_ID_active e' -> NatMap.In e' V)) ->
  (exists index F V C R, NatMap.find index k' = Some (single_level_cache F V C R) /\
  (forall e', r = enclave_ID_active e' -> NatMap.In e' V)).
Proof.
  unfold mlc_allocation.
  intros lambda h_tree.
  case_eq (get_cache_ID_path lambda h_tree).
  intros l0.
  generalize dependent lambda.
  destruct l0 as [|x].
  { intros; discriminate. }
  assert (exists a l', x :: l0 = l' ++ (a :: nil)).
  apply non_empty_list_induction.
  destruct H. destruct H.
  rewrite -> H. clear H. induction x1.
  {
    intros. simpl in *.
    destruct r_bar_val. discriminate.
    case_eq (NatMap.find x0 k); intros.
    assert (A0 := H3); destruct (NatMap.find x0 k) in A0, H1.
    case_eq (cachelet_allocation n0 n s0); intros.
    assert (A1 := H4); destruct (cachelet_allocation n0 n s0) in A1, H1.
    injection A0; injection A1; injection H1; intros; subst; clear A0 A1.
    destruct s; destruct s1.
    destruct H2 as (index & x2 & x3 & x4 & x5 & H2 & H5).
    case_eq (eqb x0 index); intros.
    {
      apply cmp_to_eq in H6; subst.
      eexists index; eexists c0; eexists v0; eexists w0; eexists s0.
      rewrite -> H2 in H3; injection H3; intros; subst.
      split. apply NatMapFacts.add_eq_o; reflexivity. intros.
      apply (cachelet_allocation_v_subset n0 n c v w s c0 v0 w0 s0 e' H4).
      apply H5. exact H6.
    }
    {
      apply cmp_to_uneq in H6.
      eexists index; eexists x2; eexists x3; eexists x4; eexists x5.
      split. rewrite <- H2.
      apply NatMapFacts.add_neq_o; exact H6. exact H5.
    }
    discriminate.
    destruct (cachelet_allocation n0 n s0); discriminate.
    discriminate.
    destruct (NatMap.find x0 k); discriminate.
  }
  {
    intros.
    assert ((a :: x1) ++ x0 :: nil = a :: (x1 ++ x0 :: nil)).
    auto. rewrite -> H3 in *. clear H3.
    unfold recursive_mlc_allocation in H1.
    fold recursive_mlc_allocation in H1.
    destruct r_bar_val. discriminate.
    case_eq (NatMap.find a k); intros.
    assert (A0 := H3); destruct (NatMap.find a k) in A0, H1.
    case_eq (cachelet_allocation n0 n s0); intros.
    assert (A1 := H4); destruct (cachelet_allocation n0 n s0) in A1, H1.
    injection A0; injection A1; intros; subst; clear A0 A1.
    destruct s; destruct s1.
    assert (exists l, a :: x1 ++ x0 :: nil = a :: l).
    apply non_empty_list_inductive_case. destruct H5.
    assert (x2 = x1 ++ x0 :: nil).
    injection H5; intros; subst. reflexivity.
    rewrite <- H6 in *. clear H5 H6.
    assert (WFH1 := H0). unfold well_defined_cache_tree in WFH1.
    destruct WFH1 as [ WFH1 WFH2 ]. destruct WFH2 as [ WFH2 WFH3 ]. destruct WFH3 as [ WFH3 WFH4 ].
    destruct x2.
    {
      apply (IHx1 root_node WFH1 r_bar_val n (NatMap.add a (single_level_cache
      c0 v0 w0 s0) k) k' r H0 H1).
      destruct H2 as (index & F & V & C & R & H2 & H5).
      case_eq (eqb index a); intros.
      apply cmp_to_eq in H6; subst a.
      eexists index; eexists c0; eexists v0; eexists w0; eexists s0.
      split. apply NatMapFacts.add_eq_o; reflexivity.
      rewrite -> H2 in H3; injection H3; intros; subst.
      apply (cachelet_allocation_v_subset n0 n c v w s c0 v0 w0 s0 e' H4).
      apply H5; reflexivity.
      apply cmp_to_uneq in H6.
      eexists index; eexists F; eexists V; eexists C; eexists R.
      split. rewrite <- H2.
      apply NatMapFacts.add_neq_o; apply not_eq_sym; exact H6.
      exact H5.
    }
    {
      destruct lambda.
      rewrite -> WFH1 in H. discriminate.
      specialize (WFH3 c1 a (p :: x2) H).
      unfold get_cache_ID_path in H. discriminate.
      specialize (WFH2 p0 a (p :: x2) H).
      injection WFH2; intros; subst p0.
      apply (WFH4 a p x2) in H.
      apply (IHx1 (cache_node p) H r_bar_val n (NatMap.add a (single_level_cache
      c0 v0 w0 s0) k) k' r H0 H1).
      destruct H2 as (index & F & V & C & R & H2 & H5).
      case_eq (eqb index a); intros.
      apply cmp_to_eq in H6; subst a.
      eexists index; eexists c0; eexists v0; eexists w0; eexists s0.
      split. apply NatMapFacts.add_eq_o; reflexivity.
      rewrite -> H2 in H3; injection H3; intros; subst.
      apply (cachelet_allocation_v_subset n0 n c v w s c0 v0 w0 s0 e' H4).
      apply H5; reflexivity.
      apply cmp_to_uneq in H6.
      eexists index; eexists F; eexists V; eexists C; eexists R.
      split. rewrite <- H2.
      apply NatMapFacts.add_neq_o; apply not_eq_sym; exact H6.
      exact H5.
    }
    discriminate.
    destruct (cachelet_allocation n0 n s0); discriminate.
    discriminate.
    destruct (NatMap.find a k); discriminate.
  }
  intros; discriminate.
Qed.

(* WF5 MLC Write *)
Lemma mlc_write_v : forall lambda h_tree k e' m0 l0 v D obs1 mu k' index F V C R F' V' C' R',
  well_defined_cache_tree h_tree ->
  mlc_write k e' m0 l0 v lambda h_tree = mlc_write_valid D obs1 mu k' ->
  NatMap.find index k = Some (single_level_cache F V C R) ->
  NatMap.find index k' = Some (single_level_cache F' V' C' R') ->
  V = V'.
Proof.
  unfold mlc_write.
  intros lambda h_tree.
  case_eq (get_cache_ID_path lambda h_tree).
  intros l.
  generalize dependent lambda.
  induction l.
  {
    intros.
    unfold recursive_mlc_write in H1.
    destruct l0. destruct (NatMap.find b m0). destruct v.
    discriminate.
    injection H1; intros; subst.
    rewrite -> H2 in H3.
    injection H3; intros; subst F' V' C' R'.
    reflexivity.
    discriminate.
  }
  {
    intros.
    unfold recursive_mlc_write in H1.
    fold recursive_mlc_write in H1.
    case_eq (NatMap.find a k). intros.
    assert (A0 := H4). destruct (NatMap.find a k) in A0, H1.
    injection A0; intros; subst s0.
    case_eq (cc_hit_write s e' l0 v). intros.
    assert (A1 := H5). destruct (cc_hit_write s e' l0 v) in A1, H1.
    destruct l0. injection A1; injection H1; intros; subst; clear A0 A1.
    destruct s; destruct s0.
    apply (cc_hit_write_v (single_level_cache c0 v0 w s) e' (address b d1) v d c
    (single_level_cache c1 v1 w0 s0) c0 v0 w s c1 v1 w0 s0) in H5.
    subst v1.
    {
      case_eq (eqb index a); intros.
      {
        apply cmp_to_eq in H5; subst a.
        rewrite -> H2 in H4.
        injection H4; intros; subst.
        assert (Some (single_level_cache F' V' C' R') = Some (single_level_cache c1 v0 w0 s0)).
        rewrite <- H3. apply NatMapFacts.add_eq_o; reflexivity.
        injection H5; intros; subst.
        reflexivity.
      }
      {
        apply cmp_to_uneq in H5.
        assert (NatMap.find index k = Some (single_level_cache F' V' C' R')).
        rewrite <- H3. apply eq_sym.
        apply NatMapFacts.add_neq_o; apply not_eq_sym; exact H5.
        rewrite -> H2 in H6.
        injection H6; intros; subst.
        reflexivity.
      }
    }
    reflexivity.
    reflexivity.
    discriminate.
    intros; destruct (cc_hit_write s e' l0 v).
    discriminate.
    clear A0.
    case_eq (recursive_mlc_write k e' m0 l0 v l); intros.
    assert (A0 := H6). destruct (recursive_mlc_write k e' m0 l0 v l) in A0, H1.
    case_eq (cc_update s e' d0 l0); intros.
    assert (A1 := H7). destruct (cc_update s e' d0 l0) in A1, H1.
    injection A0; injection A1; injection H1; intros; subst; clear A0 A1.
    {
      case_eq (eqb index a); intros.
      {
        apply cmp_to_eq in H8. subst a.
        destruct s. rewrite -> H2 in H4; injection H4; intros; subst c0 v0 w s.
        destruct s0.
        apply (cc_update_v (single_level_cache F V C R) e' d l0 c (single_level_cache c0 v0 w s)
        F V C R c0 v0 w s) in H7.
        subst v0.
        assert (NatMap.find index (NatMap.add index (single_level_cache c0 V w s) m1) =
        Some (single_level_cache c0 V w s)).
        apply NatMapFacts.add_eq_o. reflexivity.
        rewrite -> H3 in H7; injection H7; intros; subst c0 V' w s.
        reflexivity.
        reflexivity.
        reflexivity.
      }
      {
        apply cmp_to_uneq in H8.
        assert (WFH := H0).
        unfold well_defined_cache_tree in H0.
        destruct H0 as [ WFH1 ]. destruct H0 as [ WFH2 ]. destruct H0 as [ WFH3 ].
        destruct l.
        {
          apply (IHl root_node WFH1 k e' m0 l0 v d o m m1 index F V C R F' V' C' R').
          exact WFH. exact H6. exact H2.
          rewrite <- H3. apply eq_sym.
          apply NatMapFacts.add_neq_o.
          apply not_eq_sym. exact H8.
        }
        {
          destruct lambda.
          rewrite -> WFH1 in H. discriminate.
          specialize (WFH3 c0 a (p :: l) H).
          unfold get_cache_ID_path in H. discriminate.
          specialize (WFH2 p0 a (p :: l) H).
          injection WFH2; intros; subst.
          apply (H0 p0 p l) in H.
          apply (IHl (cache_node p) H k e' m0 l0 v d o m m1 index F V C R F' V' C' R').
          exact WFH. exact H6. exact H2.
          rewrite <- H3. apply eq_sym.
          apply NatMapFacts.add_neq_o.
          apply not_eq_sym. exact H8.
        }
      }
    }
    discriminate.
    destruct (cc_update s e' d0 l0); discriminate.
    discriminate.
    destruct (recursive_mlc_write k e' m0 l0 v l); discriminate.
    discriminate.
    intros; destruct (NatMap.find a k); discriminate.
  }
  intros; destruct (get_cache_ID_path lambda h_tree); discriminate.
Qed.

Lemma wf_mlc_write_some : forall lambda h_tree k e' m0 l0 v D obs1 mu k' index,
  well_defined_cache_tree h_tree ->
  mlc_write k e' m0 l0 v lambda h_tree = mlc_write_valid D obs1 mu k' ->
  NatMap.find index k <> None ->
  NatMap.find index k' <> None.
Proof.
  unfold mlc_write.
  intros lambda h_tree.
  case_eq (get_cache_ID_path lambda h_tree).
  intros l.
  generalize dependent lambda.
  induction l.
  {
    intros.
    unfold recursive_mlc_write in H1.
    destruct l0.
    destruct (NatMap.find b m0).
    destruct v.
    discriminate.
    injection H1; intros; subst.
    exact H2.
    discriminate.
  }
  {
    intros.
    unfold recursive_mlc_write in H1.
    fold recursive_mlc_write in H1.
    case_eq (NatMap.find a k). intros.
    assert (A0 := H3). destruct (NatMap.find a k) in A0, H1.
    case_eq (cc_hit_write s0 e' l0 v). intros.
    assert (A1 := H4). destruct (cc_hit_write s0 e' l0 v) in A1, H1.
    destruct l0.
    injection H1; injection A0; injection A1; intros; subst; clear A0 A1.
    assert (H5 := H4).
    destruct s; destruct s1.
    {
      case_eq (eqb a index).
      {
        intros. apply cmp_to_eq in H6. subst.
        intros contra.
        assert (None = Some (single_level_cache c1 v1 w0 s0)).
        rewrite <- contra. apply NatMapFacts.add_eq_o; reflexivity.
        discriminate.
      }
      {
        intros. apply cmp_to_uneq in H6.
        intros contra. assert (NatMap.find index (NatMap.add a (single_level_cache
        c1 v1 w0 s0) k) = NatMap.find index k).
        apply NatMapFacts.add_neq_o; exact H6.
        rewrite <- H7 in H2. rewrite -> contra in H2. apply H2; reflexivity.
      }
    }
    discriminate.
    intros; destruct (cc_hit_write s0 e' l0 v).
    discriminate.
    case_eq (recursive_mlc_write k e' m0 l0 v l). intros.
    assert (A1 := H5). destruct (recursive_mlc_write k e' m0 l0 v l) in A1, H1.
    case_eq (cc_update s0 e' d0 l0). intros.
    assert (A2 := H6). destruct (cc_update s0 e' d0 l0) in A2, H1.
    injection H1; injection A0; injection A1; injection A2; intros; subst; clear A0 A1 A2.
    {
      case_eq (eqb index a).
      {
        intros. apply cmp_to_eq in H7. subst a.
        intros contra.
        assert (None = Some s1).
        rewrite <- contra. apply NatMapFacts.add_eq_o; reflexivity.
        discriminate.
      }
      {
        intros. apply cmp_to_uneq in H7.
        assert (WFH1 := H0).
        unfold well_defined_cache_tree in WFH1.
        destruct WFH1 as [ WFH1 WFH2 ]. destruct WFH2 as [ WFH2 WFH3 ]. destruct WFH3 as [ WFH3 WFH4 ].
        destruct l.
        {
          assert (NatMap.find index m1 <> None).
          apply (IHl root_node WFH1 k e' m0 l0 v D o mu m1 index).
          exact H0. exact H5. exact H2.
          intros contra. assert (NatMap.find index (NatMap.add a s1 m1) = NatMap.find index m1).
          apply NatMapFacts.add_neq_o; apply not_eq_sym; exact H7.
          rewrite -> H9 in contra. rewrite -> contra in H8. apply H8; reflexivity.
        }
        {
          destruct lambda.
          rewrite -> WFH1 in H. discriminate.
          specialize (WFH3 c0 a (p :: l) H).
          unfold get_cache_ID_path in H. discriminate.
          specialize (WFH2 p0 a (p :: l) H).
          injection WFH2; intros; subst p0.
          apply (WFH4 a p l) in H.
          assert (NatMap.find index m1 <> None).
          apply (IHl (cache_node p) H k e' m0 l0 v D o mu m1 index).
          exact H0. exact H5. exact H2.
          intros contra. assert (NatMap.find index (NatMap.add a s1 m1) = NatMap.find index m1).
          apply NatMapFacts.add_neq_o; apply not_eq_sym; exact H7.
          rewrite -> H9 in contra. rewrite -> contra in H8. apply H8; reflexivity.
        }
      }
    }
    discriminate.
    intros; destruct (cc_update s0 e' d0 l0); discriminate.
    discriminate.
    intros; destruct (recursive_mlc_write k e' m0 l0 v l); discriminate.
    discriminate.
    intros; destruct (NatMap.find a k); discriminate.
  }
  intros; destruct (get_cache_ID_path lambda h_tree); discriminate.
Qed.

(* WF5 MLC Deallocation *)

Lemma wf5_mlc_dealloc1 : forall lambda h_tree e k k' r,
  well_defined_cache_tree h_tree ->
  mlc_deallocation e k lambda h_tree = Some k' ->
  (exists index F V C R, NatMap.find index k = Some (single_level_cache F V C R) /\
  (forall e', r = enclave_ID_active e' -> NatMap.In e' V)) ->
  (forall e_, r = enclave_ID_active e_ -> e <> e_) ->
  (exists index F V C R, NatMap.find index k' = Some (single_level_cache F V C R) /\
  (forall e', r = enclave_ID_active e' -> NatMap.In e' V)).
Proof.
  unfold mlc_deallocation.
  intros lambda h_tree.
  case_eq (get_cache_ID_path lambda h_tree).
  intros l0.
  generalize dependent lambda.
  destruct l0 as [|x].
  { intros; discriminate. }
  induction (x :: l0).
  {
    intros.
    unfold recursive_mlc_deallocation in H1.
    injection H1; intros; subst.
    exact H2.
  }
  {
    intros.
    unfold recursive_mlc_deallocation in H1.
    fold recursive_mlc_deallocation in H1.
    case_eq (NatMap.find a k); intros.
    assert (A0 := H4); destruct (NatMap.find a k) in A0, H1.
    case_eq (cachelet_deallocation e s0); intros.
    assert (A1 := H5); destruct (cachelet_deallocation e s0) in A1, H1.
    injection A0; injection A1; intros; subst; clear A0 A1.
    destruct s; destruct s1.
    assert (WFH1 := H0). unfold well_defined_cache_tree in WFH1.
    destruct WFH1 as [ WFH1 WFH2 ]. destruct WFH2 as [ WFH2 WFH3 ]. destruct WFH3 as [ WFH3 WFH4 ].
    destruct l.
    {
      apply (IHl root_node WFH1 e (NatMap.add a (single_level_cache
      c0 v0 w0 s0) k) k' r H0 H1).
      destruct H2 as (index & F & V & C & R & H2 & H6).
      case_eq (eqb index a); intros.
      apply cmp_to_eq in H7; subst a.
      eexists index; eexists c0; eexists v0; eexists w0; eexists s0.
      split. apply NatMapFacts.add_eq_o; reflexivity.
      rewrite -> H2 in H4; injection H4; intros; subst.
      apply (cachelet_deallocation_v e (single_level_cache c v w s)
      (single_level_cache c0 v0 w0 s0) c v w s c0 v0 w0 s0 e' H5).
      reflexivity. reflexivity. apply H3. reflexivity.
      apply H6; reflexivity.
      apply cmp_to_uneq in H7.
      eexists index; eexists F; eexists V; eexists C; eexists R.
      split. rewrite <- H2.
      apply NatMapFacts.add_neq_o; apply not_eq_sym; exact H7.
      exact H6. exact H3.
    }
    {
      destruct lambda.
      rewrite -> WFH1 in H. discriminate.
      specialize (WFH3 c1 a (p :: l) H).
      unfold get_cache_ID_path in H. discriminate.
      specialize (WFH2 p0 a (p :: l) H).
      injection WFH2; intros; subst p0.
      apply (WFH4 a p l) in H.
      apply (IHl (cache_node p) H e (NatMap.add a (single_level_cache
      c0 v0 w0 s0) k) k' r H0 H1).
      destruct H2 as (index & F & V & C & R & H2 & H6).
      case_eq (eqb index a); intros.
      apply cmp_to_eq in H7; subst a.
      eexists index; eexists c0; eexists v0; eexists w0; eexists s0.
      split. apply NatMapFacts.add_eq_o; reflexivity.
      rewrite -> H2 in H4; injection H4; intros; subst.
      apply (cachelet_deallocation_v e (single_level_cache c v w s)
      (single_level_cache c0 v0 w0 s0) c v w s c0 v0 w0 s0 e' H5).
      reflexivity. reflexivity. apply H3. reflexivity.
      apply H6; reflexivity.
      apply cmp_to_uneq in H7.
      eexists index; eexists F; eexists V; eexists C; eexists R.
      split. rewrite <- H2.
      apply NatMapFacts.add_neq_o; apply not_eq_sym; exact H7.
      exact H6. exact H3.
    }
    discriminate.
    destruct (cachelet_deallocation e s0); discriminate.
    discriminate.
    destruct (NatMap.find a k); discriminate.
  }
  intros; discriminate.
Qed.

(* WF5 Preservation *)
Lemma any_active_enclave_not_contained : forall sigma k mu rho p p1 e0 E l q r_val,
  sigma = runtime_state_value k mu rho p ->
  disjoint_enclave_states sigma ->
  active_enclave_contained sigma ->
  (NatMap.find p1 p = Some (process_value (enclave_state_value e0 E) l q)) ->
  (forall e, e0 = enclave_ID_active e -> r_val <> e) ->
  NatMap.In r_val E ->
  (forall p1' e0' E' l' q', NatMap.find p1' p = Some (process_value
  (enclave_state_value (enclave_ID_active e0') E') l' q') ->
  forall e, enclave_ID_active e0' = enclave_ID_active e -> r_val <> e).
Proof.
  intros sigma k mu rho p p1 e0 E l q r_val H H0 H1 H2 H3 H12;
  intros; subst sigma.
  unfold disjoint_enclave_states in H0.
  unfold active_enclave_contained in H1.
  injection H5; intros; subst. destruct e0.
  case_eq (eqb p1 p1'); intros.
  apply cmp_to_eq in H; subst.
  rewrite -> H2 in H4.
  injection H4; intros; subst.
  apply H3; reflexivity.
  apply cmp_to_uneq in H.
  assert (runtime_state_value k mu rho p = runtime_state_value k mu rho p).
  reflexivity.
  specialize (H0 k mu rho p p1 l q (enclave_ID_active r)
  E p1' l' q' (enclave_ID_active e) E' H6 H2 H4 H).
  assert (enclave_ID_active r = enclave_ID_active r).
  reflexivity. specialize (H3 r H7).
  specialize (H1 k mu rho p p1 l q (enclave_ID_active r)
  E H6 H2) as H1'.
  specialize (H1 k mu rho p p1' l' q' (enclave_ID_active e) E' H6 H4).
  destruct H1; destruct H1'. discriminate. discriminate. discriminate.
  specialize (H8 r H7). specialize (H1 e H5). clear H5 H7 H6.
  destruct H0. intros contra. subst.
  apply H5 in H1. apply H1 in H12. exact H12.
  case_eq (eqb p1 p1'); intros.
  apply cmp_to_eq in H; subst.
  rewrite -> H2 in H4.
  injection H4; intros; subst. discriminate.
  apply cmp_to_uneq in H.
  assert (runtime_state_value k mu rho p = runtime_state_value k mu rho p).
  reflexivity.
  specialize (H0 k mu rho p p1 l q enclave_ID_inactive
  E p1' l' q' (enclave_ID_active e) E' H6 H2 H4 H).
  specialize (H1 k mu rho p p1 l q enclave_ID_inactive
  E H6 H2) as H1'.
  specialize (H1 k mu rho p p1' l' q' (enclave_ID_active e) E' H6 H4).
  destruct H1; destruct H1'. discriminate. discriminate.
  specialize (H1 e H5). clear H5 H7 H6.
  destruct H0. intros contra. subst.
  apply H5 in H1. apply H1 in H12. exact H12.
  specialize (H1 e H5). clear H5 H7 H6.
  destruct H0. intros contra. subst.
  apply H5 in H1. apply H1 in H12. exact H12. 
Qed.

Lemma wf5_preservation : forall sigma obs sigma' obs',
  wf_enclave_state sigma -> wf5 sigma -> wf3 sigma -> <<sigma; obs>> ===> <<sigma'; obs'>> -> wf5 sigma'.
Proof.
  destruct sigma; destruct sigma'.
  unfold wf5 in *. unfold wf3 in *.
  intros obs' HE. intros.
  unfold wf_enclave_state in HE. assert (HE0 := HE).
  intros; injection H2; intros.
  inversion H1. inversion H19.
  - subst.
    assert (exists index F V C R, NatMap.find index m = Some (single_level_cache F V C R) /\
    (forall e, e0 = enclave_ID_active e -> NatMap.In e V)).
    case_eq (eqb p1 p2); intros.
    apply cmp_to_eq in H4; subst p2.
    apply (H m mu rho p p1 l0 q0 e0 E). reflexivity.
    assert (Some (process_value (enclave_state_value e0 E) l q)
    = Some (process_value e' l' q0)).
    rewrite <- H3. apply NatMapFacts.add_eq_o; reflexivity.
    injection H4; intros; subst. exact H20.
    apply cmp_to_uneq in H4.
    apply (H m mu rho p p1 l q e0 E). reflexivity.
    assert (NatMap.find p1 (NatMap.add p2 (process_value e' l' q0) p) = NatMap.find p1 p).
    apply NatMapFacts.add_neq_o; apply not_eq_sym; exact H4.
    rewrite <- H5. exact H3.
    destruct H4 as (index & F & V & C & R & H4 & H5).
    case_eq (NatMap.find index k); intros. destruct s.
    eexists index; eexists c; eexists v; eexists w; eexists s.
    apply (mlc_read_v lambda h_tree m e' mu l1 D delta obs0 k index F V C R c v w s H27) in H38.
    subst. split. exact H6. exact H5. exact H4. exact H6.
    assert (NatMap.find index k <> None).
    apply (wf_mlc_read_some lambda h_tree m e' mu l1 D delta obs0 k index H27 H38).
    intros contra; rewrite -> contra in H4; discriminate.
    rewrite -> H6 in H7. destruct H7; reflexivity.
  - subst. assert (H45 := H43). destruct e. destruct e'.
    apply enclave_creation_id in H43. subst e2.
    assert (exists index F V C R, NatMap.find index m = Some (single_level_cache F V C R) /\
    (forall e0, e = enclave_ID_active e0 -> NatMap.In e0 V)).
    apply (H m mu rho p p2 l0 q0 e e1). reflexivity. exact H20.
    case_eq (eqb p1 p2); intros.
    apply cmp_to_eq in H5; subst p2.
    assert (Some (process_value (enclave_state_value e0 E) l q)
    = Some (process_value (enclave_state_value e e3) l' q0)).
    rewrite <- H3. apply NatMapFacts.add_eq_o; reflexivity.
    injection H5; intros; subst.
    apply (wf5_mlc_alloc lambda h_tree r_bar_val n m).
    exact H34. exact H44. exact H4.
    apply cmp_to_uneq in H5.
    assert (exists index F V C R, NatMap.find index m = Some (single_level_cache F V C R) /\
    (forall e, e0 = enclave_ID_active e -> NatMap.In e V)).
    apply (H m mu rho p p1 l q e0 E). reflexivity.
    assert (NatMap.find p1 (NatMap.add p2 (process_value (enclave_state_value
    e e3) l' q0) p) = NatMap.find p1 p).
    apply NatMapFacts.add_neq_o; apply not_eq_sym; exact H5.
    rewrite <- H6. exact H3.
    apply (wf5_mlc_alloc lambda h_tree r_bar_val n m).
    exact H34. exact H44. exact H6.
  - subst.
    assert (exists index F V C R, NatMap.find index m = Some (single_level_cache F V C R) /\
    (forall e, e0 = enclave_ID_active e -> NatMap.In e V)).
    case_eq (eqb p1 p2); intros.
    apply cmp_to_eq in H4; subst p2.
    apply (H m m0 rho p p1 l0 q0 e0 E). reflexivity.
    assert (Some (process_value (enclave_state_value e0 E) l q)
    = Some (process_value e' l' q0)).
    rewrite <- H3. apply NatMapFacts.add_eq_o; reflexivity.
    injection H4; intros; subst. exact H20.
    apply cmp_to_uneq in H4.
    apply (H m m0 rho p p1 l q e0 E). reflexivity.
    assert (NatMap.find p1 (NatMap.add p2 (process_value e' l' q0) p) = NatMap.find p1 p).
    apply NatMapFacts.add_neq_o; apply not_eq_sym; exact H4.
    rewrite <- H5. exact H3.
    destruct H4 as (index & F & V & C & R & H4 & H5).
    case_eq (NatMap.find index k); intros. destruct s.
    eexists index; eexists c; eexists v0; eexists w; eexists s.
    apply (mlc_write_v lambda h_tree m e' m0 l1 v D obs1 mu k index F V C R c v0 w s H27) in H38.
    subst. split. exact H6. exact H5. exact H4. exact H6.
    assert (NatMap.find index k <> None).
    apply (wf_mlc_write_some lambda h_tree m e' m0 l1 v D obs1 mu k index H27 H38).
    intros contra; rewrite -> contra in H4; discriminate.
    rewrite -> H6 in H7. destruct H7; reflexivity.
  - subst. assert (H44 := H38). destruct e. destruct e'.
    assert (H42 := H41).
    apply enclave_elimination_id in H41. subst e2.
    assert (forall e_, e = enclave_ID_active e_ -> r_val <> e_). intros.
    apply (enclave_elimination_neq e e1 r_val e e3 e_) in H42. exact H42. exact H4.
    assert (exists index F V C R, NatMap.find index m = Some (single_level_cache F V C R) /\
    (forall e0, e = enclave_ID_active e0 -> NatMap.In e0 V)).
    apply (H m m0 rho p p2 l0 q0 e e1). reflexivity. exact H20.
    case_eq (eqb p1 p2); intros.
    apply cmp_to_eq in H6; subst p2.
    assert (Some (process_value (enclave_state_value e0 E) l q)
    = Some (process_value (enclave_state_value e e3) l' q0)).
    rewrite <- H3. apply NatMapFacts.add_eq_o; reflexivity.
    injection H6; intros; subst.
    apply (wf5_mlc_dealloc1 lambda h_tree r_val m k e).
    exact H31. exact H39. exact H5. auto.
    apply cmp_to_uneq in H6.
    assert (NatMap.find p1 (NatMap.add p2 (process_value (enclave_state_value
    e e3) l' q0) p) = NatMap.find p1 p).
    apply NatMapFacts.add_neq_o; apply not_eq_sym; exact H6.
    assert (exists index F V C R, NatMap.find index m = Some (single_level_cache F V C R) /\
    (forall e, e0 = enclave_ID_active e -> NatMap.In e V)).
    apply (H m m0 rho p p1 l q e0 E). reflexivity.
    rewrite <- H7. exact H3.
    rewrite -> H3 in H7. apply eq_sym in H7.
    case_eq (equal_enclave_IDs e e0); intros;
    unfold equal_enclave_IDs in *; destruct e; destruct e0.
    apply cmp_to_eq in H9. subst r0.
    apply (wf5_mlc_dealloc1 lambda h_tree r_val m k (enclave_ID_active r)).
    exact H31. exact H39. exact H5. auto.
    discriminate. discriminate.
    apply (wf5_mlc_dealloc1 lambda h_tree r_val m k enclave_ID_inactive).
    exact H31. exact H39. exact H5. auto.
    apply cmp_to_uneq in H9.
    apply (wf5_mlc_dealloc1 lambda h_tree r_val m k (enclave_ID_active r0)).
    exact H31. exact H39. exact H8. apply enclave_elimination_in in H42.
    intros. injection H10; intros; subst.
    assert (forall p1' e0' E' l' q', NatMap.find p1' p = Some (process_value
    (enclave_state_value (enclave_ID_active e0') E') l' q') ->
    forall e, enclave_ID_active e0' = enclave_ID_active e -> r_val <> e).
    apply (any_active_enclave_not_contained (runtime_state_value m m0 rho p) m m0 rho p
    p2 (enclave_ID_active r) e1 l0 q0 r_val). reflexivity. exact H23. exact HE0.
    exact H20. exact H4. exact H42.
    apply (H11 p1 e_ E l q H7). reflexivity.
    apply (wf5_mlc_dealloc1 lambda h_tree r_val m k enclave_ID_inactive).
    exact H31. exact H39. exact H8. auto.
    intros; discriminate.
    apply (wf5_mlc_dealloc1 lambda h_tree r_val m k (enclave_ID_active r)).
    exact H31. exact H39. exact H8. apply enclave_elimination_in in H42.
    intros. injection H10; intros; subst.
    assert (forall p1' e0' E' l' q', NatMap.find p1' p = Some (process_value
    (enclave_state_value (enclave_ID_active e0') E') l' q') ->
    forall e, enclave_ID_active e0' = enclave_ID_active e -> r_val <> e).
    apply (any_active_enclave_not_contained (runtime_state_value m m0 rho p) m m0 rho p
    p2 enclave_ID_inactive e1 l0 q0 r_val). reflexivity. exact H23. exact HE0.
    exact H20. exact H4. exact H42.
    apply (H11 p1 e_ E l q H7). reflexivity.
    apply (wf5_mlc_dealloc1 lambda h_tree r_val m k enclave_ID_inactive).
    exact H31. exact H39. exact H8. auto.
  - subst. destruct e.
    unfold active_enclave_update in H38.
    case_eq (NatMap.find r_val e1); intros.
    assert (A0 := H4); destruct (NatMap.find r_val e1) in A0, H38.
    injection A0; injection H38; intros; subst; clear A0.
    assert (NatMap.find r_val e1 <> None).
    intros contra; rewrite -> H4 in contra; discriminate.
    apply NatMapFacts.in_find_iff in H5.
    case_eq (eqb p1 p2); intros.
    apply cmp_to_eq in H6; subst p2.
    assert (Some (process_value (enclave_state_value e0 E) l q)
    = Some (process_value (enclave_state_value (enclave_ID_active r_val) e1) l' q0)).
    rewrite <- H3. apply NatMapFacts.add_eq_o; reflexivity.
    injection H6; intros; subst.
    assert (exists index F V C R, NatMap.find index k = Some (single_level_cache F V C R) /\
    (forall e0, e = enclave_ID_active e0 -> NatMap.In e0 V)).
    apply (H k mu rho p p1 l0 q0 e e1).
    reflexivity. exact H20.
    assert (enclave_state_value (enclave_ID_active r_val) e1
    = enclave_state_value (enclave_ID_active r_val) e1). reflexivity.
    specialize (H39 (enclave_ID_active r_val) e1 H8 r_val H5).
    destruct H39 as (index & F & V & C & R & H39 & H40).
    eexists index; eexists F; eexists V; eexists C; eexists R.
    split. exact H39.
    intros; injection H9; intros; subst. exact H40.
    apply cmp_to_uneq in H6.
    assert (NatMap.find p1 (NatMap.add p2 (process_value (enclave_state_value
    (enclave_ID_active r_val) e1) l' q0) p) = NatMap.find p1 p).
    apply NatMapFacts.add_neq_o; apply not_eq_sym; exact H6.
    rewrite -> H7 in H3.
    apply (H k mu rho p p1 l q e0 E).
    reflexivity. exact H3.
    discriminate.
    destruct (NatMap.find r_val e1); discriminate.
  - subst. destruct e.
    unfold active_enclave_update in H37.
    injection H37; intros; subst.
    case_eq (eqb p1 p2); intros.
    apply cmp_to_eq in H4; subst p2.
    assert (Some (process_value (enclave_state_value e0 E) l q)
    = Some (process_value (enclave_state_value enclave_ID_inactive e1) l' q0)).
    rewrite <- H3. apply NatMapFacts.add_eq_o; reflexivity.
    injection H4; intros; subst.
    assert (exists index F V C R, NatMap.find index k = Some (single_level_cache F V C R) /\
    (forall e0, e = enclave_ID_active e0 -> NatMap.In e0 V)).
    apply (H k mu rho p p1 l0 q0 e e1).
    reflexivity. exact H20.
    destruct H5 as (index & F & V & C & R & H5 & H6).
    eexists index; eexists F; eexists V; eexists C; eexists R.
    split. exact H5. intros; discriminate.
    apply cmp_to_uneq in H4.
    assert (NatMap.find p1 (NatMap.add p2 (process_value (enclave_state_value
    enclave_ID_inactive e1) l' q0) p) = NatMap.find p1 p).
    apply NatMapFacts.add_neq_o; apply not_eq_sym; exact H4.
    rewrite -> H5 in H3.
    apply (H k mu rho p p1 l q e0 E).
    reflexivity. exact H3.
  - subst. case_eq (eqb p1 p2); intros.
    apply cmp_to_eq in H4; subst p2.
    assert (Some (process_value (enclave_state_value e0 E) l q)
    = Some (process_value e' l' q0)).
    rewrite <- H3. apply NatMapFacts.add_eq_o; reflexivity.
    injection H4; intros; subst.
    apply (H k mu rho p p1 l0 q0 e0 E).
    reflexivity. exact H20.
    apply cmp_to_uneq in H4.
    assert (NatMap.find p1 p = Some (process_value (enclave_state_value e0 E) l q)).
    rewrite <- H3. apply eq_sym.
    apply NatMapFacts.add_neq_o; apply not_eq_sym; exact H4.
    apply (H k mu rho p p1 l q e0 E).
    reflexivity. exact H5.
  - subst. case_eq (eqb p1 p2); intros.
    apply cmp_to_eq in H4; subst p2.
    assert (Some (process_value (enclave_state_value e0 E) l q)
    = Some (process_value e' l' q0)).
    rewrite <- H3. apply NatMapFacts.add_eq_o; reflexivity.
    injection H4; intros; subst.
    apply (H k mu rho p p1 l0 q0 e0 E).
    reflexivity. exact H20.
    apply cmp_to_uneq in H4.
    assert (NatMap.find p1 p = Some (process_value (enclave_state_value e0 E) l q)).
    rewrite <- H3. apply eq_sym.
    apply NatMapFacts.add_neq_o; apply not_eq_sym; exact H4.
    apply (H k mu rho p p1 l q e0 E).
    reflexivity. exact H5.
  - subst. case_eq (eqb p1 p2); intros.
    apply cmp_to_eq in H4; subst p2.
    assert (Some (process_value (enclave_state_value e0 E) l q)
    = Some (process_value e l0 q')).
    rewrite <- H3. apply NatMapFacts.add_eq_o; reflexivity.
    injection H4; intros; subst.
    apply (H k mu rho p p1 l0 q0 e0 E).
    reflexivity. exact H11.
    apply cmp_to_uneq in H4.
    assert (NatMap.find p1 p = Some (process_value (enclave_state_value e0 E) l q)).
    rewrite <- H3. apply eq_sym.
    apply NatMapFacts.add_neq_o; apply not_eq_sym; exact H4.
    apply (H k mu rho p p1 l q e0 E).
    reflexivity. exact H5.
Qed.

(* Well-Formed 6 *)
Definition wf6 (sigma: runtime_state): Prop :=
  forall k mu rho pi p state E q e l_data k_num l_pc b_pc delta_pc D_pc,
  (sigma = runtime_state_value k mu rho pi) ->
  NatMap.find p pi = Some (process_value (enclave_state_value state E) (address b_pc delta_pc) q) ->
  NatMap.find e E = Some (enclave_address_and_data l_data k_num) ->
  l_pc = address b_pc delta_pc -> NatMap.find b_pc mu = Some D_pc ->
  (exists i, NatMap.find delta_pc D_pc = Some (memory_value_instruction i)) /\
  (forall n b_data delta_data D_data, n < k_num -> add_to_memory_address mu l_data n = Some (address b_data delta_data) ->
  NatMap.find b_data mu = Some D_data -> exists n_k, NatMap.find delta_data D_data = Some (memory_value_data n_k)).

Lemma enclave_creation_add : forall r E mu n r_val2_addr r_val3 r0 E0,
  enclave_creation (enclave_state_value r E) mu n r_val2_addr r_val3 =
  enclave_state_valid (enclave_state_value r0 E0) ->
  E0 = (NatMap.add n (enclave_address_and_data r_val2_addr r_val3) E).
Proof.
  intros.
  unfold enclave_creation in H.
  destruct r_val2_addr.
  destruct (NatMap.find b mu).
  unfold add_new_enclave_to_enclave_state in H.
  destruct is_all_zeroes in H.
  destruct (NatMap.find n E).
  discriminate.
  injection H; intros; subst; reflexivity.
  discriminate. discriminate.
Qed.

Lemma enclave_creation_neq : forall r E mu n r_val2_addr r_val3 r0 E0,
  enclave_creation (enclave_state_value r E) mu n r_val2_addr r_val3 =
  enclave_state_valid (enclave_state_value r0 E0) ->
  n <> r_val3.
Proof.
Admitted.

(* WF6 Preservation *)
Lemma wf6_preservation : forall sigma obs sigma' obs',
  wf6 sigma -> <<sigma; obs>> ===> <<sigma'; obs'>> -> wf6 sigma'.
Proof.
  destruct sigma; destruct sigma'.
  unfold wf6 in *.
  intros; injection H1.
  inversion H0.
  destruct l. destruct l'. destruct e0. destruct e'.
  inversion H17; intros; subst.
  - case_eq (eqb p1 p2); intros.
    apply cmp_to_eq in H4. subst.
    assert (Some (process_value (enclave_state_value state E) (address b_pc delta_pc) q) =
    Some (process_value (enclave_state_value e2 e3) (address b0 d0) q0)).
    rewrite <- H2. apply NatMapFacts.add_eq_o; reflexivity.
    injection H4; intros; subst.
    unfold memory_read in H13.
    case_eq (NatMap.find b mu); intros.
    assert (A0 := H6); destruct (NatMap.find b mu) in A0, H13.
    injection A0; intros; subst; clear A0.
    assert ((exists i, NatMap.find d d1 = Some (memory_value_instruction i)) /\
    (forall n b_data delta_data D_data, n < k_num ->
    add_to_memory_address mu l_data n = Some (address b_data delta_data) ->
    NatMap.find (elt:=data_block) b_data mu = Some D_data ->
    exists n_k : data, NatMap.find (elt:=memory_value) delta_data D_data = Some (memory_value_data n_k))).
    apply (H m mu rho p p2 e2 e3 q0 e l_data k_num (address b d) b d d1).
    reflexivity. exact H18. exact H3. reflexivity. exact H6.
    split. destruct H20 as (i' & H20).
    unfold memory_read in H20.
    assert (A0 := H5); destruct (NatMap.find b0 mu) in A0, H20.
    injection A0; intros; subst; clear A0.
    eexists i'; exact H20. discriminate.
    destruct H7. exact H8. discriminate.
    destruct (NatMap.find b mu); discriminate.
    apply cmp_to_uneq in H4.
    unfold memory_read in H13.
    case_eq (NatMap.find b mu); intros.
    assert (A0 := H6); destruct (NatMap.find b mu) in A0, H13.
    injection A0; intros; subst; clear A0.
    apply (H m mu rho p p1 state E q e l_data k_num (address b_pc delta_pc) b_pc delta_pc D_pc).
    reflexivity. rewrite <- H2. apply eq_sym.
    apply NatMapFacts.add_neq_o; apply not_eq_sym; exact H4.
    exact H3. reflexivity. exact H5. discriminate.
    destruct (NatMap.find b mu); discriminate.
  - give_up.
(*
    case_eq (eqb p1 p2); intros.
    apply cmp_to_eq in H4. subst.
    assert (Some (process_value (enclave_state_value state E) (address b_pc delta_pc) q) =
    Some (process_value (enclave_state_value e2 e3) (address b0 d0) q0)).
    rewrite <- H2. apply NatMapFacts.add_eq_o; reflexivity.
    injection H4; intros; subst.
    unfold memory_read in H13.
    case_eq (NatMap.find b mu); intros.
    assert (A0 := H6); destruct (NatMap.find b mu) in A0, H13.
    injection A0; intros; subst; clear A0.
    assert (H43 := H41). assert (H44 := H41).
    apply enclave_creation_id in H41. subst.
    apply enclave_creation_add in H43. subst e3.
    case_eq (NatMap.find e e1); intros. destruct e0.
    split. destruct H20 as (i' & H20).
    unfold memory_read in H20.
    assert (A0 := H5); destruct (NatMap.find b0 mu) in A0, H20.
    injection A0; intros; subst; clear A0.
    eexists i'; exact H20. discriminate.
    case_eq (eqb n e); intros.
    apply cmp_to_eq in H8; subst.
    assert (Some (enclave_address_and_data l_data k_num) =
    Some (enclave_address_and_data r_val2_addr r_val3)).
    rewrite <- H3. apply NatMapFacts.add_eq_o; reflexivity.
    injection H8; intros; subst r_val2_addr r_val3; clear H8.
    assert ((exists i, NatMap.find d d1 = Some (memory_value_instruction i)) /\
    (forall n b_data delta_data D_data, n < n0 ->
    add_to_memory_address mu m0 n = Some (address b_data delta_data) ->
    NatMap.find (elt:=data_block) b_data mu = Some D_data ->
    exists n_k : data, NatMap.find (elt:=memory_value) delta_data D_data = Some (memory_value_data n_k))).
    apply (H m mu rho p p2 e2 e1 q0 e m0 n0 (address b d) b d d1).
    reflexivity. exact H18. exact H7. reflexivity. exact H6.
    destruct H8. apply (H12 k_num b_data delta_data D_data).                                    
    apply (H m mu rho p p2 e2 e1 q0 e l_data k_num (address b d) b d D_pc).


    apply (H m mu rho p p2 e2 e1 q0 e l_data k_num (address b d) b d D_pc).
    reflexivity. exact H18.

    intros. apply (H9 k_num b_data delta_data D_data).
    apply H9.
    case_eq (eqb n e); intros.
    apply cmp_to_eq in H10; subst.
    apply (H9 k_num b_data delta_data D_data).

rewrite <- H3.
    assert (n <> e).
    unfold enclave_creation in H43. destruct r_val2_addr.
    destruct (NatMap.find b1 mu). destruct is_all_zeroes.
    unfold add_new_enclave_to_enclave_state in H43.
    case_eq (NatMap.find n e1); intros.
    destruct (NatMap.find n e1); discriminate.
    intros contra. subst.
    discriminate. injection A0; intros; subst; clear A0.





    reflexivity. exact H6.
    split. destruct H20 as (i' & H20).
    unfold memory_read in H20.
    assert (A0 := H5); destruct (NatMap.find b0 mu) in A0, H20.
    injection A0; intros; subst; clear A0.
    eexists i'; exact H20. discriminate.
    destruct H7. exact H8. discriminate.
    destruct (NatMap.find b mu); discriminate.
    apply cmp_to_uneq in H4.
    unfold memory_read in H12.
    case_eq (NatMap.find b mu); intros.
    assert (A0 := H6); destruct (NatMap.find b mu) in A0, H12.
    injection A0; intros; subst; clear A0.
    apply (H m mu rho p p1 state E q e l_data k_num (address b_pc delta_pc) b_pc delta_pc D_pc).
    reflexivity. rewrite <- H2. apply eq_sym.
    apply NatMapFacts.add_neq_o; apply not_eq_sym; exact H4.
    exact H3. reflexivity. exact H5. discriminate.
    destruct (NatMap.find b mu); discriminate.
    
Lemma mlc_read_data_block :
  mlc_read m (enclave_state_value e1 e2) mu l1 lambda h_tree =
  mlc_read_valid D delta obs0 k -> NatMap.find b mu = Some D.


    apply (H m mu rho p p2 state E (address b0 delta0) q0 e l k_num b0 delta0 D0).
    reflexivity.
*)
  - give_up.
  - give_up.
  - unfold active_enclave_update in H36.
    destruct (NatMap.find r_val e1); intros.
    injection H36; intros; subst.
    case_eq (eqb p1 p2); intros.
    apply cmp_to_eq in H4. subst.
    assert (Some (process_value (enclave_state_value state E) (address b_pc delta_pc) q) =
    Some (process_value (enclave_state_value (enclave_ID_active r_val) e3) (address b0 d0) q0)).
    rewrite <- H2. apply NatMapFacts.add_eq_o; reflexivity.
    injection H4; intros; subst.
    unfold memory_read in H13.
    case_eq (NatMap.find b mu); intros.
    assert (A0 := H6); destruct (NatMap.find b mu) in A0, H13.
    injection A0; intros; subst; clear A0.
    assert ((exists i, NatMap.find d d1 = Some (memory_value_instruction i)) /\
    (forall n b_data delta_data D_data, n < k_num ->
    add_to_memory_address mu l_data n = Some (address b_data delta_data) ->
    NatMap.find (elt:=data_block) b_data mu = Some D_data ->
    exists n_k : data, NatMap.find (elt:=memory_value) delta_data D_data = Some (memory_value_data n_k))).
    apply (H k mu rho p p2 e0 e3 q0 e l_data k_num (address b d) b d d1).
    reflexivity. exact H18. exact H3. reflexivity. exact H6.
    split. destruct H20 as (i' & H20).
    unfold memory_read in H20.
    assert (A0 := H5); destruct (NatMap.find b0 mu) in A0, H20.
    injection A0; intros; subst; clear A0.
    eexists i'; exact H20. discriminate.
    destruct H7. exact H8. discriminate.
    destruct (NatMap.find b mu); discriminate.
    apply cmp_to_uneq in H4.
    unfold memory_read in H13.
    case_eq (NatMap.find b mu); intros.
    assert (A0 := H6); destruct (NatMap.find b mu) in A0, H13.
    injection A0; intros; subst; clear A0.
    apply (H k mu rho p p1 state E q e l_data k_num (address b_pc delta_pc) b_pc delta_pc D_pc).
    reflexivity. rewrite <- H2. apply eq_sym.
    apply NatMapFacts.add_neq_o; apply not_eq_sym; exact H4.
    exact H3. reflexivity. exact H5. discriminate.
    destruct (NatMap.find b mu); discriminate. discriminate.
  - unfold active_enclave_update in H35.
    injection H35; intros; subst.
    case_eq (eqb p1 p2); intros.
    apply cmp_to_eq in H4. subst.
    assert (Some (process_value (enclave_state_value state E) (address b_pc delta_pc) q) =
    Some (process_value (enclave_state_value enclave_ID_inactive e3) (address b0 d0) q0)).
    rewrite <- H2. apply NatMapFacts.add_eq_o; reflexivity.
    injection H4; intros; subst.
    unfold memory_read in H13.
    case_eq (NatMap.find b mu); intros.
    assert (A0 := H6); destruct (NatMap.find b mu) in A0, H13.
    injection A0; intros; subst; clear A0.
    assert ((exists i, NatMap.find d d1 = Some (memory_value_instruction i)) /\
    (forall n b_data delta_data D_data, n < k_num ->
    add_to_memory_address mu l_data n = Some (address b_data delta_data) ->
    NatMap.find (elt:=data_block) b_data mu = Some D_data ->
    exists n_k : data, NatMap.find (elt:=memory_value) delta_data D_data = Some (memory_value_data n_k))).
    apply (H k mu rho p p2 e0 e3 q0 e l_data k_num (address b d) b d d1).
    reflexivity. exact H18. exact H3. reflexivity. exact H6.
    split. destruct H20 as (i' & H20).
    unfold memory_read in H20.
    assert (A0 := H5); destruct (NatMap.find b0 mu) in A0, H20.
    injection A0; intros; subst; clear A0.
    eexists i'; exact H20. discriminate.
    destruct H7. exact H8. discriminate.
    destruct (NatMap.find b mu); discriminate.
    apply cmp_to_uneq in H4.
    unfold memory_read in H13.
    case_eq (NatMap.find b mu); intros.
    assert (A0 := H6); destruct (NatMap.find b mu) in A0, H13.
    injection A0; intros; subst; clear A0.
    apply (H k mu rho p p1 state E q e l_data k_num (address b_pc delta_pc) b_pc delta_pc D_pc).
    reflexivity. rewrite <- H2. apply eq_sym.
    apply NatMapFacts.add_neq_o; apply not_eq_sym; exact H4.
    exact H3. reflexivity. exact H5. discriminate.
    destruct (NatMap.find b mu); discriminate.
  - case_eq (eqb p1 p2); intros.
    apply cmp_to_eq in H4. subst.
    assert (Some (process_value (enclave_state_value state E) (address b_pc delta_pc) q) =
    Some (process_value (enclave_state_value e2 e3) (address b0 d0) q0)).
    rewrite <- H2. apply NatMapFacts.add_eq_o; reflexivity.
    injection H4; intros; subst.
    unfold memory_read in H13.
    case_eq (NatMap.find b mu); intros.
    assert (A0 := H6); destruct (NatMap.find b mu) in A0, H13.
    injection A0; intros; subst; clear A0.
    assert ((exists i, NatMap.find d d1 = Some (memory_value_instruction i)) /\
    (forall n b_data delta_data D_data, n < k_num ->
    add_to_memory_address mu l_data n = Some (address b_data delta_data) ->
    NatMap.find (elt:=data_block) b_data mu = Some D_data ->
    exists n_k : data, NatMap.find (elt:=memory_value) delta_data D_data = Some (memory_value_data n_k))).
    apply (H k mu rho p p2 e2 e3 q0 e l_data k_num (address b d) b d d1).
    reflexivity. exact H18. exact H3. reflexivity. exact H6.
    split. destruct H20 as (i' & H20).
    unfold memory_read in H20.
    assert (A0 := H5); destruct (NatMap.find b0 mu) in A0, H20.
    injection A0; intros; subst; clear A0.
    eexists i'; exact H20. discriminate.
    destruct H7. exact H8. discriminate.
    destruct (NatMap.find b mu); discriminate.
    apply cmp_to_uneq in H4.
    unfold memory_read in H13.
    case_eq (NatMap.find b mu); intros.
    assert (A0 := H6); destruct (NatMap.find b mu) in A0, H13.
    injection A0; intros; subst; clear A0.
    apply (H k mu rho p p1 state E q e l_data k_num (address b_pc delta_pc) b_pc delta_pc D_pc).
    reflexivity. rewrite <- H2. apply eq_sym.
    apply NatMapFacts.add_neq_o; apply not_eq_sym; exact H4.
    exact H3. reflexivity. exact H5. discriminate.
    destruct (NatMap.find b mu); discriminate.
  - case_eq (eqb p1 p2); intros.
    apply cmp_to_eq in H4. subst.
    assert (Some (process_value (enclave_state_value state E) (address b_pc delta_pc) q) =
    Some (process_value (enclave_state_value e2 e3) (address b0 d0) q0)).
    rewrite <- H2. apply NatMapFacts.add_eq_o; reflexivity.
    injection H4; intros; subst.
    unfold memory_read in H13.
    case_eq (NatMap.find b mu); intros.
    assert (A0 := H6); destruct (NatMap.find b mu) in A0, H13.
    injection A0; intros; subst; clear A0.
    assert ((exists i, NatMap.find d d1 = Some (memory_value_instruction i)) /\
    (forall n b_data delta_data D_data, n < k_num ->
    add_to_memory_address mu l_data n = Some (address b_data delta_data) ->
    NatMap.find (elt:=data_block) b_data mu = Some D_data ->
    exists n_k : data, NatMap.find (elt:=memory_value) delta_data D_data = Some (memory_value_data n_k))).
    apply (H k mu rho p p2 e2 e3 q0 e l_data k_num (address b d) b d d1).
    reflexivity. exact H18. exact H3. reflexivity. exact H6.
    split. destruct H20 as (i' & H20).
    unfold memory_read in H20.
    assert (A0 := H5); destruct (NatMap.find b0 mu) in A0, H20.
    injection A0; intros; subst; clear A0.
    eexists i'; exact H20. discriminate.
    destruct H7. exact H8. discriminate.
    destruct (NatMap.find b mu); discriminate.
    apply cmp_to_uneq in H4.
    unfold memory_read in H13.
    case_eq (NatMap.find b mu); intros.
    assert (A0 := H6); destruct (NatMap.find b mu) in A0, H13.
    injection A0; intros; subst; clear A0.
    apply (H k mu rho p p1 state E q e l_data k_num (address b_pc delta_pc) b_pc delta_pc D_pc).
    reflexivity. rewrite <- H2. apply eq_sym.
    apply NatMapFacts.add_neq_o; apply not_eq_sym; exact H4.
    exact H3. reflexivity. exact H5. discriminate.
    destruct (NatMap.find b mu); discriminate.
  - intros; subst. case_eq (eqb p1 p2); intros.
    apply cmp_to_eq in H4. subst.
    assert (Some (process_value (enclave_state_value state E) (address b_pc delta_pc) q) =
    Some (process_value e0 l q')).
    rewrite <- H2. apply NatMapFacts.add_eq_o; reflexivity.
    injection H4; intros; subst.
    apply (H k mu rho p p2 state E q0 e l_data k_num (address b_pc delta_pc) b_pc delta_pc D_pc).
    reflexivity. exact H9. exact H3. reflexivity. exact H5.
    apply cmp_to_uneq in H4.
    apply (H k mu rho p p1 state E q e l_data k_num (address b_pc delta_pc) b_pc delta_pc D_pc).
    reflexivity. rewrite <- H2. apply eq_sym.
    apply NatMapFacts.add_neq_o; apply not_eq_sym; exact H4.
    exact H3. reflexivity. exact H5.
Admitted.