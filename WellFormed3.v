From Coq Require Import Lists.List.
From Coq Require Import Bool.Bool.
From Coq Require Import Lia.
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
Require Import WellFormed2.

Module NatMapFacts := NatMapProperties.F.
Module CacheletMapFacts := CacheletMapProperties.F.

(* Well-Formed 7-1 *)
Definition wf7_1 (sigma: runtime_state): Prop :=
  forall k mu rho pi lambda F V C R,
  sigma = runtime_state_value k mu rho pi ->
  (NatMap.find lambda k = Some (single_level_cache F V C R)) ->
  (forall w s, CacheletMap.In (w, s) C -> NatMap.In s R).

(* WF7-1 MLC Read *)
Lemma cc_hit_read_r : forall psi e' l D delta c0 psi' F V C R F' V' C' R',
  cc_hit_read psi e' l = cc_hit_read_valid D delta c0 psi' ->
  psi = single_level_cache F V C R ->
  psi' = single_level_cache F' V' C' R' ->
  forall x, NatMap.In x R <-> NatMap.In x R'.
Proof.
  intros.
  subst psi psi'.
  unfold cc_hit_read in H.
  case_eq (cc_unfold (single_level_cache F V C R) e' l). intros.
  assert (A0 := H0). destruct (cc_unfold (single_level_cache F V C R) e' l) in A0, H.
  injection A0; intros; subst; clear A0.
  apply cc_unfold_psi in H0.
  injection H0; intros; subst c v w s.
  destruct c1.
  destruct w0.
  case_eq (NatMap.find s R). intros p H2.
  assert (A0 := H2); destruct (NatMap.find s R) in H, A0.
  injection A0; intros; subst; clear A0.
  destruct e'.
  injection H; intros; subst.
  split; intros.
  apply NatMapFacts.add_in_iff. right; exact H1.
  apply NatMapFacts.add_in_iff in H1. destruct H1.
  subst. apply NatMapFacts.in_find_iff.
  intros contra. rewrite -> H2 in contra. discriminate.
  exact H1.
  discriminate.
  intros; destruct (NatMap.find s R); discriminate.
  discriminate.
  intros; destruct (cc_unfold (single_level_cache F V C R) e' l); discriminate.
Qed.

Lemma cc_update_r : forall psi e' d l0 c0 psi' F V C R F' V' C' R',
  cc_update psi e' d l0 = cc_update_valid c0 psi' ->
  psi = single_level_cache F V C R ->
  psi' = single_level_cache F' V' C' R' ->
  forall x, (NatMap.In x R <-> NatMap.In x R').
Proof.
  intros.
  subst psi psi'.
  unfold cc_update in H.
  case_eq (cc_unfold (single_level_cache F V C R) e' l0). intros.
  assert (A0 := H0). destruct (cc_unfold (single_level_cache F V C R) e' l0) in A0, H.
  assert (H1 := H0).
  apply cc_unfold_psi in H0.
  apply cc_unfold_c in H1.
  injection A0; intros; subst; clear A0.
  injection H0; intros; subst c v w s.
  destruct c1.
  destruct w0.
  destruct e'.
  case_eq (NatMap.find s R); intros.
  assert (A0 := H2); destruct (NatMap.find s R) in H, A0.
  injection A0; intros; subst; clear A0.
  destruct (replace p e).
  injection H; intros; subst.
  split.
  {
    intros.
    apply NatMapFacts.add_in_iff.
    right; exact H3.
  }
  {
    intros.
    apply NatMapFacts.add_in_iff in H3. destruct H3.
    subst. apply NatMapFacts.in_find_iff.
    intros contra. rewrite -> H2 in contra. discriminate.
    exact H3.
  }
  discriminate.
  discriminate.
  destruct (NatMap.find s R); discriminate.
  discriminate.
  intros; destruct (cc_unfold (single_level_cache F V C R) e' l0).
  discriminate.
  discriminate.
Qed.

Lemma wf7_1_mlc_read : forall lambda h_tree k e' m0 l0 D obs1 mu k' index psi psi'
  F V C R F' V' C' R',
  well_defined_cache_tree h_tree ->
  mlc_read k e' m0 l0 lambda h_tree = mlc_read_valid D obs1 mu k' ->
  NatMap.find index k = Some psi ->
  NatMap.find index k' = Some psi' ->
  psi = single_level_cache F V C R ->
  psi' = single_level_cache F' V' C' R' ->
  (forall w s, CacheletMap.In (w, s) C -> NatMap.In s R) ->
  (forall w s, CacheletMap.In (w, s) C' -> NatMap.In s R').
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
    apply (H8 w s). exact H9. discriminate.
  }
  {
    intros lambda IHTREE k e' m0 l0 D obs1 mu k' index psi psi' F V C R
    F' V' C' R' H H0 H1 H2 H3 H4 H7.
    unfold recursive_mlc_read in H0.
    fold recursive_mlc_read in H0.
    case_eq (NatMap.find a k). intros s1 H5.
    assert (A0 := H5). destruct (NatMap.find a k) in A0, H0.
    case_eq (cc_hit_read s e' l0). intros d d0 c s2 H6.
    assert (A1 := H6). destruct (cc_hit_read s e' l0) in A1, H0.
    injection H0; injection A0; injection A1;
    intros X0 X1 X2 X3 X4 X5 X6 X7 X8; subst; clear A0 A1.
    assert (H8:= H6).
    destruct s1; destruct s2.
    apply (cc_hit_read_c (single_level_cache c0 v w s) e' l0 D obs1 c
    (single_level_cache c1 v0 w0 s0) c0 v w s c1 v0 w0 s0) in H6.
    assert (forall x, NatMap.In x s <-> NatMap.In x s0).
    apply (cc_hit_read_r (single_level_cache c0 v w s) e' l0 D obs1 c
    (single_level_cache c1 v0 w0 s0) c0 v w s c1 v0 w0 s0 H8).
    subst. reflexivity. reflexivity.
    {
      case_eq (eqb a index).
      {
        intros. apply cmp_to_eq in H4. subst.
        rewrite -> H1 in H5.
        injection H5; intros; subst c0 v w0 s.
        assert (NatMap.find index (NatMap.add index (single_level_cache c1 v0 C s0) k) =
        Some (single_level_cache c1 v0 C s0)).
        apply NatMapFacts.add_eq_o. reflexivity.
        rewrite -> H2 in H4; injection H4; intros; subst.
        apply H3. apply (H7 w1 s1). exact H9.
      }
      {
        intros. apply cmp_to_uneq in H4.
        assert (NatMap.find index (NatMap.add a (single_level_cache c1 v0 w0 s0) k) = NatMap.find index k).
        apply NatMapFacts.add_neq_o. exact H4.
        rewrite -> H2 in H10.
        rewrite -> H1 in H10.
        injection H10; intros; subst F' V' C' R'.
        apply (H7 w1 s1). exact H9.
      }
    }
    reflexivity.
    reflexivity.
    discriminate.
    destruct (cc_hit_read s e' l0).
    intros; discriminate.
    intros H8.
    case_eq (recursive_mlc_read k e' m0 l0 l). intros d d0 o m H9.
    assert (A1 := H9). destruct (recursive_mlc_read k e' m0 l0 l) in A1, H0.
    case_eq (cc_update s e' d1 l0). intros c s0 H10.
    assert (A2 := H10). destruct (cc_update s e' d1 l0) in A2, H0.
    injection H0; injection A0; injection A1; injection A2;
    intros X0 X1 X2 X3 X4 X5 X6 X7 X8 X9 X10; subst; clear A0 A1 A2.
    {
      case_eq (eqb index a).
      {
        intros H3. apply cmp_to_eq in H3. subst a.
        destruct s1. destruct s0.
        assert (forall c, CacheletMap.In c w <-> CacheletMap.In c w0); intros.
        apply (cc_update_c (single_level_cache c0 v w s) e' D l0 c (single_level_cache c1 v0 w0 s0)
        c0 v w s c1 v0 w0 s0 c2 H10). reflexivity. reflexivity.
        assert (forall x, NatMap.In x s <-> NatMap.In x s0).
        apply (cc_update_r (single_level_cache c0 v w s) e' D l0 c (single_level_cache c1 v0 w0 s0)
        c0 v w s c1 v0 w0 s0 H10). reflexivity. reflexivity.
        subst.
        assert (NatMap.find index (NatMap.add index (single_level_cache c1 v0 w0 s0) m) =
        Some (single_level_cache c1 v0 w0 s0)).
        apply NatMapFacts.add_eq_o. reflexivity.
        rewrite -> H11 in H2.
        rewrite -> H5 in H1.
        injection H1; injection H2; intros; subst.
        apply H6. apply (H7 w1 s1). apply H3. exact H4.
      }
      {
        intros H3. apply cmp_to_uneq in H3.
        assert (WFH := H).
        unfold well_defined_cache_tree in H.
        destruct H as [ WFH1 ]. destruct H as [ WFH2 ]. destruct H as [ WFH3 ].
        destruct l.
        {
          apply (IHl root_node WFH1 k e' m0 l0 D obs1 o m index (single_level_cache F V C R)
          (single_level_cache F' V' C' R') F V C R F' V' C' R').
          exact WFH.
          unfold mlc_write. exact H9.
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
          injection WFH2; intros X0; subst.
          apply (H p0 p l) in IHTREE.
          apply (IHl (cache_node p) IHTREE k e' m0 l0 D obs1 o m index (single_level_cache F V C R)
          (single_level_cache F' V' C' R') F V C R F' V' C' R').
          exact WFH.
          unfold mlc_write. exact H9.
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
    intros; destruct (cc_update s e' d1 l0); discriminate.
    discriminate.
    intros; destruct (recursive_mlc_read k e' m0 l0 l); discriminate.
    discriminate.
    intros; destruct (NatMap.find a k); discriminate.
  }
  intros; destruct (get_cache_ID_path lambda h_tree); discriminate.
Qed.

(* WF7-1 MLC Allocation *)
Lemma wf7_1_cachelet_allocation : forall n r F V C R F' V' C' R',
  cachelet_allocation n r (single_level_cache F V C R) = Some (single_level_cache F' V' C' R') ->
  (forall w s, CacheletMap.In (w, s) C -> NatMap.In s R) ->
  (forall w s, CacheletMap.In (w, s) C' -> NatMap.In s R').
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
    apply (H0 w s). exact H1.
  }
  {
    intros F V C R F' V' C' R' H H0.
    unfold recursive_cachelet_allocation in H.
    fold recursive_cachelet_allocation in H.
    case_eq (way_first_allocation F). intros c H2.
    assert (A0 := H2); destruct (way_first_allocation F) in H, A0.
    destruct c0.
    case_eq (NatMap.find s R). intros p H3.
    assert (A1 := H3); destruct (NatMap.find s R) in H, A1.
    case_eq (remove_CAT (w, s) F). intros c0 F0.
    assert (A3 := F0). destruct (remove_CAT (w, s) F) in H, A3.
    case_eq (NatMap.find r V). intros r0 H5.
    assert (A2 := H5). destruct (NatMap.find r V) in H, A2.
    injection A0; injection A1; injection A2; injection A3;
    intros X0 X1 X2 X3; subst; clear A0 A1 A2 A3.
    {
      apply (IHn0 c0 (NatMap.add r ((w, s) :: r0) V) C
      (NatMap.add s (update p w (enclave_ID_active r)) R) F' V' C' R').
      exact H. intros.
      apply NatMapFacts.add_in_iff.
      right. apply (H0 w0 s0). exact H1.
    }
    discriminate.
    intros H5; assert (A2 := H5); destruct (NatMap.find r V) in A2, H.
    discriminate.
    assert (L0 := H2).
    injection A0; injection A1; injection A3; intros X0 X1 X2; subst; clear A0 A1 A2 A3.
    {
      apply (IHn0 c0 (NatMap.add r ((w, s) :: nil) V) C
      (NatMap.add s (update p w (enclave_ID_active r)) R) F' V' C' R').
      exact H. intros.
      apply NatMapFacts.add_in_iff.
      right. apply (H0 w0 s0). exact H1.
    }
    discriminate.
    intros; destruct (remove_CAT (w, s) F); discriminate.
    discriminate.
    intros; destruct (NatMap.find s R); discriminate.
    discriminate.
    intros; destruct (way_first_allocation F); discriminate.
  }
Qed.

Lemma wf7_1_mlc_alloc : forall lambda h_tree n state k k' index psi psi' F V C R F' V' C' R',
  well_defined_cache_tree h_tree ->
  mlc_allocation n state k lambda h_tree = Some k' ->
  NatMap.find index k = Some psi ->
  NatMap.find index k' = Some psi' ->
  psi = single_level_cache F V C R ->
  psi' = single_level_cache F' V' C' R' ->
  (forall w s, CacheletMap.In (w, s) C -> NatMap.In s R) ->
  (forall w s, CacheletMap.In (w, s) C' -> NatMap.In s R').
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
    apply (H6 w s). exact H3.
  }
  {
    intros lambda IHTREE n r k k' index psi psi' F V C R
    F' V' C' R' WFH H H0 H1 H4 H5 H6.
    unfold recursive_mlc_allocation in H.
    fold recursive_mlc_allocation in H.
    destruct n. discriminate.
    case_eq (NatMap.find a k). intros s H2.
    assert (A0 := H2). destruct (NatMap.find a k) in A0, H.
    case_eq (cachelet_allocation n r s0). intros s1 H7.
    assert (A1 := H7). destruct (cachelet_allocation n r s0) in A1, H.
    injection A0; injection A1; intros X0 X1; subst s2 s0; clear A0 A1.
    assert (WFH1 := WFH).
    unfold well_defined_cache_tree in WFH1.
    destruct WFH1 as [ WFH1 WFH2 ]. destruct WFH2 as [ WFH2 WFH3 ]. destruct WFH3 as [ WFH3 WFH4 ].
    case_eq (eqb index a).
    {
      intros H8; apply cmp_to_eq in H8; subst a.
      rewrite -> H2 in H0.
      injection H0; intros X0; subst s.
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
        apply (wf7_1_cachelet_allocation n r F V C R c v w s).
        subst psi psi'; exact H7. exact H6.
      }
      {
        destruct lambda.
        rewrite -> WFH1 in IHTREE. discriminate.
        specialize (WFH3 c0 index (p :: l) IHTREE).
        unfold get_cache_ID_path in IHTREE. discriminate.
        specialize (WFH2 p0 index (p :: l) IHTREE).
        injection WFH2; intros X0; subst p0.
        apply (WFH4 index p l) in IHTREE.
        apply (IHl (cache_node p) IHTREE n0 r (NatMap.add index (single_level_cache c v w s) k)
        k' index (single_level_cache c v w s) psi' c v w s F' V' C' R').
        exact WFH.
        exact H.
        apply NatMapFacts.add_eq_o. reflexivity.
        exact H1.
        reflexivity.
        exact H5.
        apply (wf7_1_cachelet_allocation n r F V C R c v w s).
        subst psi psi'; exact H7. exact H6.
      }
    }
    {
      intros H8; apply cmp_to_uneq in H8.
      destruct l.
      {
        apply (IHl root_node WFH1 n0 r (NatMap.add a s1 k) k' index psi psi' F V C R F' V' C' R').
        exact WFH.
        unfold mlc_allocation. exact H.
        rewrite <- H0. apply NatMapFacts.add_neq_o.
        apply not_eq_sym. exact H8.
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
        injection WFH2; intros X0; subst p0.
        apply (WFH4 a p l) in IHTREE.
        apply (IHl (cache_node p) IHTREE n0 r (NatMap.add a s1 k) k' index psi psi' F V C R F' V' C' R').
        exact WFH.
        unfold mlc_allocation. exact H.
        rewrite <- H0. apply NatMapFacts.add_neq_o.
        apply not_eq_sym. exact H8.
        exact H1.
        exact H4.
        exact H5.
        exact H6.
      }
    }
    discriminate.
    intros; destruct (cachelet_allocation n r s0); discriminate.
    discriminate.
    intros; destruct (NatMap.find a k); discriminate.
  }
  intros; destruct (get_cache_ID_path lambda h_tree); discriminate.
Qed.

(* WF7-1 MLC Write *)
Lemma cc_hit_write_r : forall psi e' l v D c0 psi' F V C R F' V' C' R',
  cc_hit_write psi e' l v = cc_hit_write_valid D c0 psi' ->
  psi = single_level_cache F V C R ->
  psi' = single_level_cache F' V' C' R' ->
  (forall x, NatMap.In x R <-> NatMap.In x R').
Proof.
  intros.
  split.
  {
    intros.
    subst psi psi'.
    unfold cc_hit_write in H.
    case_eq (cc_unfold (single_level_cache F V C R) e' l). intros.
    assert (A0 := H0). destruct (cc_unfold (single_level_cache F V C R) e' l) in A0, H.
    injection A0; intros; subst; clear A0.
    assert (H1 := H0).
    apply cc_unfold_psi in H0.
    apply cc_unfold_c in H1.
    injection H0; intros; subst c v0 w s.
    destruct c1.
    destruct w0.
    case_eq (NatMap.find s R); intros.
    assert (A0 := H3); destruct (NatMap.find s R) in A0, H.
    injection A0; intros; subst; clear A0.
    destruct v.
    discriminate.
    destruct e'.
    injection H; intros; subst.
    apply NatMapFacts.add_in_iff. right; exact H2.
    discriminate.
    destruct (NatMap.find s R); discriminate.
    discriminate.
    intros; destruct (cc_unfold (single_level_cache F V C R) e' l); discriminate.
  }
  {
    intros.
    subst psi psi'.
    unfold cc_hit_write in H.
    case_eq (cc_unfold (single_level_cache F V C R) e' l). intros.
    assert (A0 := H0). destruct (cc_unfold (single_level_cache F V C R) e' l) in A0, H.
    injection A0; intros; subst; clear A0.
    assert (H1 := H0).
    apply cc_unfold_psi in H0.
    apply cc_unfold_c in H1.
    injection H0; intros; subst c v0 w s.
    destruct c1.
    destruct w0.
    case_eq (NatMap.find s R); intros.
    assert (A0 := H3); destruct (NatMap.find s R) in A0, H.
    injection A0; intros; subst; clear A0.
    destruct v.
    discriminate.
    destruct e'.
    injection H; intros; subst.
    apply NatMapFacts.add_in_iff in H2.
    destruct H2. subst.
    apply NatMapFacts.in_find_iff. intros contra.
    rewrite -> H3 in contra. discriminate. exact H2.
    discriminate.
    destruct (NatMap.find s R); discriminate.
    discriminate.
    intros; destruct (cc_unfold (single_level_cache F V C R) e' l); discriminate.
  }
Qed.

Lemma wf7_1_mlc_write : forall lambda h_tree k e' m0 l0 v D obs1 mu k' index psi psi'
  F V C R F' V' C' R',
  well_defined_cache_tree h_tree ->
  mlc_write k e' m0 l0 v lambda h_tree = mlc_write_valid D obs1 mu k' ->
  NatMap.find index k = Some psi ->
  NatMap.find index k' = Some psi' ->
  psi = single_level_cache F V C R ->
  psi' = single_level_cache F' V' C' R' ->
  (forall w s, CacheletMap.In (w, s) C -> NatMap.In s R) ->
  (forall w s, CacheletMap.In (w, s) C' -> NatMap.In s R').
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
    apply (H6 w s). exact H5.
    discriminate.
    discriminate.
  }
  {
    intros lambda IHTREE k e' m0 l0 v D obs1 mu k' index psi psi'
    F V C R F' V' C' R' WFH1 H H0 H1 H2 H3 H6.
    unfold recursive_mlc_write in H.
    fold recursive_mlc_write in H.
    case_eq (NatMap.find a k). intros s H4.
    assert (A0 := H4). destruct (NatMap.find a k) in A0, H.
    case_eq (cc_hit_write s0 e' l0 v). intros d c s1 H5.
    assert (A1 := H5). destruct (cc_hit_write s0 e' l0 v) in A1, H. destruct l0.
    injection H; injection A0; injection A1; intros; subst; clear A0 A1.
    destruct s; destruct s1.
    assert (forall x, CacheletMap.In x w0 <-> CacheletMap.In x w1). intros.
    apply (cc_hit_write_c (single_level_cache c0 v0 w0 s) e' (address b d1) v D c
    (single_level_cache c1 v1 w1 s0) c0 v0 w0 s c1 v1 w1 s0 x H5).
    reflexivity. reflexivity.
    assert (forall x, NatMap.In x s <-> NatMap.In x s0).
    apply (cc_hit_write_r (single_level_cache c0 v0 w0 s) e' (address b d1) v D c
    (single_level_cache c1 v1 w1 s0) c0 v0 w0 s c1 v1 w1 s0 H5).
    reflexivity. reflexivity.
    {
      case_eq (eqb a index).
      {
        intros H7. apply cmp_to_eq in H7. subst.
        rewrite -> H0 in H4.
        injection H4; intros X0 X1 X2 X3; subst c0 v0 w0 s.
        assert (NatMap.find index (NatMap.add index (single_level_cache c1 v1 w1 s0) k) =
        Some (single_level_cache c1 v1 w1 s0)).
        apply NatMapFacts.add_eq_o. reflexivity.
        rewrite -> H7 in H1.
        injection H1; intros; subst c1 v1 w1 s0.
        apply H3. apply (H6 w s3). apply H2. exact H15.
      }
      {
        intros. apply cmp_to_uneq in H7.
        assert (NatMap.find index (NatMap.add a (single_level_cache c1 v1 w1 s0) k) = NatMap.find index k).
        apply NatMapFacts.add_neq_o. exact H7.
        rewrite -> H1 in H8.
        rewrite -> H0 in H8.
        injection H8; intros; subst F' V' C' R'.
        apply (H6 w s3). exact H15.
      }
    }
    discriminate.
    destruct (cc_hit_write s0 e' l0).
    discriminate.
    case_eq (recursive_mlc_write k e' m0 l0 v l). intros d o m m1 H7.
    assert (A1 := H7). destruct (recursive_mlc_write k e' m0 l0 v l) in A1, H.
    case_eq (cc_update s0 e' d0 l0). intros c s1 H8.
    assert (A2 := H8). destruct (cc_update s0 e' d0 l0) in A2, H.
    injection H; injection A0; injection A1; injection A2;
    intros X0 X1 X2 X3 X4 X5 X6 X7 X8 X9 X10 X11; subst; clear A0 A1 A2.
    {
      case_eq (eqb index a).
      {
        intros. apply cmp_to_eq in H2. subst a.
        destruct s.
        destruct s1.
        assert (forall c, CacheletMap.In c w0 <-> CacheletMap.In c w1); intros.
        apply (cc_update_c (single_level_cache c0 v0 w0 s) e' D l0 c (single_level_cache c1 v1 w1 s1)
        c0 v0 w0 s c1 v1 w1 s1 c2 H8). reflexivity. reflexivity.
        assert (forall x, NatMap.In x s <-> NatMap.In x s1).
        apply (cc_update_r (single_level_cache c0 v0 w0 s) e' D l0 c (single_level_cache c1 v1 w1 s1)
        c0 v0 w0 s c1 v1 w1 s1 H8). reflexivity. reflexivity.
        assert (NatMap.find index (NatMap.add index (single_level_cache c1 v1 w1 s1) m1) =
        Some (single_level_cache c1 v1 w1 s1)).
        apply NatMapFacts.add_eq_o. reflexivity.
        rewrite -> H4 in H0.
        rewrite -> H9 in H1.
        injection H0; injection H1; intros; subst.
        apply H5. apply (H6 w s0). apply H2. exact H3.
      }
      {
        intros H2. apply cmp_to_uneq in H2.
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
          injection WFH2; intros X0; subst.
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

(* WF7-1 MLC Deallocation *)
Lemma wf7_1_clear_remapping_list : forall r l F V C R F' V' C' R',
  clear_remapping_list r l F V C R = Some (single_level_cache F' V' C' R') ->
  NatMap.find r V = Some l ->
  (forall w s, CacheletMap.In (w, s) C -> NatMap.In s R) ->
  (forall w s, CacheletMap.In (w, s) C' -> NatMap.In s R').
Proof.
  intros r l.
  induction l.
  {
    intros F V C R F' V' C' R' H H0 H3.
    unfold clear_remapping_list in H.
    injection H; intros; subst.
    apply (H3 w s). exact H6.
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
      intros w1 s0.
      apply (cachelet_invalidation_c (w1, s0) (w, s) C w0) in H5.
      intros.
      apply NatMapFacts.add_in_iff.
      right. apply (H3 w1 s0). apply H5. exact H1.
    }
    discriminate.
    intros; destruct (cachelet_invalidation C (w, s)); discriminate.
    discriminate.
    intros; destruct (NatMap.find s R); discriminate.
  }
Qed.

Lemma wf7_1_mlc_dealloc : forall lambda h_tree state k k' index psi psi' F V C R F' V' C' R',
  well_defined_cache_tree h_tree ->
  mlc_deallocation state k lambda h_tree = Some k' ->
  NatMap.find index k = Some psi ->
  NatMap.find index k' = Some psi' ->
  psi = single_level_cache F V C R ->
  psi' = single_level_cache F' V' C' R' ->
  (forall w s, CacheletMap.In (w, s) C -> NatMap.In s R) ->
  (forall w s, CacheletMap.In (w, s) C' -> NatMap.In s R').
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
    apply (H6 w s). exact H5.
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
    injection A0; injection A1; intros X0 X1; subst s0 s2; clear A0 A1.
    assert (WFH1 := WFH).
    unfold well_defined_cache_tree in WFH1.
    destruct WFH1 as [ WFH1 WFH2 ]. destruct WFH2 as [ WFH2 WFH3 ]. destruct WFH3 as [ WFH3 WFH4 ].
    case_eq (eqb index a).
    {
      intros H9; apply cmp_to_eq in H9; subst a.
      rewrite -> H7 in H0.
      injection H0; intros X0; subst s.
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
        apply (wf7_1_clear_remapping_list r r0 F V C R c v w s).
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
        injection WFH2; intros X0; subst p0.
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
        apply (wf7_1_clear_remapping_list r r0 F V C R c v w s).
        exact H8. exact H10. exact H6.
        discriminate.
        intros; destruct (NatMap.find r v0).
        discriminate.
        discriminate.
      }
    }
    {
      intros H4; apply cmp_to_uneq in H4.
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
        injection WFH2; intros X0; subst p0.
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

(* WF7-1 Preservation *)
Lemma wf7_1_preservation : forall sigma obs sigma' obs',
  wf7_1 sigma -> <<sigma; obs>> ===> <<sigma'; obs'>> -> wf7_1 sigma'.
Proof.
  destruct sigma; destruct sigma'.
  unfold wf7_1 in *.
  intros obs' H H0 k mu rho pi lambda F V C R H1 H2; injection H1. intros X0 X1 X2 X3; subst.
  inversion H0. inversion H14; subst.
  - case_eq (NatMap.find lambda m). intros s0 H4; subst.
    destruct s0.
    apply (wf7_1_mlc_read lambda0 h_tree m e' mu l0 D delta obs0 k lambda (single_level_cache c v w s)
    (single_level_cache F V C R) c v w s F V C R).
    exact H22. exact H33. exact H4. exact H2.
    reflexivity. reflexivity.
    apply (H m mu rho p lambda c v w s).
    reflexivity. exact H4.
    intros H4. apply (wf_mlc_read_none lambda0 h_tree m e' mu l0 D delta obs0 k lambda) in H4.
    rewrite -> H2 in H4.
    discriminate. exact H22. exact H33.
  - case_eq (NatMap.find lambda m). intros s H3; subst.
    destruct s.
    apply (wf7_1_mlc_alloc lambda0 h_tree r_bar_val n m k lambda (single_level_cache c v w s)
    (single_level_cache F V C R) c v w s F V C R).
    exact H29. exact H39. exact H3. exact H2.
    reflexivity. reflexivity.
    apply (H m mu rho p lambda c v w s).
    reflexivity. exact H3.
    intros H3. apply (wf_mlc_alloc_none lambda0 h_tree r_bar_val n m k lambda) in H39.
    rewrite -> H39 in H2.
    discriminate. exact H29. exact H3.
  - case_eq (NatMap.find lambda m). intros s H3; subst.
    destruct s.
    apply (wf7_1_mlc_write lambda0 h_tree m e' m0 l0 v D obs1 mu k lambda (single_level_cache c v0 w s)
    (single_level_cache F V C R) c v0 w s F V C R).
    exact H22. exact H33. exact H3. exact H2.
    reflexivity. reflexivity.
    apply (H m m0 rho p lambda c v0 w s).
    reflexivity. exact H3.
    intros H3. apply (wf_mlc_write_none lambda0 h_tree m e' m0 l0 v D obs1 mu k lambda) in H3.
    rewrite -> H2 in H3.
    discriminate. exact H22. exact H33.
  - case_eq (NatMap.find lambda m). intros s H3; subst.
    destruct s.
    apply (wf7_1_mlc_dealloc lambda0 h_tree r_val m k lambda (single_level_cache c v w s)
    (single_level_cache F V C R) c v w s F V C R).
    exact H26. exact H34. exact H3. exact H2. reflexivity. reflexivity.
    apply (H m m0 rho p lambda c v w s).
    reflexivity. exact H3.
    intros H3. apply (wf_mlc_dealloc_none lambda0 h_tree r_val m k lambda) in H34.
    rewrite -> H34 in H2.
    discriminate. exact H26. exact H3.
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

(* Well-Formed 7-2 *)
Definition wf7_2 (sigma: runtime_state): Prop :=
  forall k mu rho pi lambda F V C R,
  sigma = runtime_state_value k mu rho pi ->
  (NatMap.find lambda k = Some (single_level_cache F V C R)) ->
  (forall s, NatMap.In s R -> exists w, CacheletMap.In (w, s) C).

(* WF7-2 MLC Read *)
Lemma wf7_2_mlc_read : forall lambda h_tree k e' m0 l0 D obs1 mu k' index psi psi'
  F V C R F' V' C' R',
  well_defined_cache_tree h_tree ->
  mlc_read k e' m0 l0 lambda h_tree = mlc_read_valid D obs1 mu k' ->
  NatMap.find index k = Some psi ->
  NatMap.find index k' = Some psi' ->
  psi = single_level_cache F V C R ->
  psi' = single_level_cache F' V' C' R' ->
  (forall s, NatMap.In s R -> exists w, CacheletMap.In (w, s) C) ->
  (forall s, NatMap.In s R' -> exists w, CacheletMap.In (w, s) C').
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
    apply (H8 s). exact H9. discriminate.
  }
  {
    intros lambda IHTREE k e' m0 l0 D obs1 mu k' index psi psi' F V C R
    F' V' C' R' H H0 H1 H2 H3 H4 H7.
    unfold recursive_mlc_read in H0.
    fold recursive_mlc_read in H0.
    case_eq (NatMap.find a k). intros s1 H5.
    assert (A0 := H5). destruct (NatMap.find a k) in A0, H0.
    case_eq (cc_hit_read s e' l0). intros d d0 c s2 H6.
    assert (A1 := H6). destruct (cc_hit_read s e' l0) in A1, H0.
    injection H0; injection A0; injection A1;
    intros X0 X1 X2 X3 X4 X5 X6 X7 X8; subst; clear A0 A1.
    assert (H8:= H6).
    destruct s1; destruct s2.
    apply (cc_hit_read_c (single_level_cache c0 v w s) e' l0 D obs1 c
    (single_level_cache c1 v0 w0 s0) c0 v w s c1 v0 w0 s0) in H6.
    assert (forall x, NatMap.In x s <-> NatMap.In x s0).
    apply (cc_hit_read_r (single_level_cache c0 v w s) e' l0 D obs1 c
    (single_level_cache c1 v0 w0 s0) c0 v w s c1 v0 w0 s0 H8).
    subst. reflexivity. reflexivity.
    {
      case_eq (eqb a index).
      {
        intros. apply cmp_to_eq in H4. subst.
        rewrite -> H1 in H5.
        injection H5; intros; subst c0 v w0 s.
        assert (NatMap.find index (NatMap.add index (single_level_cache c1 v0 C s0) k) =
        Some (single_level_cache c1 v0 C s0)).
        apply NatMapFacts.add_eq_o. reflexivity.
        rewrite -> H2 in H4; injection H4; intros; subst.
        apply (H7 s1). apply H3. exact H9.
      }
      {
        intros. apply cmp_to_uneq in H4.
        assert (NatMap.find index (NatMap.add a (single_level_cache c1 v0 w0 s0) k) = NatMap.find index k).
        apply NatMapFacts.add_neq_o. exact H4.
        rewrite -> H2 in H10.
        rewrite -> H1 in H10.
        injection H10; intros; subst F' V' C' R'.
        apply (H7 s1). exact H9.
      }
    }
    reflexivity.
    reflexivity.
    discriminate.
    destruct (cc_hit_read s e' l0).
    intros; discriminate.
    intros H8.
    case_eq (recursive_mlc_read k e' m0 l0 l). intros d d0 o m H9.
    assert (A1 := H9). destruct (recursive_mlc_read k e' m0 l0 l) in A1, H0.
    case_eq (cc_update s e' d1 l0). intros c s0 H10.
    assert (A2 := H10). destruct (cc_update s e' d1 l0) in A2, H0.
    injection H0; injection A0; injection A1; injection A2;
    intros X0 X1 X2 X3 X4 X5 X6 X7 X8 X9 X10; subst; clear A0 A1 A2.
    {
      case_eq (eqb index a).
      {
        intros H3. apply cmp_to_eq in H3. subst a.
        destruct s1. destruct s0.
        assert (forall c, CacheletMap.In c w <-> CacheletMap.In c w0); intros.
        apply (cc_update_c (single_level_cache c0 v w s) e' D l0 c (single_level_cache c1 v0 w0 s0)
        c0 v w s c1 v0 w0 s0 c2 H10). reflexivity. reflexivity.
        assert (forall x, NatMap.In x s <-> NatMap.In x s0).
        apply (cc_update_r (single_level_cache c0 v w s) e' D l0 c (single_level_cache c1 v0 w0 s0)
        c0 v w s c1 v0 w0 s0 H10). reflexivity. reflexivity.
        subst.
        assert (NatMap.find index (NatMap.add index (single_level_cache c1 v0 w0 s0) m) =
        Some (single_level_cache c1 v0 w0 s0)).
        apply NatMapFacts.add_eq_o. reflexivity.
        rewrite -> H11 in H2.
        rewrite -> H5 in H1.
        injection H1; injection H2; intros; subst.
        assert (forall s', (exists w', CacheletMap.In (w', s') C) <->
        (exists w', CacheletMap.In (w', s') C')).
        split; intros; destruct H12 as (w' & H12);
        eexists w'; apply H3; exact H12.
        apply H12. apply (H7 s1). apply H6. exact H4.
      }
      {
        intros H3. apply cmp_to_uneq in H3.
        assert (WFH := H).
        unfold well_defined_cache_tree in H.
        destruct H as [ WFH1 ]. destruct H as [ WFH2 ]. destruct H as [ WFH3 ].
        destruct l.
        {
          apply (IHl root_node WFH1 k e' m0 l0 D obs1 o m index (single_level_cache F V C R)
          (single_level_cache F' V' C' R') F V C R F' V' C' R').
          exact WFH.
          unfold mlc_write. exact H9.
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
          injection WFH2; intros X0; subst.
          apply (H p0 p l) in IHTREE.
          apply (IHl (cache_node p) IHTREE k e' m0 l0 D obs1 o m index (single_level_cache F V C R)
          (single_level_cache F' V' C' R') F V C R F' V' C' R').
          exact WFH.
          unfold mlc_write. exact H9.
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
    intros; destruct (cc_update s e' d1 l0); discriminate.
    discriminate.
    intros; destruct (recursive_mlc_read k e' m0 l0 l); discriminate.
    discriminate.
    intros; destruct (NatMap.find a k); discriminate.
  }
  intros; destruct (get_cache_ID_path lambda h_tree); discriminate.
Qed.

(* WF7-2 MLC Allocation *)
Lemma wf7_2_cachelet_allocation : forall n r F V C R F' V' C' R',
  cachelet_allocation n r (single_level_cache F V C R) = Some (single_level_cache F' V' C' R') ->
  (forall s, NatMap.In s R -> exists w, CacheletMap.In (w, s) C) ->
  (forall s, NatMap.In s R' -> exists w, CacheletMap.In (w, s) C').
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
    apply (H0 s). exact H1.
  }
  {
    intros F V C R F' V' C' R' H H0.
    unfold recursive_cachelet_allocation in H.
    fold recursive_cachelet_allocation in H.
    case_eq (way_first_allocation F). intros c H2.
    assert (A0 := H2); destruct (way_first_allocation F) in H, A0.
    destruct c0.
    case_eq (NatMap.find s R). intros p H3.
    assert (A1 := H3); destruct (NatMap.find s R) in H, A1.
    case_eq (remove_CAT (w, s) F). intros c0 F0.
    assert (A3 := F0). destruct (remove_CAT (w, s) F) in H, A3.
    case_eq (NatMap.find r V). intros r0 H5.
    assert (A2 := H5). destruct (NatMap.find r V) in H, A2.
    injection A0; injection A1; injection A2; injection A3;
    intros X0 X1 X2 X3; subst; clear A0 A1 A2 A3.
    {
      apply (IHn0 c0 (NatMap.add r ((w, s) :: r0) V) C
      (NatMap.add s (update p w (enclave_ID_active r)) R) F' V' C' R').
      exact H. intros. apply H0.
      apply NatMapFacts.add_in_iff in H1.
      destruct H1. subst.
      apply NatMapFacts.in_find_iff. intros contra.
      rewrite -> H3 in contra. discriminate. exact H1.
    }
    discriminate.
    intros H5; assert (A2 := H5); destruct (NatMap.find r V) in A2, H.
    discriminate.
    assert (L0 := H2).
    injection A0; injection A1; injection A3; intros X0 X1 X2; subst; clear A0 A1 A2 A3.
    {
      apply (IHn0 c0 (NatMap.add r ((w, s) :: nil) V) C
      (NatMap.add s (update p w (enclave_ID_active r)) R) F' V' C' R').
      exact H. intros. apply H0.
      apply NatMapFacts.add_in_iff in H1.
      destruct H1. subst.
      apply NatMapFacts.in_find_iff. intros contra.
      rewrite -> H3 in contra. discriminate. exact H1.
    }
    discriminate.
    intros; destruct (remove_CAT (w, s) F); discriminate.
    discriminate.
    intros; destruct (NatMap.find s R); discriminate.
    discriminate.
    intros; destruct (way_first_allocation F); discriminate.
  }
Qed.

Lemma wf7_2_mlc_alloc : forall lambda h_tree n state k k' index psi psi' F V C R F' V' C' R',
  well_defined_cache_tree h_tree ->
  mlc_allocation n state k lambda h_tree = Some k' ->
  NatMap.find index k = Some psi ->
  NatMap.find index k' = Some psi' ->
  psi = single_level_cache F V C R ->
  psi' = single_level_cache F' V' C' R' ->
  (forall s, NatMap.In s R -> exists w, CacheletMap.In (w, s) C) ->
  (forall s, NatMap.In s R' -> exists w, CacheletMap.In (w, s) C').
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
    apply (H6 s). exact H3.
  }
  {
    intros lambda IHTREE n r k k' index psi psi' F V C R
    F' V' C' R' WFH H H0 H1 H4 H5 H6.
    unfold recursive_mlc_allocation in H.
    fold recursive_mlc_allocation in H.
    destruct n. discriminate.
    case_eq (NatMap.find a k). intros s H2.
    assert (A0 := H2). destruct (NatMap.find a k) in A0, H.
    case_eq (cachelet_allocation n r s0). intros s1 H7.
    assert (A1 := H7). destruct (cachelet_allocation n r s0) in A1, H.
    injection A0; injection A1; intros X0 X1; subst s2 s0; clear A0 A1.
    assert (WFH1 := WFH).
    unfold well_defined_cache_tree in WFH1.
    destruct WFH1 as [ WFH1 WFH2 ]. destruct WFH2 as [ WFH2 WFH3 ]. destruct WFH3 as [ WFH3 WFH4 ].
    case_eq (eqb index a).
    {
      intros H8; apply cmp_to_eq in H8; subst a.
      rewrite -> H2 in H0.
      injection H0; intros X0; subst s.
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
        apply (wf7_2_cachelet_allocation n r F V C R c v w s).
        subst psi psi'; exact H7. exact H6.
      }
      {
        destruct lambda.
        rewrite -> WFH1 in IHTREE. discriminate.
        specialize (WFH3 c0 index (p :: l) IHTREE).
        unfold get_cache_ID_path in IHTREE. discriminate.
        specialize (WFH2 p0 index (p :: l) IHTREE).
        injection WFH2; intros X0; subst p0.
        apply (WFH4 index p l) in IHTREE.
        apply (IHl (cache_node p) IHTREE n0 r (NatMap.add index (single_level_cache c v w s) k)
        k' index (single_level_cache c v w s) psi' c v w s F' V' C' R').
        exact WFH.
        exact H.
        apply NatMapFacts.add_eq_o. reflexivity.
        exact H1.
        reflexivity.
        exact H5.
        apply (wf7_2_cachelet_allocation n r F V C R c v w s).
        subst psi psi'; exact H7. exact H6.
      }
    }
    {
      intros H8; apply cmp_to_uneq in H8.
      destruct l.
      {
        apply (IHl root_node WFH1 n0 r (NatMap.add a s1 k) k' index psi psi' F V C R F' V' C' R').
        exact WFH.
        unfold mlc_allocation. exact H.
        rewrite <- H0. apply NatMapFacts.add_neq_o.
        apply not_eq_sym. exact H8.
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
        injection WFH2; intros X0; subst p0.
        apply (WFH4 a p l) in IHTREE.
        apply (IHl (cache_node p) IHTREE n0 r (NatMap.add a s1 k) k' index psi psi' F V C R F' V' C' R').
        exact WFH.
        unfold mlc_allocation. exact H.
        rewrite <- H0. apply NatMapFacts.add_neq_o.
        apply not_eq_sym. exact H8.
        exact H1.
        exact H4.
        exact H5.
        exact H6.
      }
    }
    discriminate.
    intros; destruct (cachelet_allocation n r s0); discriminate.
    discriminate.
    intros; destruct (NatMap.find a k); discriminate.
  }
  intros; destruct (get_cache_ID_path lambda h_tree); discriminate.
Qed.

(* WF7-2 MLC Write *)
Lemma wf7_2_mlc_write : forall lambda h_tree k e' m0 l0 v D obs1 mu k' index psi psi'
  F V C R F' V' C' R',
  well_defined_cache_tree h_tree ->
  mlc_write k e' m0 l0 v lambda h_tree = mlc_write_valid D obs1 mu k' ->
  NatMap.find index k = Some psi ->
  NatMap.find index k' = Some psi' ->
  psi = single_level_cache F V C R ->
  psi' = single_level_cache F' V' C' R' ->
  (forall s, NatMap.In s R -> exists w, CacheletMap.In (w, s) C) ->
  (forall s, NatMap.In s R' -> exists w, CacheletMap.In (w, s) C').
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
    apply (H6 s). exact H5.
    discriminate.
    discriminate.
  }
  {
    intros lambda IHTREE k e' m0 l0 v D obs1 mu k' index psi psi'
    F V C R F' V' C' R' WFH1 H H0 H1 H2 H3 H6.
    unfold recursive_mlc_write in H.
    fold recursive_mlc_write in H.
    case_eq (NatMap.find a k). intros s H4.
    assert (A0 := H4). destruct (NatMap.find a k) in A0, H.
    case_eq (cc_hit_write s0 e' l0 v). intros d c s1 H5.
    assert (A1 := H5). destruct (cc_hit_write s0 e' l0 v) in A1, H. destruct l0.
    injection H; injection A0; injection A1; intros; subst; clear A0 A1.
    destruct s; destruct s1.
    assert (forall x, CacheletMap.In x w <-> CacheletMap.In x w0). intros.
    apply (cc_hit_write_c (single_level_cache c0 v0 w s) e' (address b d1) v D c
    (single_level_cache c1 v1 w0 s0) c0 v0 w s c1 v1 w0 s0 x H5).
    reflexivity. reflexivity.
    assert (forall x, NatMap.In x s <-> NatMap.In x s0).
    apply (cc_hit_write_r (single_level_cache c0 v0 w s) e' (address b d1) v D c
    (single_level_cache c1 v1 w0 s0) c0 v0 w s c1 v1 w0 s0 H5).
    reflexivity. reflexivity.
    {
      case_eq (eqb a index).
      {
        intros H7. apply cmp_to_eq in H7. subst.
        rewrite -> H0 in H4.
        injection H4; intros X0 X1 X2 X3; subst c0 v0 w s.
        assert (NatMap.find index (NatMap.add index (single_level_cache c1 v1 w0 s0) k) =
        Some (single_level_cache c1 v1 w0 s0)).
        apply NatMapFacts.add_eq_o. reflexivity.
        rewrite -> H7 in H1.
        injection H1; intros; subst c1 v1 w0 s0.
        assert (forall s', (exists w', CacheletMap.In (w', s') C) <->
        (exists w', CacheletMap.In (w', s') C')).
        split; intros; destruct H8 as (w' & H8);
        eexists w'; apply H2; exact H8.
        apply H8. apply (H6 s3). apply H3. exact H15.
      }
      {
        intros. apply cmp_to_uneq in H7.
        assert (NatMap.find index (NatMap.add a (single_level_cache c1 v1 w0 s0) k) = NatMap.find index k).
        apply NatMapFacts.add_neq_o. exact H7.
        rewrite -> H1 in H8.
        rewrite -> H0 in H8.
        injection H8; intros; subst F' V' C' R'.
        apply (H6 s3). exact H15.
      }
    }
    discriminate.
    destruct (cc_hit_write s0 e' l0).
    discriminate.
    case_eq (recursive_mlc_write k e' m0 l0 v l). intros d o m m1 H7.
    assert (A1 := H7). destruct (recursive_mlc_write k e' m0 l0 v l) in A1, H.
    case_eq (cc_update s0 e' d0 l0). intros c s1 H8.
    assert (A2 := H8). destruct (cc_update s0 e' d0 l0) in A2, H.
    injection H; injection A0; injection A1; injection A2;
    intros X0 X1 X2 X3 X4 X5 X6 X7 X8 X9 X10 X11; subst; clear A0 A1 A2.
    {
      case_eq (eqb index a).
      {
        intros. apply cmp_to_eq in H2. subst a.
        destruct s.
        destruct s1.
        assert (forall c, CacheletMap.In c w <-> CacheletMap.In c w0); intros.
        apply (cc_update_c (single_level_cache c0 v0 w s) e' D l0 c (single_level_cache c1 v1 w0 s1)
        c0 v0 w s c1 v1 w0 s1 c2 H8). reflexivity. reflexivity.
        assert (forall x, NatMap.In x s <-> NatMap.In x s1).
        apply (cc_update_r (single_level_cache c0 v0 w s) e' D l0 c (single_level_cache c1 v1 w0 s1)
        c0 v0 w s c1 v1 w0 s1 H8). reflexivity. reflexivity.
        assert (NatMap.find index (NatMap.add index (single_level_cache c1 v1 w0 s1) m1) =
        Some (single_level_cache c1 v1 w0 s1)).
        apply NatMapFacts.add_eq_o. reflexivity.
        rewrite -> H4 in H0.
        rewrite -> H9 in H1.
        injection H0; injection H1; intros; subst.
        assert (forall s', (exists w', CacheletMap.In (w', s') C) <->
        (exists w', CacheletMap.In (w', s') C')).
        split; intros; destruct H10 as (w' & H10);
        eexists w'; apply H2; exact H10.
        apply H10. apply (H6 s0). apply H5. exact H3.
      }
      {
        intros H2. apply cmp_to_uneq in H2.
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
          injection WFH2; intros X0; subst.
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

(* WF7-2 MLC Deallocation *)
Lemma wf7_2_clear_remapping_list : forall r l F V C R F' V' C' R',
  clear_remapping_list r l F V C R = Some (single_level_cache F' V' C' R') ->
  NatMap.find r V = Some l ->
  (forall s, NatMap.In s R -> exists w, CacheletMap.In (w, s) C) ->
  (forall s, NatMap.In s R' -> exists w, CacheletMap.In (w, s) C').
Proof.
  intros r l.
  induction l.
  {
    intros F V C R F' V' C' R' H H0 H3.
    unfold clear_remapping_list in H.
    injection H; intros; subst.
    apply (H3 s). exact H6.
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
      intros s0 H1.
      assert (forall c, CacheletMap.In c C <-> CacheletMap.In c w0).
      intros c. apply (cachelet_invalidation_c c (w, s) C w0 H5).
      assert (forall s, (exists w, CacheletMap.In (w, s) C) <->
      (exists w, CacheletMap.In (w, s) w0)).
      split; intros H10; destruct H10 as (w' & H10);
      eexists w'; apply H2; exact H10.
      apply H6. apply H3.
      apply NatMapFacts.add_in_iff in H1.
      destruct H1. subst. apply NatMapFacts.in_find_iff.
      intros contra. rewrite -> H4 in contra. discriminate. exact H1.
    }
    discriminate.
    intros; destruct (cachelet_invalidation C (w, s)); discriminate.
    discriminate.
    intros; destruct (NatMap.find s R); discriminate.
  }
Qed.

Lemma wf7_2_mlc_dealloc : forall lambda h_tree state k k' index psi psi' F V C R F' V' C' R',
  well_defined_cache_tree h_tree ->
  mlc_deallocation state k lambda h_tree = Some k' ->
  NatMap.find index k = Some psi ->
  NatMap.find index k' = Some psi' ->
  psi = single_level_cache F V C R ->
  psi' = single_level_cache F' V' C' R' ->
  (forall s, NatMap.In s R -> exists w, CacheletMap.In (w, s) C) ->
  (forall s, NatMap.In s R' -> exists w, CacheletMap.In (w, s) C').
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
    apply (H6 s). exact H5.
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
    injection A0; injection A1; intros X0 X1; subst s0 s2; clear A0 A1.
    assert (WFH1 := WFH).
    unfold well_defined_cache_tree in WFH1.
    destruct WFH1 as [ WFH1 WFH2 ]. destruct WFH2 as [ WFH2 WFH3 ]. destruct WFH3 as [ WFH3 WFH4 ].
    case_eq (eqb index a).
    {
      intros H9; apply cmp_to_eq in H9; subst a.
      rewrite -> H7 in H0.
      injection H0; intros X0; subst s.
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
        apply (wf7_2_clear_remapping_list r r0 F V C R c v w s).
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
        injection WFH2; intros X0; subst p0.
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
        apply (wf7_2_clear_remapping_list r r0 F V C R c v w s).
        exact H8. exact H10. exact H6.
        discriminate.
        intros; destruct (NatMap.find r v0).
        discriminate.
        discriminate.
      }
    }
    {
      intros H4; apply cmp_to_uneq in H4.
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
        injection WFH2; intros X0; subst p0.
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

(* WF7-2 Preservation *)
Lemma wf7_2_preservation : forall sigma obs sigma' obs',
  wf7_2 sigma -> <<sigma; obs>> ===> <<sigma'; obs'>> -> wf7_2 sigma'.
Proof.
  destruct sigma; destruct sigma'.
  unfold wf7_1 in *.
  intros obs' H H0 k mu rho pi lambda F V C R H1 H2; injection H1. intros X0 X1 X2 X3; subst.
  inversion H0. inversion H14; subst.
  - case_eq (NatMap.find lambda m). intros s0 H4; subst.
    destruct s0.
    apply (wf7_2_mlc_read lambda0 h_tree m e' mu l0 D delta obs0 k lambda (single_level_cache c v w s)
    (single_level_cache F V C R) c v w s F V C R).
    exact H22. exact H33. exact H4. exact H2.
    reflexivity. reflexivity.
    apply (H m mu rho p lambda c v w s).
    reflexivity. exact H4.
    intros H4. apply (wf_mlc_read_none lambda0 h_tree m e' mu l0 D delta obs0 k lambda) in H4.
    rewrite -> H2 in H4.
    discriminate. exact H22. exact H33.
  - case_eq (NatMap.find lambda m). intros s H3; subst.
    destruct s.
    apply (wf7_2_mlc_alloc lambda0 h_tree r_bar_val n m k lambda (single_level_cache c v w s)
    (single_level_cache F V C R) c v w s F V C R).
    exact H29. exact H39. exact H3. exact H2.
    reflexivity. reflexivity.
    apply (H m mu rho p lambda c v w s).
    reflexivity. exact H3.
    intros H3. apply (wf_mlc_alloc_none lambda0 h_tree r_bar_val n m k lambda) in H39.
    rewrite -> H39 in H2.
    discriminate. exact H29. exact H3.
  - case_eq (NatMap.find lambda m). intros s H3; subst.
    destruct s.
    apply (wf7_2_mlc_write lambda0 h_tree m e' m0 l0 v D obs1 mu k lambda (single_level_cache c v0 w s)
    (single_level_cache F V C R) c v0 w s F V C R).
    exact H22. exact H33. exact H3. exact H2.
    reflexivity. reflexivity.
    apply (H m m0 rho p lambda c v0 w s).
    reflexivity. exact H3.
    intros H3. apply (wf_mlc_write_none lambda0 h_tree m e' m0 l0 v D obs1 mu k lambda) in H3.
    rewrite -> H2 in H3.
    discriminate. exact H22. exact H33.
  - case_eq (NatMap.find lambda m). intros s H3; subst.
    destruct s.
    apply (wf7_2_mlc_dealloc lambda0 h_tree r_val m k lambda (single_level_cache c v w s)
    (single_level_cache F V C R) c v w s F V C R).
    exact H26. exact H34. exact H3. exact H2. reflexivity. reflexivity.
    apply (H m m0 rho p lambda c v w s).
    reflexivity. exact H3.
    intros H3. apply (wf_mlc_dealloc_none lambda0 h_tree r_val m k lambda) in H34.
    rewrite -> H34 in H2.
    discriminate. exact H26. exact H3.
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

(* Well-Formed 8 *)
Fixpoint recursive_way_ID_in (w : way_ID) (T : PLRU_tree): Prop :=
  match T with
  | subtree sigma e T1 T2 => (recursive_way_ID_in w T1) \/ (recursive_way_ID_in w T2)
  | subtree_leaf L => 
    match L with
    | leaf w' e => w = w'
    end
  end.
Definition way_ID_in (w: way_ID) (T: PLRU_tree): Prop := recursive_way_ID_in w T.
Lemma contains_way_ID_iff : forall w T,
  contains_way_ID w T = true <-> way_ID_in w T.
Proof.
  intros.
  induction T.
  unfold contains_way_ID in *; unfold recursive_contains_way_ID.
  unfold way_ID_in in *; unfold recursive_way_ID_in.
  fold recursive_contains_way_ID; fold recursive_way_ID_in.
  split; intros. apply orb_prop in H.
  destruct H.
  apply IHT1 in H. left; exact H.
  apply IHT2 in H. right; exact H.
  apply orb_true_intro. destruct H.
  apply IHT1 in H. left; exact H.
  apply IHT2 in H. right; exact H.
  unfold way_ID_in; unfold recursive_way_ID_in.
  unfold contains_way_ID; unfold recursive_contains_way_ID.
  destruct p.
  split; intros.
  apply cmp_to_eq in H; exact H.
  subst. apply eq_to_cmp. reflexivity.
Qed.

(* Well-Formed 8-1 *)
Definition wf8_1 (sigma: runtime_state): Prop :=
  forall k mu rho pi lambda F V C R,
  sigma = runtime_state_value k mu rho pi ->
  (NatMap.find lambda k = Some (single_level_cache F V C R)) ->
  (forall w s, CacheletMap.In (w, s) C -> exists y T, way_ID_in w T
  /\ NatMap.find y R = Some T).

Lemma way_ID_in_update : forall x S w e,
  way_ID_in x S <-> way_ID_in x (update S w e).
Proof.
  intros; split; intros; induction S.
  unfold update in *. unfold recursive_update.
  fold recursive_update.
  unfold way_ID_in in *. unfold recursive_way_ID_in in H.
  unfold recursive_way_ID_in. fold recursive_way_ID_in in *.
  destruct (equal_enclave_IDs e e0).
  case_eq (contains_way_ID w S1); intros.
  destruct H. apply IHS1 in H. left; exact H.
  right; exact H.
  case_eq (contains_way_ID w S2); intros.
  destruct H.
  unfold recursive_way_ID_in. fold recursive_way_ID_in in *.
  left; exact H.
  right. apply IHS2 in H. exact H.
  destruct H. left; exact H.
  right; exact H.
  destruct H.
  left; apply IHS1; exact H.
  right; apply IHS2; exact H.
  unfold update. unfold recursive_update.
  destruct p. destruct e0. exact H.
  case_eq (eqb w w0); intros.
  apply cmp_to_eq in H0; subst.
  exact H. exact H.
  unfold update in *. unfold recursive_update in H.
  fold recursive_update in H.
  unfold way_ID_in in *. 
  destruct (equal_enclave_IDs e e0).
  destruct (contains_way_ID w S1).
  unfold recursive_way_ID_in in *. fold recursive_way_ID_in in *.
  destruct H. apply IHS1 in H. left; exact H.
  right; exact H.
  destruct (contains_way_ID w S2).
  unfold recursive_way_ID_in in *. fold recursive_way_ID_in in *.
  destruct H. left; exact H.
  apply IHS2 in H. right; exact H.
  unfold recursive_way_ID_in in *. fold recursive_way_ID_in in *.
  exact H.
  unfold recursive_way_ID_in in *. fold recursive_way_ID_in in *.
  destruct H.
  apply IHS1 in H. left; exact H.
  apply IHS2 in H. right; exact H.
  unfold update in H. unfold recursive_update in H.
  destruct p. destruct e0.
  exact H.
  case_eq (eqb w w0); intros; assert (A0 := H0);
  destruct (eqb w w0) in H, A0.
  apply cmp_to_eq in H0. subst.
  exact H. discriminate.
  discriminate.
  exact H.
Qed.

(* WF8-1 MLC Read *)
Lemma cc_hit_read_r_range : forall psi e mem l D delta c psi' F V C R F' V' C' R',
  cc_hit_read psi (enclave_state_value e mem) l = cc_hit_read_valid D delta c psi' ->
  psi = single_level_cache F V C R ->
  psi' = single_level_cache F' V' C' R' ->
  forall x, ((exists y T, way_ID_in x T /\ NatMap.find y R = Some T) <->
  (exists y T, way_ID_in x T /\ NatMap.find y R' = Some T)).
Proof.
  intros.
  subst psi psi'.
  unfold cc_hit_read in H.
  case_eq (cc_unfold (single_level_cache F V C R)
  (enclave_state_value e mem) l). intros.
  assert (A0 := H0).
  destruct (cc_unfold (single_level_cache F V C R)
  (enclave_state_value e mem) l) in A0, H.
  destruct c3.
  injection A0; intros; subst; clear A0.
  apply cc_unfold_psi in H0.
  injection H0; intros; subst c0 v w s.
  destruct w0.
  case_eq (NatMap.find s1 R). intros p H1.
  assert (A0 := H1); destruct (NatMap.find s1 R) in H, A0.
  injection A0; injection H; intros; subst; clear A0.
  split; intros.
  destruct H2 as (y & T & H2 & H3).
  case_eq (eqb y s1); intros.
  apply cmp_to_eq in H4; subst.
  rewrite -> H1 in H3. injection H3; intros; subst.
  eexists s1; eexists (update T w3 e).
  split. apply way_ID_in_update. exact H2.
  apply NatMapFacts.add_eq_o; reflexivity.
  apply cmp_to_uneq in H4.
  eexists y; eexists T.
  split. exact H2. rewrite <- H3.
  apply NatMapFacts.add_neq_o; apply not_eq_sym; exact H4.
  destruct H2 as (y & T & H2 & H3).
  case_eq (eqb y s1); intros.
  apply cmp_to_eq in H4; subst.
  assert (Some T = Some (update p w3 e)).
  rewrite <- H3. apply NatMapFacts.add_eq_o; reflexivity.
  injection H4; intros; subst.
  eexists s1; eexists p.
  split. apply way_ID_in_update in H2.
  exact H2. exact H1.
  apply cmp_to_uneq in H4.
  assert (NatMap.find y R = Some T).
  rewrite <- H3; apply eq_sym.
  apply NatMapFacts.add_neq_o; apply not_eq_sym; exact H4.
  eexists y; eexists T. split.
  exact H2. exact H5.
  discriminate.
  destruct (NatMap.find s1 R); discriminate.
  discriminate.
  destruct cc_unfold; discriminate.
Qed.

Lemma cc_update_r_range : forall psi e' d l0 c0 psi' F V C R F' V' C' R',
  cc_update psi e' d l0 = cc_update_valid c0 psi' ->
  psi = single_level_cache F V C R ->
  psi' = single_level_cache F' V' C' R' ->
  forall x, ((exists y T, way_ID_in x T /\ NatMap.find y R = Some T) <->
  (exists y T, way_ID_in x T /\ NatMap.find y R' = Some T)).
Proof.
  intros.
  subst psi psi'.
  unfold cc_update in H.
  case_eq (cc_unfold (single_level_cache F V C R) e' l0). intros.
  assert (A0 := H0). destruct (cc_unfold (single_level_cache F V C R) e' l0) in A0, H.
  assert (H1 := H0).
  apply cc_unfold_psi in H0.
  apply cc_unfold_c in H1.
  injection A0; intros; subst; clear A0.
  injection H0; intros; subst c v w s.
  destruct c1.
  destruct w0.
  destruct e'.
  case_eq (NatMap.find s R); intros.
  assert (A0 := H2); destruct (NatMap.find s R) in H, A0.
  injection A0; intros; subst; clear A0.
  destruct (replace p e).
  injection H; intros; subst.
  split; intros.
  {
    destruct H3 as (y & T & H3 & H4).
    case_eq (eqb s y); intros.
    apply cmp_to_eq in H5; subst.
    rewrite -> H2 in H4.
    injection H4; intros; subst.
    eexists y; eexists (update T w e).
    split. apply way_ID_in_update. exact H3.
    apply NatMapFacts.add_eq_o; reflexivity.
    apply cmp_to_uneq in H5.
    eexists y; eexists T. split. exact H3.
    rewrite <- H4. apply NatMapFacts.add_neq_o; exact H5.
  }
  {
    destruct H3 as (y & T & H3 & H4).
    case_eq (eqb s y); intros.
    apply cmp_to_eq in H5; subst.
    assert (Some T = Some (update p w e)).
    rewrite <- H4. apply NatMapFacts.add_eq_o; reflexivity.
    injection H5; intros; subst.
    eexists y; eexists p. split.
    apply way_ID_in_update in H3. exact H3. exact H2.
    apply cmp_to_uneq in H5.
    eexists y; eexists T. split. exact H3.
    rewrite <- H4. apply eq_sym. apply NatMapFacts.add_neq_o; exact H5.
  }
  discriminate.
  discriminate.
  destruct (NatMap.find s R); discriminate.
  discriminate.
  intros; destruct (cc_unfold (single_level_cache F V C R) e' l0).
  discriminate.
  discriminate.
Qed.

Lemma wf8_1_mlc_read : forall lambda h_tree k e' m0 l0 D obs1 mu k' index psi psi'
  F V C R F' V' C' R',
  well_defined_cache_tree h_tree ->
  mlc_read k e' m0 l0 lambda h_tree = mlc_read_valid D obs1 mu k' ->
  NatMap.find index k = Some psi ->
  NatMap.find index k' = Some psi' ->
  psi = single_level_cache F V C R ->
  psi' = single_level_cache F' V' C' R' ->
  (forall w s, CacheletMap.In (w, s) C -> exists y T, way_ID_in w T
  /\ NatMap.find y R = Some T) ->
  (forall w s, CacheletMap.In (w, s) C' -> exists y T, way_ID_in w T
  /\ NatMap.find y R' = Some T).
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
    apply (H8 w s H9). discriminate.
  }
  {
    intros lambda IHTREE k e' m0 l0 D obs1 mu k' index psi psi' F V C R
    F' V' C' R' H H0 H1 H2 H3 H4 H7.
    unfold recursive_mlc_read in H0.
    fold recursive_mlc_read in H0.
    case_eq (NatMap.find a k). intros s H5.
    assert (A0 := H5). destruct (NatMap.find a k) in A0, H0.
    case_eq (cc_hit_read s0 e' l0). intros d d0 c s1 H6.
    assert (A1 := H6). destruct (cc_hit_read s0 e' l0) in A1, H0.
    injection H0; injection A0; injection A1; intros; subst; clear A0 A1.
    assert (H8 := H6).
    destruct s; destruct s1.
    apply (cc_hit_read_c (single_level_cache c0 v w0 s) e' l0 D obs1 c
    (single_level_cache c1 v0 w1 s0) c0 v w0 s c1 v0 w1 s0) in H6.
    destruct e'.
    assert (forall x, ((exists y T, way_ID_in x T /\ NatMap.find y s = Some T) <->
    (exists y T, way_ID_in x T /\ NatMap.find y s0 = Some T))).
    apply (cc_hit_read_r_range (single_level_cache c0 v w0 s) e e0 l0 D obs1 c
    (single_level_cache c1 v0 w1 s0) c0 v w0 s c1 v0 w1 s0 H8).
    reflexivity. reflexivity.
    {
      case_eq (eqb a index).
      {
        intros. apply cmp_to_eq in H4. subst.
        rewrite -> H1 in H5.
        injection H5; intros; subst c0 v w1 s.
        assert (NatMap.find index (NatMap.add index (single_level_cache c1 v0 C s0) k) =
        Some (single_level_cache c1 v0 C s0)).
        apply NatMapFacts.add_eq_o. reflexivity.
        rewrite -> H2 in H4; injection H4; intros; subst.
        apply H3. apply (H7 w s3). exact H17.
      }
      {
        intros. apply cmp_to_uneq in H4.
        assert (NatMap.find index (NatMap.add a (single_level_cache c1 v0 w1 s0) k) = NatMap.find index k).
        apply NatMapFacts.add_neq_o. exact H4.
        rewrite -> H2 in H9.
        rewrite -> H1 in H9.
        injection H9; intros; subst F' V' C' R'.
        apply (H7 w s3). exact H17.
      }
    }
    reflexivity.
    reflexivity.
    discriminate.
    intros H6. destruct (cc_hit_read s0 e' l0).
    discriminate.
    case_eq (recursive_mlc_read k e' m0 l0 l). intros d d0 o m H8.
    assert (A1 := H8). destruct (recursive_mlc_read k e' m0 l0 l) in A1, H0.
    case_eq (cc_update s0 e' d1 l0). intros c s1 H9.
    assert (A2 := H9). destruct (cc_update s0 e' d1 l0) in A2, H0.
    injection H0; injection A0; injection A1; injection A2;
    intros X0 X1 X2 X3 X4 X5 X6 X7 X8 X9 X10; subst; clear A0 A1 A2.
    {
      case_eq (eqb index a).
      {
        intros. apply cmp_to_eq in H3. subst a.
        destruct s. destruct s1.
        assert (forall c, CacheletMap.In c w0 <-> CacheletMap.In c w1); intros.
        apply (cc_update_c (single_level_cache c0 v w0 s) e' D l0 c (single_level_cache c1 v0 w1 s1)
        c0 v w0 s c1 v0 w1 s1 c2 H9). reflexivity. reflexivity.
        assert (forall x, ((exists y T, way_ID_in x T /\ NatMap.find y s = Some T) <->
        (exists y T, way_ID_in x T /\ NatMap.find y s1 = Some T))).
        apply (cc_update_r_range (single_level_cache c0 v w0 s) e' D l0 c (single_level_cache c1 v0 w1 s1)
        c0 v w0 s c1 v0 w1 s1 H9). reflexivity. reflexivity.
        assert (NatMap.find index (NatMap.add index (single_level_cache c1 v0 w1 s1) m) =
        Some (single_level_cache c1 v0 w1 s1)).
        apply NatMapFacts.add_eq_o. reflexivity.
        rewrite -> H11 in H2.
        rewrite -> H5 in H1.
        injection H1; injection H2; intros; subst.
        apply H10. apply (H7 w s0). apply H3. exact H4.
      }
      {
        intros H3. apply cmp_to_uneq in H3.
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
          injection WFH2; intros X0; subst.
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
    intros; destruct (cc_update s0 e' d1 l0); discriminate.
    discriminate.
    intros; destruct (recursive_mlc_read k e' m0 l0 l); discriminate.
    discriminate.
    intros; destruct (NatMap.find a k); discriminate.
  }
  intros; destruct (get_cache_ID_path lambda h_tree); discriminate.
Qed.

(* WF8-1 MLC Allocation *)
Lemma wf8_1_cachelet_allocation : forall n r F V C R F' V' C' R',
  cachelet_allocation n r (single_level_cache F V C R) = Some (single_level_cache F' V' C' R') ->
  (forall w s, CacheletMap.In (w, s) C -> exists y T, way_ID_in w T
  /\ NatMap.find y R = Some T) ->
  (forall w s, CacheletMap.In (w, s) C' -> exists y T, way_ID_in w T
  /\ NatMap.find y R' = Some T).
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
    apply (H0 w s H1).
  }
  {
    intros F V C R F' V' C' R' H H0.
    unfold recursive_cachelet_allocation in H.
    fold recursive_cachelet_allocation in H.
    case_eq (way_first_allocation F). intros c H1.
    assert (A0 := H1); destruct (way_first_allocation F) in H, A0.
    destruct c0.
    case_eq (NatMap.find s R). intros p H2.
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
      exact H. intros.
      specialize (H0 w0 s0 H3).
      destruct H0 as (y & T & H0 & H4).
      case_eq (eqb s y); intros.
      apply cmp_to_eq in H6; subst.
      rewrite -> H2 in H4. injection H4; intros; subst.
      eexists y; eexists (update T w (enclave_ID_active r)). split.
      apply way_ID_in_update. exact H0.
      apply NatMapFacts.add_eq_o; reflexivity.
      apply cmp_to_uneq in H6.
      eexists y; eexists T. split. exact H0.
      rewrite <- H4. apply NatMapFacts.add_neq_o; exact H6.
    }
    discriminate.
    intros H5; assert (A2 := H5); destruct (NatMap.find r V) in A2, H.
    discriminate.
    injection A0; injection A1; injection A3; intros X0 X1 X2; subst; clear A0 A1 A2 A3.
    {
      apply (IHn0 c0 (NatMap.add r ((w, s) :: nil) V) C
      (NatMap.add s (update p w (enclave_ID_active r)) R) F' V' C' R').
      exact H. intros.
      apply H0 in H3. destruct H3 as (y & T & H3 & H4).
      case_eq (eqb s y); intros.
      apply cmp_to_eq in H6; subst.
      rewrite -> H2 in H4. injection H4; intros; subst.
      eexists y; eexists (update T w (enclave_ID_active r)).
      split. apply way_ID_in_update. exact H3.
      apply NatMapFacts.add_eq_o; reflexivity.
      apply cmp_to_uneq in H6.
      eexists y; eexists T. split. exact H3.
      rewrite <- H4. apply NatMapFacts.add_neq_o; exact H6.
    }
    discriminate.
    intros; destruct (remove_CAT (w, s) F); discriminate.
    discriminate.
    intros; destruct (NatMap.find s R); discriminate.
    discriminate.
    intros; destruct (way_first_allocation F); discriminate.
  }
Qed.

Lemma wf8_1_mlc_alloc : forall lambda h_tree n state k k' index psi psi' F V C R F' V' C' R',
  well_defined_cache_tree h_tree ->
  mlc_allocation n state k lambda h_tree = Some k' ->
  NatMap.find index k = Some psi ->
  NatMap.find index k' = Some psi' ->
  psi = single_level_cache F V C R ->
  psi' = single_level_cache F' V' C' R' ->
  (forall w s, CacheletMap.In (w, s) C -> exists y T, way_ID_in w T
  /\ NatMap.find y R = Some T) ->
  (forall w s, CacheletMap.In (w, s) C' -> exists y T, way_ID_in w T
  /\ NatMap.find y R' = Some T).
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
    exact (H6 w s H3).
  }
  {
    intros lambda IHTREE n r k k' index psi psi' F V C R
    F' V' C' R' WFH H H0 H1 H4 H5 H6.
    unfold recursive_mlc_allocation in H.
    fold recursive_mlc_allocation in H.
    destruct n. discriminate.
    case_eq (NatMap.find a k). intros s H2.
    assert (A0 := H2). destruct (NatMap.find a k) in A0, H.
    case_eq (cachelet_allocation n r s0). intros s3 H3.
    assert (A1 := H3). destruct (cachelet_allocation n r s0) in A1, H.
    injection A0; injection A1; intros X0 X1; subst s0 s3; clear A0 A1.
    assert (WFH1 := WFH).
    unfold well_defined_cache_tree in WFH1.
    destruct WFH1 as [ WFH1 WFH2 ]. destruct WFH2 as [ WFH2 WFH3 ]. destruct WFH3 as [ WFH3 WFH4 ].
    case_eq (eqb index a).
    {
      intros H7; apply cmp_to_eq in H7; subst a.
      rewrite -> H2 in H0.
      injection H0; intros X0; subst s.
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
        apply (wf8_1_cachelet_allocation n r F V C R c v w s).
        subst psi; exact H3. exact H6.
      }
      {
        destruct lambda.
        rewrite -> WFH1 in IHTREE. discriminate.
        specialize (WFH3 c0 index (p :: l) IHTREE).
        unfold get_cache_ID_path in IHTREE. discriminate.
        specialize (WFH2 p0 index (p :: l) IHTREE).
        injection WFH2; intros X0; subst p0.
        apply (WFH4 index p l) in IHTREE.
        apply (IHl (cache_node p) IHTREE  n0 r (NatMap.add index (single_level_cache c v w s) k)
        k' index (single_level_cache c v w s) psi' c v w s F' V' C' R').
        exact WFH.
        exact H.
        apply NatMapFacts.add_eq_o. reflexivity.
        exact H1.
        reflexivity.
        exact H5.
        apply (wf8_1_cachelet_allocation n r F V C R c v w s).
        subst psi; exact H3. exact H6.
      }
    }
    {
      intros H7; apply cmp_to_uneq in H7.
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
        injection WFH2; intros X0; subst p0.
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
    intros; destruct (cachelet_allocation n r s0); discriminate.
    discriminate.
    intros; destruct (NatMap.find a k); discriminate.
  }
  intros; destruct (get_cache_ID_path lambda h_tree); discriminate.
Qed.

(* WF8 MLC Write *)
Lemma cc_hit_write_r_range : forall psi e' l v D c0 psi' F V C R F' V' C' R',
  cc_hit_write psi e' l v = cc_hit_write_valid D c0 psi' ->
  psi = single_level_cache F V C R ->
  psi' = single_level_cache F' V' C' R' ->
  forall x, ((exists y T, way_ID_in x T /\ NatMap.find y R = Some T) <->
  (exists y T, way_ID_in x T /\ NatMap.find y R' = Some T)).
Proof.
  intros.
  split.
  {
    intros.
    subst psi psi'.
    unfold cc_hit_write in H.
    case_eq (cc_unfold (single_level_cache F V C R) e' l). intros.
    assert (A0 := H0). destruct (cc_unfold (single_level_cache F V C R) e' l) in A0, H.
    injection A0; intros; subst; clear A0.
    assert (H1 := H0).
    apply cc_unfold_psi in H0.
    injection H0; intros; subst c v0 w s.
    destruct c1.
    destruct w0.
    case_eq (NatMap.find s R); intros.
    assert (A0 := H3); destruct (NatMap.find s R) in A0, H.
    injection A0; intros; subst; clear A0.
    destruct v.
    discriminate.
    destruct e'.
    injection H; intros; subst.
    destruct H2 as (y & T & H2 & H4).
    case_eq (eqb s y); intros.
    apply cmp_to_eq in H5; subst.
    rewrite -> H3 in H4. injection H4; intros; subst.
    eexists y; eexists (update T w e). split.
    apply way_ID_in_update. exact H2.
    apply NatMapFacts.add_eq_o; reflexivity.
    apply cmp_to_uneq in H5.
    eexists y; eexists T. split. exact H2.
    rewrite <- H4. apply NatMapFacts.add_neq_o; exact H5.
    discriminate.
    destruct (NatMap.find s R); discriminate.
    discriminate.
    intros; destruct (cc_unfold (single_level_cache F V C R) e' l); discriminate.
  }
  {
    intros.
    subst psi psi'.
    unfold cc_hit_write in H.
    case_eq (cc_unfold (single_level_cache F V C R) e' l). intros.
    assert (A0 := H0). destruct (cc_unfold (single_level_cache F V C R) e' l) in A0, H.
    injection A0; intros; subst; clear A0.
    assert (H1 := H0).
    apply cc_unfold_psi in H0.
    injection H0; intros; subst c v0 w s.
    destruct c1.
    destruct w0.
    case_eq (NatMap.find s R); intros.
    assert (A0 := H3); destruct (NatMap.find s R) in A0, H.
    injection A0; intros; subst; clear A0.
    destruct v.
    discriminate.
    destruct e'.
    injection H; intros; subst.
    destruct H2 as (y & T & H2 & H4).
    case_eq (eqb s y); intros.
    apply cmp_to_eq in H5; subst.
    assert (Some T = Some (update p w e)).
    rewrite <- H4. apply NatMapFacts.add_eq_o; reflexivity.
    injection H5; intros; subst.
    eexists y; eexists p. split. apply way_ID_in_update in H2.
    exact H2. exact H3.
    apply cmp_to_uneq in H5.
    eexists y; eexists T. split. exact H2.
    rewrite <- H4. apply eq_sym. apply NatMapFacts.add_neq_o; exact H5.
    discriminate.
    destruct (NatMap.find s R); discriminate.
    discriminate.
    intros; destruct (cc_unfold (single_level_cache F V C R) e' l); discriminate.
  }
Qed.

Lemma wf8_1_mlc_write : forall lambda h_tree k e' m0 l0 v D obs1 mu k' index psi psi'
  F V C R F' V' C' R',
  well_defined_cache_tree h_tree ->
  mlc_write k e' m0 l0 v lambda h_tree = mlc_write_valid D obs1 mu k' ->
  NatMap.find index k = Some psi ->
  NatMap.find index k' = Some psi' ->
  psi = single_level_cache F V C R ->
  psi' = single_level_cache F' V' C' R' ->
  (forall w s, CacheletMap.In (w, s) C -> exists y T, way_ID_in w T
  /\ NatMap.find y R = Some T) ->
  (forall w s, CacheletMap.In (w, s) C' -> exists y T, way_ID_in w T
  /\ NatMap.find y R' = Some T).
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
    exact (H6 w s H5).
    discriminate.
    discriminate.
  }
  {
    intros lambda IHTREE k e' m0 l0 v D obs1 mu k' index psi psi'
    F V C R F' V' C' R' WFH1 H H0 H1 H2 H3 H6.
    unfold recursive_mlc_write in H.
    fold recursive_mlc_write in H.
    case_eq (NatMap.find a k). intros s H4.
    assert (A0 := H4). destruct (NatMap.find a k) in A0, H.
    case_eq (cc_hit_write s0 e' l0 v). intros d c s1 H5.
    assert (A1 := H5). destruct (cc_hit_write s0 e' l0 v) in A1, H. destruct l0.
    injection H; injection A0; injection A1;
    intros X0 X1 X2 X3 X4 X5 X6 X7; subst; clear A0 A1.
    destruct s; destruct s1.
    assert (forall x, CacheletMap.In x w <-> CacheletMap.In x w0). intros.
    apply (cc_hit_write_c (single_level_cache c0 v0 w s) e' (address b d1) v D c
    (single_level_cache c1 v1 w0 s0) c0 v0 w s c1 v1 w0 s0 x H5).
    reflexivity. reflexivity.
    assert (forall x, ((exists y T, way_ID_in x T /\ NatMap.find y s = Some T) <->
    (exists y T, way_ID_in x T /\ NatMap.find y s0 = Some T))).
    apply (cc_hit_write_r_range (single_level_cache c0 v0 w s) e' (address b d1) v D c
    (single_level_cache c1 v1 w0 s0) c0 v0 w s c1 v1 w0 s0 H5).
    reflexivity. reflexivity.
    {
      case_eq (eqb a index).
      {
        intros H7; apply cmp_to_eq in H7. subst.
        rewrite -> H0 in H4.
        injection H4; intros; subst c0 v0 w s.
        assert (NatMap.find index (NatMap.add index (single_level_cache c1 v1 w0 s0) k) =
        Some (single_level_cache c1 v1 w0 s0)).
        apply NatMapFacts.add_eq_o. reflexivity.
        rewrite -> H7 in H1.
        injection H1; intros; subst c1 v1 w0 s0.
        apply H3. apply (H6 w1 s1). apply H2. exact H11.
      }
      {
        intros. apply cmp_to_uneq in H7.
        assert (NatMap.find index (NatMap.add a (single_level_cache c1 v1 w0 s0) k) = NatMap.find index k).
        apply NatMapFacts.add_neq_o. exact H7.
        rewrite -> H1 in H9.
        rewrite -> H0 in H9.
        injection H9; intros; subst F' V' C' R'.
        exact (H6 w1 s1 H8).
      }
    }
    discriminate.
    intros H5. destruct (cc_hit_write s0 e' l0).
    discriminate.
    case_eq (recursive_mlc_write k e' m0 l0 v l). intros d o m m1 H7.
    assert (A1 := H7). destruct (recursive_mlc_write k e' m0 l0 v l) in A1, H.
    case_eq (cc_update s0 e' d0 l0). intros c s1 H8.
    assert (A2 := H8). destruct (cc_update s0 e' d0 l0) in A2, H.
    injection H; injection A0; injection A1; injection A2;
    intros X0 X1 X2 X3 X4 X5 X6 X7 X8 X9 X10; subst; clear A0 A1 A2.
    {
      case_eq (eqb index a).
      {
        intros H2. apply cmp_to_eq in H2. subst a.
        destruct s. destruct s1.
        assert (forall c, CacheletMap.In c w <-> CacheletMap.In c w0). intros.
        apply (cc_update_c (single_level_cache c0 v0 w s) e' D l0 c (single_level_cache c1 v1 w0 s0)
        c0 v0 w s c1 v1 w0 s0 c2 H8). reflexivity. reflexivity.
        assert (forall x, ((exists y T, way_ID_in x T /\ NatMap.find y s = Some T) <->
        (exists y T, way_ID_in x T /\ NatMap.find y s0 = Some T))).
        apply (cc_update_r_range (single_level_cache c0 v0 w s) e' D l0 c (single_level_cache c1 v1 w0 s0)
        c0 v0 w s c1 v1 w0 s0 H8). reflexivity. reflexivity.
        assert (NatMap.find index (NatMap.add index (single_level_cache c1 v1 w0 s0) m1) =
        Some (single_level_cache c1 v1 w0 s0)).
        apply NatMapFacts.add_eq_o. reflexivity.
        rewrite -> H9 in H1.
        rewrite -> H4 in H0.
        injection H0; injection H1; intros; subst.
        apply H3. apply (H6 w1 s1). apply H2. exact H18.
      }
      {
        intros H2. apply cmp_to_uneq in H2.
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
          injection WFH2; intros X0; subst.
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

(* WF8-1 MLC Deallocation *)
Lemma wf8_1_clear_remapping_list : forall r l F V C R F' V' C' R',
  clear_remapping_list r l F V C R = Some (single_level_cache F' V' C' R') ->
  NatMap.find r V = Some l ->
  (forall w s, CacheletMap.In (w, s) C -> exists y T, way_ID_in w T
  /\ NatMap.find y R = Some T) ->
  (forall w s, CacheletMap.In (w, s) C' -> exists y T, way_ID_in w T
  /\ NatMap.find y R' = Some T).
Proof.
  intros r l.
  induction l.
  {
    intros F V C R F' V' C' R' H H0.
    unfold clear_remapping_list in H.
    injection H; intros; subst.
    exact (H5 w s H6).
  }
  {
    intros F V C R F' V' C' R' H H0 B.
    unfold clear_remapping_list in H.
    fold clear_remapping_list in H.
    destruct a.
    case_eq (NatMap.find s R). intros p H4.
    assert (A0 := H4). destruct (NatMap.find s R) in A0, H.
    case_eq (cachelet_invalidation C (w, s)). intros w1 H5.
    assert (A1 := H5). destruct (cachelet_invalidation C (w, s)) in A1, H.
    injection A0; injection A1; intros X Y; subst w1 p; clear A0 A1.
    {
      apply (IHl ((w, s) :: F) (NatMap.add r l V) w0 (NatMap.add s (update p0 w
      (enclave_ID_active r)) R) F' V' C' R' H).
      apply NatMapFacts.add_eq_o; reflexivity. intros.
      apply (cachelet_invalidation_c (w1, s0) (w, s) C w0 H5) in H1.
      apply B in H1. destruct H1 as (y & T & H1 & H2).
      case_eq (eqb s y); intros.
      apply cmp_to_eq in H3; subst.
      rewrite -> H4 in H2. injection H2; intros; subst.
      eexists y; eexists (update T w (enclave_ID_active r)). split.
      apply way_ID_in_update. exact H1.
      apply NatMapFacts.add_eq_o; reflexivity.
      apply cmp_to_uneq in H3.
      eexists y; eexists T. split. exact H1.
      rewrite <- H2. apply NatMapFacts.add_neq_o; exact H3.
    }
    discriminate.
    intros; destruct (cachelet_invalidation C (w, s)); discriminate.
    discriminate.
    intros; destruct (NatMap.find s R); discriminate.
  }
Qed.

Lemma wf8_1_mlc_dealloc : forall lambda h_tree state k k' index psi psi' F V C R F' V' C' R',
  well_defined_cache_tree h_tree ->
  mlc_deallocation state k lambda h_tree = Some k' ->
  NatMap.find index k = Some psi ->
  NatMap.find index k' = Some psi' ->
  psi = single_level_cache F V C R ->
  psi' = single_level_cache F' V' C' R' ->
  (forall w s, CacheletMap.In (w, s) C -> exists y T, way_ID_in w T
  /\ NatMap.find y R = Some T) ->
  (forall w s, CacheletMap.In (w, s) C' -> exists y T, way_ID_in w T
  /\ NatMap.find y R' = Some T).
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
    exact (H6 w s H5).
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
    injection A0; injection A1; intros X0 X1; subst s0 s2; clear A0 A1.
    assert (WFH1 := WFH).
    unfold well_defined_cache_tree in WFH1.
    destruct WFH1 as [ WFH1 WFH2 ]. destruct WFH2 as [ WFH2 WFH3 ]. destruct WFH3 as [ WFH3 WFH4 ].
    case_eq (eqb index a).
    {
      intros H9; apply cmp_to_eq in H9; subst a.
      rewrite -> H7 in H0.
      injection H0; intros X0; subst s.
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
        apply (wf8_1_clear_remapping_list r r0 F V C R c v w s).
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
        injection WFH2; intros X0; subst p0.
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
        apply (wf8_1_clear_remapping_list r r0 F V C R c v w s).
        exact H8. exact H10. exact H6.
        discriminate.
        intros; destruct (NatMap.find r v0).
        discriminate.
        discriminate.
      }
    }
    {
      intros H4; apply cmp_to_uneq in H4.
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
        injection WFH2; intros X0; subst p0.
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

(* WF8-1 Preservation *)
Lemma wf8_1_preservation : forall sigma obs sigma' obs',
  wf8_1 sigma -> <<sigma; obs>> ===> <<sigma'; obs'>> -> wf8_1 sigma'.
Proof.
  destruct sigma; destruct sigma'.
  unfold wf8_1 in *.
  intros obs' H H0 k mu rho pi lambda F V C R H1 H2; injection H1;
  intros X0 X1 X2 X3; subst.
  inversion H0. inversion H14; subst.
  - case_eq (NatMap.find lambda m). intros s0 H4; subst.
    destruct s0.
    apply (wf8_1_mlc_read lambda0 h_tree m e' mu l0 D delta obs0 k lambda (single_level_cache c v w s)
    (single_level_cache F V C R) c v w s F V C R).
    exact H22. exact H33. exact H4. exact H2.
    reflexivity. reflexivity.
    apply (H m mu rho p lambda c v w s).
    reflexivity. exact H4.
    intros H4. apply (wf_mlc_read_none lambda0 h_tree m e' mu l0 D delta obs0 k lambda) in H4.
    rewrite -> H2 in H4.
    discriminate. exact H22. exact H33.
  - case_eq (NatMap.find lambda m). intros s0 H4; subst.
    destruct s0.
    apply (wf8_1_mlc_alloc lambda0 h_tree r_bar_val n m k lambda (single_level_cache c v w s)
    (single_level_cache F V C R) c v w s F V C R).
    exact H29. exact H39. exact H4. exact H2.
    reflexivity. reflexivity.
    apply (H m mu rho p lambda c v w s).
    reflexivity. exact H4.
    intros H4. apply (wf_mlc_alloc_none lambda0 h_tree r_bar_val n m k lambda) in H39.
    rewrite -> H39 in H2.
    discriminate. exact H29. exact H4.
  - case_eq (NatMap.find lambda m). intros s0 H4; subst.
    destruct s0.
    apply (wf8_1_mlc_write lambda0 h_tree m e' m0 l0 v D obs1 mu k lambda (single_level_cache c v0 w s)
    (single_level_cache F V C R) c v0 w s F V C R).
    exact H22. exact H33. exact H4. exact H2.
    reflexivity. reflexivity.
    apply (H m m0 rho p lambda c v0 w s).
    reflexivity. exact H4.
    intros H4. apply (wf_mlc_write_none lambda0 h_tree m e' m0 l0 v D obs1 mu k lambda) in H4.
    rewrite -> H2 in H4.
    discriminate. exact H22. exact H33.
  - case_eq (NatMap.find lambda m). intros s0 H4; subst.
    destruct s0.
    apply (wf8_1_mlc_dealloc lambda0 h_tree r_val m k lambda (single_level_cache c v w s)
    (single_level_cache F V C R) c v w s F V C R).
    exact H26. exact H34. exact H4. exact H2. reflexivity. reflexivity.
    apply (H m m0 rho p lambda c v w s).
    reflexivity. exact H4.
    intros H4. apply (wf_mlc_dealloc_none lambda0 h_tree r_val m k lambda) in H34.
    rewrite -> H34 in H2.
    discriminate. exact H26. exact H4.
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

(* Well-Formed 8-2 *)
Definition wf8_2 (sigma: runtime_state): Prop :=
  forall k mu rho pi lambda F V C R,
  sigma = runtime_state_value k mu rho pi ->
  (NatMap.find lambda k = Some (single_level_cache F V C R)) ->
  (forall w, (exists y T, way_ID_in w T /\ NatMap.find y R = Some T) ->
  (exists s, CacheletMap.In (w, s) C)).

(* WF8-2 MLC Read *)
Lemma wf8_2_mlc_read : forall lambda h_tree k e' m0 l0 D obs1 mu k' index psi psi'
  F V C R F' V' C' R',
  well_defined_cache_tree h_tree ->
  mlc_read k e' m0 l0 lambda h_tree = mlc_read_valid D obs1 mu k' ->
  NatMap.find index k = Some psi ->
  NatMap.find index k' = Some psi' ->
  psi = single_level_cache F V C R ->
  psi' = single_level_cache F' V' C' R' ->
  (forall w, (exists y T, way_ID_in w T /\ NatMap.find y R = Some T) ->
  (exists s, CacheletMap.In (w, s) C)) ->
  (forall w, (exists y T, way_ID_in w T /\ NatMap.find y R' = Some T) ->
  (exists s, CacheletMap.In (w, s) C')).
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
    apply (H8 w H9). discriminate.
  }
  {
    intros lambda IHTREE k e' m0 l0 D obs1 mu k' index psi psi' F V C R
    F' V' C' R' H H0 H1 H2 H3 H4 H7.
    unfold recursive_mlc_read in H0.
    fold recursive_mlc_read in H0.
    case_eq (NatMap.find a k). intros s H5.
    assert (A0 := H5). destruct (NatMap.find a k) in A0, H0.
    case_eq (cc_hit_read s0 e' l0). intros d d0 c s1 H6.
    assert (A1 := H6). destruct (cc_hit_read s0 e' l0) in A1, H0.
    injection H0; injection A0; injection A1; intros; subst; clear A0 A1.
    assert (H8 := H6).
    destruct s; destruct s1.
    apply (cc_hit_read_c (single_level_cache c0 v w0 s) e' l0 D obs1 c
    (single_level_cache c1 v0 w1 s0) c0 v w0 s c1 v0 w1 s0) in H6.
    destruct e'.
    assert (forall x, ((exists y T, way_ID_in x T /\ NatMap.find y s = Some T) <->
    (exists y T, way_ID_in x T /\ NatMap.find y s0 = Some T))).
    apply (cc_hit_read_r_range (single_level_cache c0 v w0 s) e e0 l0 D obs1 c
    (single_level_cache c1 v0 w1 s0) c0 v w0 s c1 v0 w1 s0 H8).
    reflexivity. reflexivity.
    {
      case_eq (eqb a index).
      {
        intros. apply cmp_to_eq in H4. subst.
        rewrite -> H1 in H5.
        injection H5; intros; subst c0 v w1 s.
        assert (NatMap.find index (NatMap.add index (single_level_cache c1 v0 C s0) k) =
        Some (single_level_cache c1 v0 C s0)).
        apply NatMapFacts.add_eq_o. reflexivity.
        rewrite -> H2 in H4; injection H4; intros; subst.
        apply (H7 w). apply H3. exact H17.
      }
      {
        intros. apply cmp_to_uneq in H4.
        assert (NatMap.find index (NatMap.add a (single_level_cache c1 v0 w1 s0) k) = NatMap.find index k).
        apply NatMapFacts.add_neq_o. exact H4.
        rewrite -> H2 in H9.
        rewrite -> H1 in H9.
        injection H9; intros; subst F' V' C' R'.
        apply (H7 w). exact H17.
      }
    }
    reflexivity.
    reflexivity.
    discriminate.
    intros H6. destruct (cc_hit_read s0 e' l0).
    discriminate.
    case_eq (recursive_mlc_read k e' m0 l0 l). intros d d0 o m H8.
    assert (A1 := H8). destruct (recursive_mlc_read k e' m0 l0 l) in A1, H0.
    case_eq (cc_update s0 e' d1 l0). intros c s1 H9.
    assert (A2 := H9). destruct (cc_update s0 e' d1 l0) in A2, H0.
    injection H0; injection A0; injection A1; injection A2;
    intros X0 X1 X2 X3 X4 X5 X6 X7 X8 X9 X10; subst; clear A0 A1 A2.
    {
      case_eq (eqb index a).
      {
        intros. apply cmp_to_eq in H3. subst a.
        destruct s. destruct s1.
        assert (forall c, CacheletMap.In c w0 <-> CacheletMap.In c w1); intros.
        apply (cc_update_c (single_level_cache c0 v w0 s) e' D l0 c (single_level_cache c1 v0 w1 s0)
        c0 v w0 s c1 v0 w1 s0 c2 H9). reflexivity. reflexivity.
        assert (forall x, ((exists y T, way_ID_in x T /\ NatMap.find y s = Some T) <->
        (exists y T, way_ID_in x T /\ NatMap.find y s0 = Some T))).
        apply (cc_update_r_range (single_level_cache c0 v w0 s) e' D l0 c (single_level_cache c1 v0 w1 s0)
        c0 v w0 s c1 v0 w1 s0 H9). reflexivity. reflexivity.
        assert (NatMap.find index (NatMap.add index (single_level_cache c1 v0 w1 s0) m) =
        Some (single_level_cache c1 v0 w1 s0)).
        apply NatMapFacts.add_eq_o. reflexivity.
        rewrite -> H11 in H2.
        rewrite -> H5 in H1.
        injection H1; injection H2; intros; subst.
        assert (forall w', (exists s', CacheletMap.In (w', s') C) <->
        (exists s', CacheletMap.In (w', s') C')).
        split; intros; destruct H12 as (s' & H12);
        eexists s'; apply H3; exact H12.
        apply H12. apply H7. apply H10. exact H4.
      }
      {
        intros H3. apply cmp_to_uneq in H3.
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
          injection WFH2; intros X0; subst.
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
    intros; destruct (cc_update s0 e' d1 l0); discriminate.
    discriminate.
    intros; destruct (recursive_mlc_read k e' m0 l0 l); discriminate.
    discriminate.
    intros; destruct (NatMap.find a k); discriminate.
  }
  intros; destruct (get_cache_ID_path lambda h_tree); discriminate.
Qed.

(* WF8-2 MLC Allocation *)
Lemma wf8_2_cachelet_allocation : forall n r F V C R F' V' C' R',
  cachelet_allocation n r (single_level_cache F V C R) = Some (single_level_cache F' V' C' R') ->
  (forall w, (exists y T, way_ID_in w T /\ NatMap.find y R = Some T) ->
  (exists s, CacheletMap.In (w, s) C)) ->
  (forall w, (exists y T, way_ID_in w T /\ NatMap.find y R' = Some T) ->
  (exists s, CacheletMap.In (w, s) C')).
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
    apply (H0 w H1).
  }
  {
    intros F V C R F' V' C' R' H H0.
    unfold recursive_cachelet_allocation in H.
    fold recursive_cachelet_allocation in H.
    case_eq (way_first_allocation F). intros c H1.
    assert (A0 := H1); destruct (way_first_allocation F) in H, A0.
    destruct c0.
    case_eq (NatMap.find s R). intros p H2.
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
      exact H. intros.
      destruct H3 as (y & T & H3 & H4). apply H0.
      case_eq (eqb s y); intros.
      apply cmp_to_eq in H6; subst.
      assert (Some T = Some (update p w (enclave_ID_active r))).
      rewrite <- H4. apply NatMapFacts.add_eq_o; reflexivity.
      injection H6; intros; subst.
      eexists y; eexists p. split.
      apply way_ID_in_update in H3. exact H3. exact H2.
      apply cmp_to_uneq in H6.
      assert (NatMap.find y R = Some T). rewrite <- H4.
      apply eq_sym. apply NatMapFacts.add_neq_o; exact H6.
      eexists y; eexists T. split. exact H3. exact H7.
    }
    discriminate.
    intros H5; assert (A2 := H5); destruct (NatMap.find r V) in A2, H.
    discriminate.
    injection A0; injection A1; injection A3; intros X0 X1 X2; subst; clear A0 A1 A2 A3.
    {
      apply (IHn0 c0 (NatMap.add r ((w, s) :: nil) V) C
      (NatMap.add s (update p w (enclave_ID_active r)) R) F' V' C' R').
      exact H. intros.
      destruct H3 as (y & T & H3 & H4). apply H0.
      case_eq (eqb s y); intros.
      apply cmp_to_eq in H6; subst.
      assert (Some T = Some (update p w (enclave_ID_active r))).
      rewrite <- H4. apply NatMapFacts.add_eq_o; reflexivity.
      injection H6; intros; subst.
      eexists y; eexists p. split.
      apply way_ID_in_update in H3. exact H3. exact H2.
      apply cmp_to_uneq in H6.
      assert (NatMap.find y R = Some T). rewrite <- H4.
      apply eq_sym. apply NatMapFacts.add_neq_o; exact H6.
      eexists y; eexists T. split. exact H3. exact H7.
    }
    discriminate.
    intros; destruct (remove_CAT (w, s) F); discriminate.
    discriminate.
    intros; destruct (NatMap.find s R); discriminate.
    discriminate.
    intros; destruct (way_first_allocation F); discriminate.
  }
Qed.

Lemma wf8_2_mlc_alloc : forall lambda h_tree n state k k' index psi psi' F V C R F' V' C' R',
  well_defined_cache_tree h_tree ->
  mlc_allocation n state k lambda h_tree = Some k' ->
  NatMap.find index k = Some psi ->
  NatMap.find index k' = Some psi' ->
  psi = single_level_cache F V C R ->
  psi' = single_level_cache F' V' C' R' ->
  (forall w, (exists y T, way_ID_in w T /\ NatMap.find y R = Some T) ->
  (exists s, CacheletMap.In (w, s) C)) ->
  (forall w, (exists y T, way_ID_in w T /\ NatMap.find y R' = Some T) ->
  (exists s, CacheletMap.In (w, s) C')).
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
    exact (H6 w H3).
  }
  {
    intros lambda IHTREE n r k k' index psi psi' F V C R
    F' V' C' R' WFH H H0 H1 H4 H5 H6.
    unfold recursive_mlc_allocation in H.
    fold recursive_mlc_allocation in H.
    destruct n. discriminate.
    case_eq (NatMap.find a k). intros s H2.
    assert (A0 := H2). destruct (NatMap.find a k) in A0, H.
    case_eq (cachelet_allocation n r s0). intros s3 H3.
    assert (A1 := H3). destruct (cachelet_allocation n r s0) in A1, H.
    injection A0; injection A1; intros X0 X1; subst s0 s3; clear A0 A1.
    assert (WFH1 := WFH).
    unfold well_defined_cache_tree in WFH1.
    destruct WFH1 as [ WFH1 WFH2 ]. destruct WFH2 as [ WFH2 WFH3 ]. destruct WFH3 as [ WFH3 WFH4 ].
    case_eq (eqb index a).
    {
      intros H7; apply cmp_to_eq in H7; subst a.
      rewrite -> H2 in H0.
      injection H0; intros X0; subst s.
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
        apply (wf8_2_cachelet_allocation n r F V C R c v w s).
        subst psi; exact H3. exact H6.
      }
      {
        destruct lambda.
        rewrite -> WFH1 in IHTREE. discriminate.
        specialize (WFH3 c0 index (p :: l) IHTREE).
        unfold get_cache_ID_path in IHTREE. discriminate.
        specialize (WFH2 p0 index (p :: l) IHTREE).
        injection WFH2; intros X0; subst p0.
        apply (WFH4 index p l) in IHTREE.
        apply (IHl (cache_node p) IHTREE  n0 r (NatMap.add index (single_level_cache c v w s) k)
        k' index (single_level_cache c v w s) psi' c v w s F' V' C' R').
        exact WFH.
        exact H.
        apply NatMapFacts.add_eq_o. reflexivity.
        exact H1.
        reflexivity.
        exact H5.
        apply (wf8_2_cachelet_allocation n r F V C R c v w s).
        subst psi; exact H3. exact H6.
      }
    }
    {
      intros H7; apply cmp_to_uneq in H7.
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
        injection WFH2; intros X0; subst p0.
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
    intros; destruct (cachelet_allocation n r s0); discriminate.
    discriminate.
    intros; destruct (NatMap.find a k); discriminate.
  }
  intros; destruct (get_cache_ID_path lambda h_tree); discriminate.
Qed.

(* WF8-2 MLC Write *)
Lemma wf8_2_mlc_write : forall lambda h_tree k e' m0 l0 v D obs1 mu k' index psi psi'
  F V C R F' V' C' R',
  well_defined_cache_tree h_tree ->
  mlc_write k e' m0 l0 v lambda h_tree = mlc_write_valid D obs1 mu k' ->
  NatMap.find index k = Some psi ->
  NatMap.find index k' = Some psi' ->
  psi = single_level_cache F V C R ->
  psi' = single_level_cache F' V' C' R' ->
  (forall w, (exists y T, way_ID_in w T /\ NatMap.find y R = Some T) ->
  (exists s, CacheletMap.In (w, s) C)) ->
  (forall w, (exists y T, way_ID_in w T /\ NatMap.find y R' = Some T) ->
  (exists s, CacheletMap.In (w, s) C')).
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
    exact (H6 w H5).
    discriminate.
    discriminate.
  }
  {
    intros lambda IHTREE k e' m0 l0 v D obs1 mu k' index psi psi'
    F V C R F' V' C' R' WFH1 H H0 H1 H2 H3 H6.
    unfold recursive_mlc_write in H.
    fold recursive_mlc_write in H.
    case_eq (NatMap.find a k). intros s H4.
    assert (A0 := H4). destruct (NatMap.find a k) in A0, H.
    case_eq (cc_hit_write s0 e' l0 v). intros d c s1 H5.
    assert (A1 := H5). destruct (cc_hit_write s0 e' l0 v) in A1, H. destruct l0.
    injection H; injection A0; injection A1;
    intros X0 X1 X2 X3 X4 X5 X6 X7; subst; clear A0 A1.
    destruct s; destruct s1.
    assert (forall x, CacheletMap.In x w <-> CacheletMap.In x w0). intros.
    apply (cc_hit_write_c (single_level_cache c0 v0 w s) e' (address b d1) v D c
    (single_level_cache c1 v1 w0 s0) c0 v0 w s c1 v1 w0 s0 x H5).
    reflexivity. reflexivity.
    assert (forall x, ((exists y T, way_ID_in x T /\ NatMap.find y s = Some T) <->
    (exists y T, way_ID_in x T /\ NatMap.find y s0 = Some T))).
    apply (cc_hit_write_r_range (single_level_cache c0 v0 w s) e' (address b d1) v D c
    (single_level_cache c1 v1 w0 s0) c0 v0 w s c1 v1 w0 s0 H5).
    reflexivity. reflexivity.
    {
      case_eq (eqb a index).
      {
        intros H7; apply cmp_to_eq in H7. subst.
        rewrite -> H0 in H4.
        injection H4; intros; subst c0 v0 w s.
        assert (NatMap.find index (NatMap.add index (single_level_cache c1 v1 w0 s0) k) =
        Some (single_level_cache c1 v1 w0 s0)).
        apply NatMapFacts.add_eq_o. reflexivity.
        rewrite -> H7 in H1.
        injection H1; intros; subst c1 v1 w0 s0.
        assert (forall w', (exists s', CacheletMap.In (w', s') C) <->
        (exists s', CacheletMap.In (w', s') C')).
        split; intros; destruct H8 as (s' & H8);
        eexists s'; apply H2; exact H8.
        apply H8. apply H6. apply H3. exact H11.
      }
      {
        intros. apply cmp_to_uneq in H7.
        assert (NatMap.find index (NatMap.add a (single_level_cache c1 v1 w0 s0) k) = NatMap.find index k).
        apply NatMapFacts.add_neq_o. exact H7.
        rewrite -> H1 in H9.
        rewrite -> H0 in H9.
        injection H9; intros; subst F' V' C' R'.
        exact (H6 w1 H8).
      }
    }
    discriminate.
    intros H5. destruct (cc_hit_write s0 e' l0).
    discriminate.
    case_eq (recursive_mlc_write k e' m0 l0 v l). intros d o m m1 H7.
    assert (A1 := H7). destruct (recursive_mlc_write k e' m0 l0 v l) in A1, H.
    case_eq (cc_update s0 e' d0 l0). intros c s1 H8.
    assert (A2 := H8). destruct (cc_update s0 e' d0 l0) in A2, H.
    injection H; injection A0; injection A1; injection A2;
    intros X0 X1 X2 X3 X4 X5 X6 X7 X8 X9 X10; subst; clear A0 A1 A2.
    {
      case_eq (eqb index a).
      {
        intros H2. apply cmp_to_eq in H2. subst a.
        destruct s. destruct s1.
        assert (forall c, CacheletMap.In c w <-> CacheletMap.In c w0). intros.
        apply (cc_update_c (single_level_cache c0 v0 w s) e' D l0 c (single_level_cache c1 v1 w0 s0)
        c0 v0 w s c1 v1 w0 s0 c2 H8). reflexivity. reflexivity.
        assert (forall x, ((exists y T, way_ID_in x T /\ NatMap.find y s = Some T) <->
        (exists y T, way_ID_in x T /\ NatMap.find y s0 = Some T))).
        apply (cc_update_r_range (single_level_cache c0 v0 w s) e' D l0 c (single_level_cache c1 v1 w0 s0)
        c0 v0 w s c1 v1 w0 s0 H8). reflexivity. reflexivity.
        assert (NatMap.find index (NatMap.add index (single_level_cache c1 v1 w0 s0) m1) =
        Some (single_level_cache c1 v1 w0 s0)).
        apply NatMapFacts.add_eq_o. reflexivity.
        rewrite -> H9 in H1.
        rewrite -> H4 in H0.
        injection H0; injection H1; intros; subst.
        assert (forall w', (exists s', CacheletMap.In (w', s') C) <->
        (exists s', CacheletMap.In (w', s') C')).
        split; intros; destruct H10 as (s' & H10);
        eexists s'; apply H2; exact H10.
        apply H10. apply H6. apply H3. exact H18.
      }
      {
        intros H2. apply cmp_to_uneq in H2.
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
          injection WFH2; intros X0; subst.
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

(* WF8-2 MLC Deallocation *)
Lemma wf8_2_clear_remapping_list : forall r l F V C R F' V' C' R',
  clear_remapping_list r l F V C R = Some (single_level_cache F' V' C' R') ->
  NatMap.find r V = Some l ->
  (forall w, (exists y T, way_ID_in w T /\ NatMap.find y R = Some T) ->
  (exists s, CacheletMap.In (w, s) C)) ->
  (forall w, (exists y T, way_ID_in w T /\ NatMap.find y R' = Some T) ->
  (exists s, CacheletMap.In (w, s) C')).
Proof.
  intros r l.
  induction l.
  {
    intros F V C R F' V' C' R' H H0.
    unfold clear_remapping_list in H.
    injection H; intros; subst.
    exact (H5 w H6).
  }
  {
    intros F V C R F' V' C' R' H H0 B.
    unfold clear_remapping_list in H.
    fold clear_remapping_list in H.
    destruct a.
    case_eq (NatMap.find s R). intros p H4.
    assert (A0 := H4). destruct (NatMap.find s R) in A0, H.
    case_eq (cachelet_invalidation C (w, s)). intros w1 H5.
    assert (A1 := H5). destruct (cachelet_invalidation C (w, s)) in A1, H.
    injection A0; injection A1; intros X Y; subst w1 p; clear A0 A1.
    {
      apply (IHl ((w, s) :: F) (NatMap.add r l V) w0 (NatMap.add s (update p0 w
      (enclave_ID_active r)) R) F' V' C' R' H).
      apply NatMapFacts.add_eq_o; reflexivity. intros.
      assert (forall w' s', CacheletMap.In (w', s') C <-> CacheletMap.In (w', s') w0).
      intros. apply (cachelet_invalidation_c (w', s') (w, s) C w0 H5).
      assert (forall w', (exists s', CacheletMap.In (w', s') C) <->
      (exists s', CacheletMap.In (w', s') w0)).
      split; intros; destruct H3 as (s' & H3);
      eexists s'; apply H2; exact H3. apply H3.
      apply B. destruct H1 as (y & T & H1 & H6).
      case_eq (eqb s y); intros.
      apply cmp_to_eq in H7; subst.
      assert (Some T = Some (update p0 w (enclave_ID_active r))).
      rewrite <- H6. apply NatMapFacts.add_eq_o; reflexivity.
      injection H7; intros; subst.
      eexists y; eexists p0. split.
      apply way_ID_in_update in H1. exact H1. exact H4.
      apply cmp_to_uneq in H7.
      assert (NatMap.find y R = Some T).
      rewrite <- H6. apply eq_sym.
      apply NatMapFacts.add_neq_o; exact H7.
      eexists y; eexists T.
      split. exact H1. exact H8.
    }
    discriminate.
    intros; destruct (cachelet_invalidation C (w, s)); discriminate.
    discriminate.
    intros; destruct (NatMap.find s R); discriminate.
  }
Qed.

Lemma wf8_2_mlc_dealloc : forall lambda h_tree state k k' index psi psi' F V C R F' V' C' R',
  well_defined_cache_tree h_tree ->
  mlc_deallocation state k lambda h_tree = Some k' ->
  NatMap.find index k = Some psi ->
  NatMap.find index k' = Some psi' ->
  psi = single_level_cache F V C R ->
  psi' = single_level_cache F' V' C' R' ->
  (forall w, (exists y T, way_ID_in w T /\ NatMap.find y R = Some T) ->
  (exists s, CacheletMap.In (w, s) C)) ->
  (forall w, (exists y T, way_ID_in w T /\ NatMap.find y R' = Some T) ->
  (exists s, CacheletMap.In (w, s) C')).
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
    exact (H6 w H5).
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
    injection A0; injection A1; intros X0 X1; subst s0 s2; clear A0 A1.
    assert (WFH1 := WFH).
    unfold well_defined_cache_tree in WFH1.
    destruct WFH1 as [ WFH1 WFH2 ]. destruct WFH2 as [ WFH2 WFH3 ]. destruct WFH3 as [ WFH3 WFH4 ].
    case_eq (eqb index a).
    {
      intros H9; apply cmp_to_eq in H9; subst a.
      rewrite -> H7 in H0.
      injection H0; intros X0; subst s.
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
        apply (wf8_2_clear_remapping_list r r0 F V C R c v w s).
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
        injection WFH2; intros X0; subst p0.
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
        apply (wf8_2_clear_remapping_list r r0 F V C R c v w s).
        exact H8. exact H10. exact H6.
        discriminate.
        intros; destruct (NatMap.find r v0).
        discriminate.
        discriminate.
      }
    }
    {
      intros H4; apply cmp_to_uneq in H4.
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
        injection WFH2; intros X0; subst p0.
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

(* WF8-2 Preservation *)
Lemma wf8_2_preservation : forall sigma obs sigma' obs',
  wf8_2 sigma -> <<sigma; obs>> ===> <<sigma'; obs'>> -> wf8_2 sigma'.
Proof.
  destruct sigma; destruct sigma'.
  unfold wf8_2 in *.
  intros obs' H H0 k mu rho pi lambda F V C R H1 H2; injection H1;
  intros X0 X1 X2 X3; subst.
  inversion H0. inversion H14; subst.
  - case_eq (NatMap.find lambda m). intros s0 H4; subst.
    destruct s0.
    apply (wf8_2_mlc_read lambda0 h_tree m e' mu l0 D delta obs0 k lambda (single_level_cache c v w s)
    (single_level_cache F V C R) c v w s F V C R).
    exact H22. exact H33. exact H4. exact H2.
    reflexivity. reflexivity.
    apply (H m mu rho p lambda c v w s).
    reflexivity. exact H4.
    intros H4. apply (wf_mlc_read_none lambda0 h_tree m e' mu l0 D delta obs0 k lambda) in H4.
    rewrite -> H2 in H4.
    discriminate. exact H22. exact H33.
  - case_eq (NatMap.find lambda m). intros s0 H4; subst.
    destruct s0.
    apply (wf8_2_mlc_alloc lambda0 h_tree r_bar_val n m k lambda (single_level_cache c v w s)
    (single_level_cache F V C R) c v w s F V C R).
    exact H29. exact H39. exact H4. exact H2.
    reflexivity. reflexivity.
    apply (H m mu rho p lambda c v w s).
    reflexivity. exact H4.
    intros H4. apply (wf_mlc_alloc_none lambda0 h_tree r_bar_val n m k lambda) in H39.
    rewrite -> H39 in H2.
    discriminate. exact H29. exact H4.
  - case_eq (NatMap.find lambda m). intros s0 H4; subst.
    destruct s0.
    apply (wf8_2_mlc_write lambda0 h_tree m e' m0 l0 v D obs1 mu k lambda (single_level_cache c v0 w s)
    (single_level_cache F V C R) c v0 w s F V C R).
    exact H22. exact H33. exact H4. exact H2.
    reflexivity. reflexivity.
    apply (H m m0 rho p lambda c v0 w s).
    reflexivity. exact H4.
    intros H4. apply (wf_mlc_write_none lambda0 h_tree m e' m0 l0 v D obs1 mu k lambda) in H4.
    rewrite -> H2 in H4.
    discriminate. exact H22. exact H33.
  - case_eq (NatMap.find lambda m). intros s0 H4; subst.
    destruct s0.
    apply (wf8_2_mlc_dealloc lambda0 h_tree r_val m k lambda (single_level_cache c v w s)
    (single_level_cache F V C R) c v w s F V C R).
    exact H26. exact H34. exact H4. exact H2. reflexivity. reflexivity.
    apply (H m m0 rho p lambda c v w s).
    reflexivity. exact H4.
    intros H4. apply (wf_mlc_dealloc_none lambda0 h_tree r_val m k lambda) in H34.
    rewrite -> H34 in H2.
    discriminate. exact H26. exact H4.
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

(* Well-Formed 9 *)
Definition wf9 (sigma: runtime_state): Prop :=
  forall k mu rho pi lambda F V C R,
  sigma = runtime_state_value k mu rho pi ->
  (NatMap.find lambda k = Some (single_level_cache F V C R)) ->
  forall e T, (contains_enclave_prop e T -> (exists x, NatMap.find x R = Some T) ->
  (e = enclave_ID_inactive \/ (exists raw_e, e = enclave_ID_active raw_e /\ NatMap.In raw_e V))).

(* WF9 MLC Read *)
Lemma contains_enclave_prop_update : forall e' p w e,
  contains_enclave_prop e' (update p w e) -> contains_enclave_prop e' p.
Proof.
  intros.
  induction p.
  unfold contains_enclave_prop.
  unfold contains_enclave_prop in H.
  unfold update in *. unfold recursive_update in H.
  fold recursive_update in *.
  case_eq (equal_enclave_IDs e e0); intros.
  assert (A0 := H0); destruct (equal_enclave_IDs e e0) in H, A0.
  destruct (contains_way_ID w p1).
  fold contains_enclave_prop in *.
  unfold equal_enclave_IDs in H0. destruct e; destruct e0.
  apply cmp_to_eq in H0; intros; subst.
  destruct H. left. exact H.
  destruct H. right; left. apply IHp1; exact H.
  right; right. apply IHp1; exact H.
  discriminate. discriminate.
  destruct H. left. exact H.
  destruct H. right; left. apply IHp1; exact H.
  right; right. apply IHp1; exact H.
  destruct (contains_way_ID w p2).
  fold contains_enclave_prop in *.
  unfold equal_enclave_IDs in H0. destruct e; destruct e0.
  apply cmp_to_eq in H0; intros; subst.
  destruct H. left. exact H.
  destruct H. right; left. exact H.
  right; right. exact H.
  discriminate. discriminate.
  destruct H. left. exact H.
  destruct H. right; left. exact H.
  right; right. exact H.
  fold contains_enclave_prop in *.
  unfold equal_enclave_IDs in H0. destruct e; destruct e0.
  apply cmp_to_eq in H0; intros; subst.
  destruct H. left. exact H.
  destruct H. right; left. exact H.
  right; right. exact H.
  discriminate. discriminate.
  destruct H. left. exact H.
  destruct H. right; left. exact H.
  right; right. exact H.
  discriminate.
  assert (A0 := H0); destruct (equal_enclave_IDs e e0) in H, A0.
  destruct (contains_way_ID w p1).
  fold contains_enclave_prop in *.
  unfold equal_enclave_IDs in H0. destruct e; destruct e0; discriminate.
  discriminate.

  unfold equal_enclave_IDs in H0. destruct e; destruct e0.
  apply cmp_to_uneq in H0.
  fold contains_enclave_prop in *.
  destruct H.

  give_up.

  destruct H. right; left. apply IHp1; exact H.
  right; right. apply IHp1; exact H.
  fold contains_enclave_prop in *.
  unfold equal_enclave_IDs in H0. destruct e; destruct e0; discriminate.
  discriminate.


  unfold contains_enclave_prop in *.
  destruct p. unfold update in H.
  unfold recursive_update in H. destruct e0.
  exact H. destruct (eqb w w0).
  unfold equal_enclave_IDs_prop in *.
  destruct e'. destruct e.
  give_up.
  exact H.
  auto.
  exact H.
Admitted.

Lemma wf9_cc_hit_read : forall psi e mem l D delta c psi' F V C R F' V' C' R',
  cc_hit_read psi (enclave_state_value e mem) l = cc_hit_read_valid D delta c psi' ->
  psi = single_level_cache F V C R ->
  psi' = single_level_cache F' V' C' R' ->
  (forall e T, contains_enclave_prop e T -> (exists x, NatMap.find x R = Some T) ->
  e = enclave_ID_inactive \/ (exists raw_e, e = enclave_ID_active raw_e /\ NatMap.In raw_e V)) ->
  (forall e T, contains_enclave_prop e T -> (exists x, NatMap.find x R' = Some T) ->
  e = enclave_ID_inactive \/ (exists raw_e, e = enclave_ID_active raw_e /\ NatMap.In raw_e V')).
Proof.
  intros.
  subst psi psi'.
  unfold cc_hit_read in H.
  case_eq (cc_unfold (single_level_cache F V C R)
  (enclave_state_value e mem) l). intros.
  assert (A0 := H0).
  destruct (cc_unfold (single_level_cache F V C R)
  (enclave_state_value e mem) l) in A0, H.
  destruct c3.
  injection A0; intros; subst; clear A0.
  apply cc_unfold_psi in H0.
  injection H0; intros; subst c0 v w s.
  destruct w0.
  case_eq (NatMap.find s1 R). intros p H1.
  assert (A0 := H1); destruct (NatMap.find s1 R) in H, A0.
  injection A0; injection H; intros; subst; clear A0.
  destruct H4 as (y & H4).
  case_eq (eqb s1 y); intros.
  apply cmp_to_eq in H5; subst.
  apply (H2 e0 p). assert (Some T = Some (update p w3 e)).
  rewrite <- H4. apply NatMapFacts.add_eq_o; reflexivity.
  injection H5; intros; subst.





  eexists y; exact H1.
  apply cmp_to_uneq in H5.
  apply (H2 e0 T). eexists y.
  rewrite <- H4. apply eq_sym.
  apply NatMapFacts.add_neq_o; exact H5.
  discriminate.
  destruct (NatMap.find s1 R); discriminate.
  discriminate.
  destruct cc_unfold; discriminate.
Qed.
(*
Lemma cc_update_r_range : forall psi e' d l0 c0 psi' F V C R F' V' C' R',
  cc_update psi e' d l0 = cc_update_valid c0 psi' ->
  psi = single_level_cache F V C R ->
  psi' = single_level_cache F' V' C' R' ->
  forall x, ((exists y T, way_ID_in x T /\ NatMap.find y R = Some T) <->
  (exists y T, way_ID_in x T /\ NatMap.find y R' = Some T)).
Proof.
  intros.
  subst psi psi'.
  unfold cc_update in H.
  case_eq (cc_unfold (single_level_cache F V C R) e' l0). intros.
  assert (A0 := H0). destruct (cc_unfold (single_level_cache F V C R) e' l0) in A0, H.
  assert (H1 := H0).
  apply cc_unfold_psi in H0.
  apply cc_unfold_c in H1.
  injection A0; intros; subst; clear A0.
  injection H0; intros; subst c v w s.
  destruct c1.
  destruct w0.
  destruct e'.
  case_eq (NatMap.find s R); intros.
  assert (A0 := H2); destruct (NatMap.find s R) in H, A0.
  injection A0; intros; subst; clear A0.
  destruct (replace p e).
  injection H; intros; subst.
  split; intros.
  {
    destruct H3 as (y & T & H3 & H4).
    case_eq (eqb s y); intros.
    apply cmp_to_eq in H5; subst.
    rewrite -> H2 in H4.
    injection H4; intros; subst.
    eexists y; eexists (update T w e).
    split. apply way_ID_in_update. exact H3.
    apply NatMapFacts.add_eq_o; reflexivity.
    apply cmp_to_uneq in H5.
    eexists y; eexists T. split. exact H3.
    rewrite <- H4. apply NatMapFacts.add_neq_o; exact H5.
  }
  {
    destruct H3 as (y & T & H3 & H4).
    case_eq (eqb s y); intros.
    apply cmp_to_eq in H5; subst.
    assert (Some T = Some (update p w e)).
    rewrite <- H4. apply NatMapFacts.add_eq_o; reflexivity.
    injection H5; intros; subst.
    eexists y; eexists p. split.
    apply way_ID_in_update in H3. exact H3. exact H2.
    apply cmp_to_uneq in H5.
    eexists y; eexists T. split. exact H3.
    rewrite <- H4. apply eq_sym. apply NatMapFacts.add_neq_o; exact H5.
  }
  discriminate.
  discriminate.
  destruct (NatMap.find s R); discriminate.
  discriminate.
  intros; destruct (cc_unfold (single_level_cache F V C R) e' l0).
  discriminate.
  discriminate.
Qed.
*)

Lemma wf9_mlc_read : forall lambda h_tree k e' m0 l0 D obs1 mu k' index psi psi'
  F V C R F' V' C' R',
  well_defined_cache_tree h_tree ->
  mlc_read k e' m0 l0 lambda h_tree = mlc_read_valid D obs1 mu k' ->
  NatMap.find index k = Some psi ->
  NatMap.find index k' = Some psi' ->
  psi = single_level_cache F V C R ->
  psi' = single_level_cache F' V' C' R' ->
  (forall e T, (contains_enclave_prop e T ->
  (exists x, NatMap.find x R = Some T) ->
  (e = enclave_ID_inactive \/ (exists raw_e, e = enclave_ID_active raw_e /\ NatMap.In raw_e V)))) ->
  (forall e T, (contains_enclave_prop e T ->
  (exists x, NatMap.find x R' = Some T) ->
  (e = enclave_ID_inactive \/ (exists raw_e, e = enclave_ID_active raw_e /\ NatMap.In raw_e V')))).
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
    apply (H8 e T H9 H10).
    discriminate.
  }
  {
    intros lambda IHTREE k e' m0 l0 D obs1 mu k' index psi psi' F V C R
    F' V' C' R' H H0 H1 H2 H3 H4 H7.
    unfold recursive_mlc_read in H0.
    fold recursive_mlc_read in H0.
    case_eq (NatMap.find a k). intros s H5.
    assert (A0 := H5). destruct (NatMap.find a k) in A0, H0.
    case_eq (cc_hit_read s0 e' l0). intros d d0 c s1 H6.
    assert (A1 := H6). destruct (cc_hit_read s0 e' l0) in A1, H0.
    injection H0; injection A0; injection A1; intros X0 X1 X2 X3 X4 X5 X6 X7 X8; subst; clear A0 A1.
    assert (H8 := H6). destruct s; destruct s1.
    (*
    apply (cc_hit_read_v (single_level_cache c0 v w s) e' l0 D obs1 c
    (single_level_cache c1 v0 w0 s0) c0 v w s c1 v0 w0 s0) in H6.
    destruct e'.
    assert (forall x, ((exists y T, way_ID_in x T /\ NatMap.find y s = Some T) <->
    (exists y T, way_ID_in x T /\ NatMap.find y s0 = Some T))).
    apply (cc_hit_read_r_range (single_level_cache c0 v w s) e e0 l0 D obs1 c
    (single_level_cache c1 v0 w0 s0) c0 v w s c1 v0 w0 s0 H8).
    reflexivity. reflexivity. subst v0.
    *)
    {
      case_eq (eqb a index).
      {
        intros H3. apply cmp_to_eq in H3. subst.
        rewrite -> H1 in H5.
        injection H5; intros X0 X1 X2 X3; subst c0 v w s.
        assert (NatMap.find index (NatMap.add index (single_level_cache c1 v0 w0 s0) k) =
        Some (single_level_cache c1 v0 w0 s0)).
        apply NatMapFacts.add_eq_o. reflexivity.
        rewrite -> H2 in H3; injection H3; intros X0 X1 X2 X3; subst.
        destruct e'. intros e1 T H4.
        apply (wf9_cc_hit_read (single_level_cache F V C R) e e0 l0 D obs1
        c (single_level_cache c1 v0 w0 s0) F V C R c1 v0 w0 s0).
        exact H6. reflexivity. reflexivity.
        intros e2 T0. apply (H7 e2 T0).




        apply (H7 w s0) in H6. apply H3.
        apply H3 in H6. apply H3. exact H6.
        apply (H7 w s0). apply H3. exact H6.
      }
      {
        intros. apply cmp_to_uneq in H4.
        assert (NatMap.find index (NatMap.add a (single_level_cache c1 v0 w1 s1) k) = NatMap.find index k).
        apply NatMapFacts.add_neq_o. exact H4.
        rewrite -> H2 in H9.
        rewrite -> H1 in H9.
        injection H9; intros; subst F' V' C' R'.
        exact (H7 w s0).
      }
    }
    reflexivity.
    reflexivity.
    discriminate.
    intros; destruct (cc_hit_read s1 e' l0).
    discriminate.
    case_eq (recursive_mlc_read k e' m0 l0 l). intros.
    assert (A1 := H8). destruct (recursive_mlc_read k e' m0 l0 l) in A1, H0.
    case_eq (cc_update s1 e' d1 l0). intros.
    assert (A2 := H9). destruct (cc_update s1 e' d1 l0) in A2, H0.
    injection H0; injection A0; injection A1; injection A2; intros; subst; clear A0 A1 A2.
    {
      case_eq (eqb index a).
      {
        intros. apply cmp_to_eq in H3. subst a.
        destruct s.
        destruct s2.
        assert (forall c, CacheletMap.In c w0 <-> CacheletMap.In c w1); intros.
        apply (cc_update_c (single_level_cache c0 v w0 s) e' D l0 c (single_level_cache c1 v0 w1 s1)
        c0 v w0 s c1 v0 w1 s1 c2 H9). reflexivity. reflexivity.
        assert (forall x, ((exists y T, way_ID_in x T /\ NatMap.find y s = Some T) <->
        (exists y T, way_ID_in x T /\ NatMap.find y s1 = Some T))).
        apply (cc_update_r_range (single_level_cache c0 v w0 s) e' D l0 c (single_level_cache c1 v0 w1 s1)
        c0 v w0 s c1 v0 w1 s1 H9). reflexivity. reflexivity.
        assert (NatMap.find index (NatMap.add index (single_level_cache c1 v0 w1 s1) m) =
        Some (single_level_cache c1 v0 w1 s1)).
        apply NatMapFacts.add_eq_o. reflexivity.
        rewrite -> H10 in H2.
        rewrite -> H5 in H1.
        injection H1; injection H2; intros; subst.
        split; intros.
        apply H4. apply (H7 w s0). apply H3. exact H11.
        apply H3. apply H7. apply H4. exact H11.
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
    intros; destruct (cc_update s1 e' d1 l0); discriminate.
    discriminate.
    intros; destruct (recursive_mlc_read k e' m0 l0 l); discriminate.
    discriminate.
    intros; destruct (NatMap.find a k); discriminate.
  }
  intros; destruct (get_cache_ID_path lambda h_tree); discriminate.
Qed.

(* WF8 MLC Allocation *)
Lemma wf8_cachelet_allocation : forall n r F V C R F' V' C' R',
  cachelet_allocation n r (single_level_cache F V C R) = Some (single_level_cache F' V' C' R') ->
  (forall w s, CacheletMap.In (w, s) C <-> exists y T, way_ID_in w T
  /\ NatMap.find y R = Some T) ->
  (forall w s, CacheletMap.In (w, s) C' <-> exists y T, way_ID_in w T
  /\ NatMap.find y R' = Some T).
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
    exact (H0 w s).
  }
  {
    intros.
    unfold recursive_cachelet_allocation in H.
    fold recursive_cachelet_allocation in H.
    case_eq (way_first_allocation F); intros.
    assert (A0 := H1); destruct (way_first_allocation F) in H, A0.
    destruct c0.
    case_eq (NatMap.find s0 R); intros.
    assert (A1 := H2); destruct (NatMap.find s0 R) in H, A1.
    case_eq (remove_CAT (w0, s0) F). intros c0 F0.
    assert (A3 := F0). destruct (remove_CAT (w0, s0) F) in H, A3.
    case_eq (NatMap.find r V). intros r0 H5.
    assert (A2 := H5). destruct (NatMap.find r V) in H, A2.
    injection A0; injection A1; injection A2; injection A3;
    intros X0 X1 X2 X3; subst; clear A0 A1 A2 A3.
    {
      apply (IHn0 c0 (NatMap.add r ((w0, s0) :: r0) V) C
      (NatMap.add s0 (update p w0 (enclave_ID_active r)) R) F' V' C' R').
      exact H. split; intros.
      apply (H0 w1 s1) in H3. destruct H3 as (y & T & H3 & H4).
      case_eq (eqb s0 y); intros.
      apply cmp_to_eq in H6; subst.
      rewrite -> H2 in H4. injection H4; intros; subst.
      eexists y; eexists (update T w0 (enclave_ID_active r)). split.
      apply way_ID_in_update. exact H3.
      apply NatMapFacts.add_eq_o; reflexivity.
      apply cmp_to_uneq in H6.
      eexists y; eexists T. split. exact H3.
      rewrite <- H4. apply NatMapFacts.add_neq_o; exact H6.
      apply H0. destruct H3 as (y & T & H3 & H4).
      case_eq (eqb s0 y); intros.
      apply cmp_to_eq in H6; subst.
      assert (Some T = Some (update p w0 (enclave_ID_active r))).
      rewrite <- H4. apply NatMapFacts.add_eq_o; reflexivity.
      injection H6; intros; subst.
      eexists y; eexists p. split.
      apply way_ID_in_update in H3. exact H3. exact H2.
      apply cmp_to_uneq in H6.
      eexists y; eexists T. split. exact H3.
      rewrite <- H4. apply eq_sym.
      apply NatMapFacts.add_neq_o; exact H6.
    }
    discriminate.
    intros H5; assert (A2 := H5); destruct (NatMap.find r V) in A2, H.
    discriminate.
    injection A0; injection A1; injection A3; intros X0 X1 X2; subst; clear A0 A1 A2 A3.
    {
      apply (IHn0 c0 (NatMap.add r ((w0, s0) :: nil) V) C
      (NatMap.add s0 (update p w0 (enclave_ID_active r)) R) F' V' C' R').
      exact H. split; intros.
      apply H0 in H3. destruct H3 as (y & T & H3 & H4).
      case_eq (eqb s0 y); intros.
      apply cmp_to_eq in H6; subst.
      rewrite -> H2 in H4. injection H4; intros; subst.
      eexists y; eexists (update T w0 (enclave_ID_active r)).
      split. apply way_ID_in_update. exact H3.
      apply NatMapFacts.add_eq_o; reflexivity.
      apply cmp_to_uneq in H6.
      eexists y; eexists T. split. exact H3.
      rewrite <- H4. apply NatMapFacts.add_neq_o; exact H6.
      destruct H3 as (y & T & H3 & H4).
      apply H0. case_eq (eqb s0 y); intros.
      apply cmp_to_eq in H6; subst.
      assert (Some T = Some (update p w0 (enclave_ID_active r))).
      rewrite <- H4. apply NatMapFacts.add_eq_o; reflexivity.
      injection H6; intros; subst.
      eexists y; eexists p. split. apply way_ID_in_update in H3.
      exact H3. exact H2.
      apply cmp_to_uneq in H6. eexists y; eexists T.
      split. exact H3. rewrite <- H4. apply eq_sym.
      apply NatMapFacts.add_neq_o; exact H6.
    }
    discriminate.
    intros; destruct (remove_CAT (w0, s0) F); discriminate.
    discriminate.
    intros; destruct (NatMap.find s0 R); discriminate.
    discriminate.
    intros; destruct (way_first_allocation F); discriminate.
  }
Qed.

Lemma wf8_mlc_alloc : forall lambda h_tree n state k k' index psi psi' F V C R F' V' C' R',
  well_defined_cache_tree h_tree ->
  mlc_allocation n state k lambda h_tree = Some k' ->
  NatMap.find index k = Some psi ->
  NatMap.find index k' = Some psi' ->
  psi = single_level_cache F V C R ->
  psi' = single_level_cache F' V' C' R' ->
  (forall w s, CacheletMap.In (w, s) C <-> exists y T, way_ID_in w T
  /\ NatMap.find y R = Some T) ->
  (forall w s, CacheletMap.In (w, s) C' <-> exists y T, way_ID_in w T
  /\ NatMap.find y R' = Some T).
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
    exact (H6 w s).
  }
  {
    intros lambda IHTREE n r k k' index psi psi' F V C R
    F' V' C' R' WFH H H0 H1 H4 H5 H6.
    unfold recursive_mlc_allocation in H.
    fold recursive_mlc_allocation in H.
    destruct n. discriminate.
    case_eq (NatMap.find a k). intros.
    assert (A0 := H2). destruct (NatMap.find a k) in A0, H.
    case_eq (cachelet_allocation n r s1). intros.
    assert (A1 := H3). destruct (cachelet_allocation n r s1) in A1, H.
    injection A0; injection A1; intros; subst s1 s3; clear A0 A1.
    assert (WFH1 := WFH).
    unfold well_defined_cache_tree in WFH1.
    destruct WFH1 as [ WFH1 WFH2 ]. destruct WFH2 as [ WFH2 WFH3 ]. destruct WFH3 as [ WFH3 WFH4 ].
    case_eq (eqb index a).
    {
      intros; apply cmp_to_eq in H7; subst a.
      rewrite -> H2 in H0.
      injection H0; intros; subst s.
      destruct s2.
      destruct l.
      {
        apply (IHl root_node WFH1 n0 r (NatMap.add index (single_level_cache c v w0 s) k)
        k' index (single_level_cache c v w0 s) psi' c v w0 s F' V' C' R').
        exact WFH.
        exact H.
        apply NatMapFacts.add_eq_o. reflexivity.
        exact H1.
        reflexivity.
        exact H5.
        apply (wf8_cachelet_allocation n r F V C R c v w0 s).
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
        apply (IHl (cache_node p) IHTREE n0 r (NatMap.add index (single_level_cache c v w0 s) k)
        k' index (single_level_cache c v w0 s) psi' c v w0 s F' V' C' R').
        exact WFH.
        exact H.
        apply NatMapFacts.add_eq_o. reflexivity.
        exact H1.
        reflexivity.
        exact H5.
        apply (wf8_cachelet_allocation n r F V C R c v w0 s).
        subst psi; exact H3. exact H6.
      }
    }
    {
      intros; apply cmp_to_uneq in H7.
      destruct l.
      {
        apply (IHl root_node WFH1 n0 r (NatMap.add a s2 k) k' index psi psi' F V C R F' V' C' R').
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
        apply (IHl (cache_node p) IHTREE n0 r (NatMap.add a s2 k) k' index psi psi' F V C R F' V' C' R').
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
    intros; destruct (cachelet_allocation n r s1); discriminate.
    discriminate.
    intros; destruct (NatMap.find a k); discriminate.
  }
  intros; destruct (get_cache_ID_path lambda h_tree); discriminate.
Qed.

(* WF8 MLC Write *)
Lemma cc_hit_write_r_range : forall psi e' l v D c0 psi' F V C R F' V' C' R',
  cc_hit_write psi e' l v = cc_hit_write_valid D c0 psi' ->
  psi = single_level_cache F V C R ->
  psi' = single_level_cache F' V' C' R' ->
  forall x, ((exists y T, way_ID_in x T /\ NatMap.find y R = Some T) <->
  (exists y T, way_ID_in x T /\ NatMap.find y R' = Some T)).
Proof.
  intros.
  split.
  {
    intros.
    subst psi psi'.
    unfold cc_hit_write in H.
    case_eq (cc_unfold (single_level_cache F V C R) e' l). intros.
    assert (A0 := H0). destruct (cc_unfold (single_level_cache F V C R) e' l) in A0, H.
    injection A0; intros; subst; clear A0.
    assert (H1 := H0).
    apply cc_unfold_psi in H0.
    injection H0; intros; subst c v0 w s.
    destruct c1.
    destruct w0.
    case_eq (NatMap.find s R); intros.
    assert (A0 := H3); destruct (NatMap.find s R) in A0, H.
    injection A0; intros; subst; clear A0.
    destruct v.
    discriminate.
    destruct e'.
    injection H; intros; subst.
    destruct H2 as (y & T & H2 & H4).
    case_eq (eqb s y); intros.
    apply cmp_to_eq in H5; subst.
    rewrite -> H3 in H4. injection H4; intros; subst.
    eexists y; eexists (update T w e). split.
    apply way_ID_in_update. exact H2.
    apply NatMapFacts.add_eq_o; reflexivity.
    apply cmp_to_uneq in H5.
    eexists y; eexists T. split. exact H2.
    rewrite <- H4. apply NatMapFacts.add_neq_o; exact H5.
    discriminate.
    destruct (NatMap.find s R); discriminate.
    discriminate.
    intros; destruct (cc_unfold (single_level_cache F V C R) e' l); discriminate.
  }
  {
    intros.
    subst psi psi'.
    unfold cc_hit_write in H.
    case_eq (cc_unfold (single_level_cache F V C R) e' l). intros.
    assert (A0 := H0). destruct (cc_unfold (single_level_cache F V C R) e' l) in A0, H.
    injection A0; intros; subst; clear A0.
    assert (H1 := H0).
    apply cc_unfold_psi in H0.
    injection H0; intros; subst c v0 w s.
    destruct c1.
    destruct w0.
    case_eq (NatMap.find s R); intros.
    assert (A0 := H3); destruct (NatMap.find s R) in A0, H.
    injection A0; intros; subst; clear A0.
    destruct v.
    discriminate.
    destruct e'.
    injection H; intros; subst.
    destruct H2 as (y & T & H2 & H4).
    case_eq (eqb s y); intros.
    apply cmp_to_eq in H5; subst.
    assert (Some T = Some (update p w e)).
    rewrite <- H4. apply NatMapFacts.add_eq_o; reflexivity.
    injection H5; intros; subst.
    eexists y; eexists p. split. apply way_ID_in_update in H2.
    exact H2. exact H3.
    apply cmp_to_uneq in H5.
    eexists y; eexists T. split. exact H2.
    rewrite <- H4. apply eq_sym. apply NatMapFacts.add_neq_o; exact H5.
    discriminate.
    destruct (NatMap.find s R); discriminate.
    discriminate.
    intros; destruct (cc_unfold (single_level_cache F V C R) e' l); discriminate.
  }
Qed.

Lemma wf8_mlc_write : forall lambda h_tree k e' m0 l0 v D obs1 mu k' index psi psi'
  F V C R F' V' C' R',
  well_defined_cache_tree h_tree ->
  mlc_write k e' m0 l0 v lambda h_tree = mlc_write_valid D obs1 mu k' ->
  NatMap.find index k = Some psi ->
  NatMap.find index k' = Some psi' ->
  psi = single_level_cache F V C R ->
  psi' = single_level_cache F' V' C' R' ->
  (forall w s, CacheletMap.In (w, s) C <-> exists y T, way_ID_in w T
  /\ NatMap.find y R = Some T) ->
  (forall w s, CacheletMap.In (w, s) C' <-> exists y T, way_ID_in w T
  /\ NatMap.find y R' = Some T).
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
    exact (H6 w s).
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
    case_eq (cc_hit_write s1 e' l0 v); intros.
    assert (A1 := H5). destruct (cc_hit_write s1 e' l0 v) in A1, H. destruct l0.
    injection H; injection A0; injection A1; intros; subst; clear A0 A1.
    destruct s; destruct s2.
    assert (forall x, CacheletMap.In x w0 <-> CacheletMap.In x w1). intros.
    apply (cc_hit_write_c (single_level_cache c0 v0 w0 s) e' (address b d1) v D c
    (single_level_cache c1 v1 w1 s1) c0 v0 w0 s c1 v1 w1 s1 x H5).
    reflexivity. reflexivity.
    assert (forall x, ((exists y T, way_ID_in x T /\ NatMap.find y s = Some T) <->
    (exists y T, way_ID_in x T /\ NatMap.find y s1 = Some T))).
    apply (cc_hit_write_r_range (single_level_cache c0 v0 w0 s) e' (address b d1) v D c
    (single_level_cache c1 v1 w1 s1) c0 v0 w0 s c1 v1 w1 s1 H5).
    reflexivity. reflexivity.
    {
      case_eq (eqb a index).
      {
        intros. apply cmp_to_eq in H7. subst.
        rewrite -> H0 in H4.
        injection H4; intros; subst c0 v0 w0 s.
        assert (NatMap.find index (NatMap.add index (single_level_cache c1 v1 w1 s1) k) =
        Some (single_level_cache c1 v1 w1 s1)).
        apply NatMapFacts.add_eq_o. reflexivity.
        rewrite -> H7 in H1.
        injection H1; intros; subst c1 v1 w1 s1.
        split; intros.
        apply H3. apply (H6 w s0). apply H2. exact H8.
        apply H2. apply H6. apply H3. exact H8.
      }
      {
        intros. apply cmp_to_uneq in H7.
        assert (NatMap.find index (NatMap.add a (single_level_cache c1 v1 w1 s1) k) = NatMap.find index k).
        apply NatMapFacts.add_neq_o. exact H7.
        rewrite -> H1 in H8.
        rewrite -> H0 in H8.
        injection H8; intros; subst F' V' C' R'.
        exact (H6 w s0).
      }
    }
    discriminate.
    intros; destruct (cc_hit_write s1 e' l0).
    discriminate.
    case_eq (recursive_mlc_write k e' m0 l0 v l). intros.
    assert (A1 := H7). destruct (recursive_mlc_write k e' m0 l0 v l) in A1, H.
    case_eq (cc_update s1 e' d0 l0). intros.
    assert (A2 := H8). destruct (cc_update s1 e' d0 l0) in A2, H.
    injection H; injection A0; injection A1; injection A2; intros; subst; clear A0 A1 A2.
    {
      case_eq (eqb index a).
      {
        intros. apply cmp_to_eq in H2. subst a.
        destruct s.
        destruct s2.
        assert (forall c, CacheletMap.In c w0 <-> CacheletMap.In c w1); intros.
        apply (cc_update_c (single_level_cache c0 v0 w0 s) e' D l0 c (single_level_cache c1 v1 w1 s1)
        c0 v0 w0 s c1 v1 w1 s1 c2 H8). reflexivity. reflexivity.
        assert (forall x, ((exists y T, way_ID_in x T /\ NatMap.find y s = Some T) <->
        (exists y T, way_ID_in x T /\ NatMap.find y s1 = Some T))).
        apply (cc_update_r_range (single_level_cache c0 v0 w0 s) e' D l0 c (single_level_cache c1 v1 w1 s1)
        c0 v0 w0 s c1 v1 w1 s1 H8). reflexivity. reflexivity.
        assert (NatMap.find index (NatMap.add index (single_level_cache c1 v1 w1 s1) m1) =
        Some (single_level_cache c1 v1 w1 s1)).
        apply NatMapFacts.add_eq_o. reflexivity.
        rewrite -> H9 in H1.
        rewrite -> H4 in H0.
        injection H0; injection H1; intros; subst.
        split; intros.
        apply H3. apply (H6 w s0). apply H2. exact H10.
        apply H2. apply H6. apply H3. exact H10.
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
    intros; destruct (cc_update s1 e' d0 l0); discriminate.
    discriminate.
    intros; destruct (recursive_mlc_write k e' m0 l0 v l); discriminate.
    discriminate.
    intros; destruct (NatMap.find a k); discriminate.
  }
  intros; destruct (get_cache_ID_path lambda h_tree); discriminate.
Qed.

(* WF8 MLC Deallocation *)
Lemma wf8_clear_remapping_list : forall r l F V C R F' V' C' R',
  clear_remapping_list r l F V C R = Some (single_level_cache F' V' C' R') ->
  NatMap.find r V = Some l ->
  (forall w s, CacheletMap.In (w, s) C <-> exists y T, way_ID_in w T
  /\ NatMap.find y R = Some T) ->
  (forall w s, CacheletMap.In (w, s) C' <-> exists y T, way_ID_in w T
  /\ NatMap.find y R' = Some T).
Proof.
  intros r l.
  induction l.
  {
    intros F V C R F' V' C' R' H H0.
    unfold clear_remapping_list in H.
    injection H; intros; subst.
    exact (H5 w s).
  }
  {
    intros F V C R F' V' C' R' H H0 B.
    unfold clear_remapping_list in H.
    fold clear_remapping_list in H.
    destruct a.
    case_eq (NatMap.find s R). intros p H4.
    assert (A0 := H4). destruct (NatMap.find s R) in A0, H.
    case_eq (cachelet_invalidation C (w, s)). intros w1 H5.
    assert (A1 := H5). destruct (cachelet_invalidation C (w, s)) in A1, H.
    injection A0; injection A1; intros X Y; subst w1 p; clear A0 A1.
    {
      apply (IHl ((w, s) :: F) (NatMap.add r l V) w0 (NatMap.add s (update p0 w
      (enclave_ID_active r)) R) F' V' C' R' H).
      apply NatMapFacts.add_eq_o; reflexivity.
      split; intros.
      apply (cachelet_invalidation_c (w1, s0) (w, s) C w0 H5) in H1.
      apply B in H1. destruct H1 as (y & T & H1 & H2).
      case_eq (eqb s y); intros.
      apply cmp_to_eq in H3; subst.
      rewrite -> H4 in H2. injection H2; intros; subst.
      eexists y; eexists (update T w (enclave_ID_active r)). split.
      apply way_ID_in_update. exact H1.
      apply NatMapFacts.add_eq_o; reflexivity.
      apply cmp_to_uneq in H3.
      eexists y; eexists T. split. exact H1.
      rewrite <- H2. apply NatMapFacts.add_neq_o; exact H3.
      apply (cachelet_invalidation_c (w1, s0) (w, s) C w0 H5).
      apply B. destruct H1 as (y & T & H1 & H2).
      case_eq (eqb s y); intros.
      apply cmp_to_eq in H3; subst.
      assert (Some T = Some (update p0 w (enclave_ID_active r))).
      rewrite <- H2. apply NatMapFacts.add_eq_o; reflexivity.
      injection H3; intros; subst.
      eexists y; eexists p0. split.
      apply way_ID_in_update in H1. exact H1. exact H4.
      apply cmp_to_uneq in H3.
      eexists y; eexists T. split. exact H1.
      rewrite <- H2. apply eq_sym.
      apply NatMapFacts.add_neq_o; exact H3.
    }
    discriminate.
    intros; destruct (cachelet_invalidation C (w, s)); discriminate.
    discriminate.
    intros; destruct (NatMap.find s R); discriminate.
  }
Qed.

Lemma wf8_mlc_dealloc : forall lambda h_tree state k k' index psi psi' F V C R F' V' C' R',
  well_defined_cache_tree h_tree ->
  mlc_deallocation state k lambda h_tree = Some k' ->
  NatMap.find index k = Some psi ->
  NatMap.find index k' = Some psi' ->
  psi = single_level_cache F V C R ->
  psi' = single_level_cache F' V' C' R' ->
  (forall w s, CacheletMap.In (w, s) C <-> exists y T, way_ID_in w T
  /\ NatMap.find y R = Some T) ->
  (forall w s, CacheletMap.In (w, s) C' <-> exists y T, way_ID_in w T
  /\ NatMap.find y R' = Some T).
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
    exact (H6 w s).
  }
  {
    intros lambda IHTREE k k' index psi psi' F V C R
    F' V' C' R' WFH H H0 H1 H2 H3 H6 w' s'.
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
        intros.
        apply (wf8_clear_remapping_list r r0 F V C R c v w s).
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
        apply (wf8_clear_remapping_list r r0 F V C R c v w s).
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

(* WF8-1 Preservation *)
Lemma wf8_1_preservation : forall sigma obs sigma' obs',
  wf8 sigma -> <<sigma; obs>> ===> <<sigma'; obs'>> -> wf8 sigma'.
Proof.
  destruct sigma; destruct sigma'.
  unfold wf8 in *.
  intros; injection H1; intros.
  inversion H0. inversion H18; subst.
  - case_eq (NatMap.find lambda m); intros; subst.
    destruct s0.
    apply (wf8_mlc_read lambda0 h_tree m e' mu l0 D delta obs0 k lambda (single_level_cache c v w0 s0)
    (single_level_cache F V C R) c v w0 s0 F V C R).
    exact H24. exact H35. exact H3. exact H2.
    reflexivity. reflexivity.
    apply (H m mu rho p lambda c v w0 s0).
    reflexivity. exact H3.
    apply (wf_mlc_read_none lambda0 h_tree m e' mu l0 D delta obs0 k lambda) in H3.
    rewrite -> H2 in H3.
    discriminate. exact H24. exact H35.
  - case_eq (NatMap.find lambda m); intros; subst.
    destruct s0.
    apply (wf8_mlc_alloc lambda0 h_tree r_bar_val n m k lambda (single_level_cache c v w0 s0)
    (single_level_cache F V C R) c v w0 s0 F V C R).
    exact H31. exact H41. exact H3. exact H2.
    reflexivity. reflexivity.
    apply (H m mu rho p lambda c v w0 s0).
    reflexivity. exact H3.
    apply (wf_mlc_alloc_none lambda0 h_tree r_bar_val n m k lambda) in H41.
    rewrite -> H41 in H2.
    discriminate. exact H31. exact H3.
  - case_eq (NatMap.find lambda m); intros; subst.
    destruct s0.
    apply (wf8_mlc_write lambda0 h_tree m e' m0 l0 v D obs1 mu k lambda (single_level_cache c v0 w0 s0)
    (single_level_cache F V C R) c v0 w0 s0 F V C R).
    exact H24. exact H35. exact H3. exact H2.
    reflexivity. reflexivity.
    apply (H m m0 rho p lambda c v0 w0 s0).
    reflexivity. exact H3.
    apply (wf_mlc_write_none lambda0 h_tree m e' m0 l0 v D obs1 mu k lambda) in H3.
    rewrite -> H2 in H3.
    discriminate. exact H24. exact H35.
  - case_eq (NatMap.find lambda m); intros; subst.
    destruct s0.
    apply (wf8_mlc_dealloc lambda0 h_tree r_val m k lambda (single_level_cache c v w0 s0)
    (single_level_cache F V C R) c v w0 s0 F V C R).
    exact H28. exact H36. exact H3. exact H2. reflexivity. reflexivity.
    apply (H m m0 rho p lambda c v w0 s0).
    reflexivity. exact H3.
    apply (wf_mlc_dealloc_none lambda0 h_tree r_val m k lambda) in H36.
    rewrite -> H36 in H2.
    discriminate. exact H28. exact H3.
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


(* Well-Formed Memory *)
Definition wf_mu (sigma: runtime_state): Prop :=
  forall k mu rho pi p e l q,
  (sigma = runtime_state_value k mu rho pi) ->
  NatMap.find p pi = Some (process_value e l q) ->
  (exists i, memory_read mu l = Some (memory_value_instruction i)) /\
  (exists k' mu' rho' e0 e1 obs q n l' i,
  << k, mu, rho, e0 | i, q >> -->> << k', mu', rho', e1 | obs, q, n >> ->
  add_to_memory_address mu l n = Some l' -> memory_read mu l' = Some (memory_value_instruction i)). 
