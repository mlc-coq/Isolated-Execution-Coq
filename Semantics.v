From Coq Require Import Lists.List.
Require Import RuntimeDefinitions.
Require Import MLCOperations.
Require Import AppendixF.
Require Import AppendixE.

(* Disjoint Enclave States *)
Definition disjoint_enclave_states (sigma: runtime_state): Prop :=
  forall k mu rho pi p l q e0 E p' l' q' e0' E',
  (sigma = runtime_state_value k mu rho pi) ->
  (NatMap.find p pi = Some (process_value (enclave_state_value e0 E) l q)) ->
  (NatMap.find p' pi = Some (process_value (enclave_state_value e0' E') l' q')) ->
  p <> p' -> ((forall e, NatMap.In e E -> ~NatMap.In e E') /\
  (forall e, NatMap.In e E' -> ~NatMap.In e E)).

(* Single-process State *)
Inductive single_process_state : Type :=
| process_state_value : multi_level_cache -> memory -> registers -> enclave_state -> single_process_state.
Inductive pre_single_process_state : Type :=
| pre_process_state : single_process_state -> instruction -> core_ID -> pre_single_process_state.
Notation "'<<' k ',' m ',' r ',' e '|' i ',' q '>>'" := (pre_process_state (process_state_value k m r e) i q).
Inductive post_single_process_state : Type :=
| post_process_state : single_process_state -> observation_trace -> core_ID -> nat -> post_single_process_state.
Notation "'<<' k ',' m ',' r ',' e '|' obs ',' q ',' n '>>'" := (post_process_state (process_state_value k m r e) obs q n).

(* Single-process Operational Semantics *)
Reserved Notation "c1 '-->>' c2" (at level 40).

Inductive single_process_sem : pre_single_process_state -> post_single_process_state -> Prop :=
| Load: forall k mu rho e i l r q lambda h_tree D delta obs k',
    well_defined_cache_tree h_tree ->
    i = load l r ->
    mlc_read k e mu l lambda h_tree = mlc_read_valid D delta obs k' ->
    <<k, mu, rho, e | i, q>> -->> <<k', mu, rho, e | obs, q, 1>>
| Create: forall k mu rho e i r1 r2 r3 r_bar r_val1 r_val2 r_val2_addr r_val3 r_bar_val q lambda h_tree k' e',
    well_defined_cache_tree h_tree ->
    i = create r1 r2 r3 r_bar ->
    (NatMap.find r1 rho) = Some (memory_value_data (data_value r_val1)) ->
    (NatMap.find r2 rho) = Some (memory_value_data (data_value r_val2)) ->
    (NatMap.find r3 rho) = Some (memory_value_data (data_value r_val3)) ->
    read_register_list rho r_bar = Some (r_bar_val) ->
    number_to_memory_address mu r_val2 = Some (r_val2_addr) ->
    enclave_creation e mu r_val1 r_val2_addr r_val3 = enclave_state_valid e' ->
    mlc_allocation r_bar_val r_val1 k lambda h_tree = Some k' ->
    <<k, mu, rho, e | i, q>> -->> <<k', mu, rho, e' | nil, q, r_val1>>
| Store: forall k mu rho e i r l v q lambda h_tree D obs mu' k',
    well_defined_cache_tree h_tree ->
    i = store r l ->
    mlc_write k e mu l v lambda h_tree = mlc_write_valid D obs mu' k' ->
    <<k, mu, rho, e | i, q>> -->> <<k', mu', rho, e | nil, q, 1>>
| Destroy: forall k mu rho e i r r_val q lambda h_tree k' mu' e',
    well_defined_cache_tree h_tree ->
    i = destroy r ->
    (NatMap.find r rho) = Some (memory_value_data (data_value r_val)) ->
    mlc_deallocation r_val k lambda h_tree = Some k' ->
    reinitialize_memory r_val e mu = Some mu' ->
    enclave_elimination e r_val = enclave_state_valid e' ->
    <<k, mu, rho, e | i, q>> -->> <<k', mu', rho, e' | nil, q, 1>>
| Enter: forall k mu rho e i r q e_state r_val,
    i = enter r ->
    (NatMap.find r rho) = Some (memory_value_data (data_value r_val)) ->
    (active_enclave_update e (enclave_ID_active r_val)) = enclave_state_valid e_state ->
    (forall e' E, e_state = enclave_state_value e' E -> (forall e_, NatMap.In e_ E ->
    exists index F V C R, NatMap.find index k = Some (single_level_cache F V C R) /\ NatMap.In e_ V)) ->
    <<k, mu, rho, e | i, q>> -->> <<k, mu, rho, e_state | nil, q, 1>>
| Exit: forall k mu rho e i q e',
    i = exit ->
    (active_enclave_update e enclave_ID_inactive) = enclave_state_valid e' ->
    <<k, mu, rho, e | i, q>> -->> <<k, mu, rho, e' | nil, q, 1>>
| BrTrue: forall k mu rho e i r r' q r_val pc_jump,
    i = br r r' ->
    (NatMap.find r rho) = Some (memory_value_data (data_value r_val)) ->
    r_val <> 0 ->
    (NatMap.find r' rho) = Some (memory_value_data (data_value pc_jump)) ->
    <<k, mu, rho, e | i, q>> -->> <<k, mu, rho, e | nil, q, pc_jump>>
| BrFalse: forall k mu rho e i r r' q r_val pc_jump,
    i = br r r' ->
    (NatMap.find r rho) = Some (memory_value_data (data_value r_val)) ->
    (eq r_val 0) ->
    <<k, mu, rho, e | i, q>> -->> <<k, mu, rho, e | nil, q, pc_jump>>
where "c1 -->> c2" := (single_process_sem c1 c2).

(* Runtime State and Observation Trace *)
Inductive semantic_state : Type :=
| state_and_trace: runtime_state -> process_explicit_observation_trace -> semantic_state.
Notation "'<<' k ',' m ',' r ',' p '|' obs '>>'" := (state_and_trace (runtime_state_value k m r p) obs).

(* Multi-process Operational Semantics *)
Reserved Notation "c1 '===>' c2" (at level 40).
Inductive multi_sem : semantic_state -> semantic_state -> Prop :=
| Multi: forall k mu rho pi e i obs_p obs q n k' mu' rho' e' l l' p,
    memory_read mu l = Some (memory_value_instruction i) ->
    <<k, mu, rho, e | i, q>> -->> <<k', mu', rho', e' | obs, q, n>> ->
    (NatMap.find p pi) = Some (process_value e l q) ->
    add_to_memory_address mu l n = Some l' ->
    (exists i', memory_read mu' l' = Some (memory_value_instruction i')) ->
    disjoint_enclave_states (runtime_state_value k mu rho pi) ->
    <<k, mu, rho, pi | obs_p>> ===> <<k', mu', rho', (NatMap.add p (process_value e' l' q) pi) | (obs_p ++ (to_p_trace p obs)) >>
| ContextSwitch : forall k mu rho pi q q' p e l obs,
    (NatMap.find p pi) = Some (process_value e l q) ->
    q <> q' ->
    (exists i, memory_read mu l = Some (memory_value_instruction i)) ->
    <<k, mu, rho, pi | obs>> ===> <<k, mu, rho, (NatMap.add p (process_value e l q') pi) | obs>>
where "c1 ===> c2" := (multi_sem c1 c2).