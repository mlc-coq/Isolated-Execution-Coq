Require Import RuntimeDefinitions.
From Coq Require Import Lists.List.
From Coq Require Import Bool.Bool.
From Coq Require Import Init.Nat.

(* Checks if raw_enclave_ID is in the memory range for enclave_state *)
Definition contains_enclave (l: enclave_memory_range) (id: raw_enclave_ID): bool :=
  match (NatMap.find id l) with
  | Some _ => true
  | None => false
  end.
Inductive validatable_enclave_state :=
  | enclave_state_valid: enclave_state -> validatable_enclave_state
  | enclave_state_error: validatable_enclave_state.

Definition data_equality (x: data) (y: data) :=
  match x, y with
  | data_value x1, data_value y1 => x1 =? y1
  | _, _ => false
  end.

(* Enclave Creation *)
Fixpoint is_all_zeroes (mu: memory) (block: block_ID) (offset: data_offset) (block_size: nat) (current_size: nat) {struct current_size} : bool :=
  match current_size with
  | 0 => true
  | S new_size =>
    match (NatMap.find block mu) with
    | None => false
    | Some l =>
      match (NatMap.find offset l) with
      | None => false
      | Some x =>
        match x with
        | memory_value_instruction _ => false
        | memory_value_data d =>
          match d with
          | data_none => false
          | data_value v =>
            match v with
            | S _ => false
            | 0 =>
              match ((S offset) =? block_size) with
              | true => is_all_zeroes mu (S block) 0 block_size new_size
              | false => is_all_zeroes mu block (S offset) block_size new_size
              end
            end
          end
        end
      end
    end
  end.
Definition add_new_enclave_to_enclave_state (state: enclave_state) (e: raw_enclave_ID) (l: memory_address) (n: number) : validatable_enclave_state :=
  match state with
  | enclave_state_value x mem_range =>
    match (NatMap.find e mem_range) with
    | Some _ => enclave_state_error
    | None => enclave_state_valid (enclave_state_value x (NatMap.add e (enclave_address_and_data l n) mem_range))
    end
  end.
Definition enclave_creation (state: enclave_state) (mu: memory) (e: raw_enclave_ID) (l: memory_address) (n: number): validatable_enclave_state :=
  match l with
  | address block offset =>
    match (NatMap.find block mu) with
    | Some x =>
      match (is_all_zeroes mu block offset (length (NatMapProperties.to_list x)) n) with
      | true => add_new_enclave_to_enclave_state state e l n
      | false => enclave_state_error
      end
    | None => enclave_state_error
    end
  end.

(* Active Enclave Update *)
Definition active_enclave_update (state: enclave_state) (id: enclave_ID): validatable_enclave_state :=
  match state with
  | enclave_state_value e mem_range =>
    match id with
    | enclave_ID_active x =>
      match (NatMap.find x mem_range) with
      | Some _ => enclave_state_valid (enclave_state_value id mem_range)
      | None => enclave_state_error
      end
    | enclave_ID_inactive => enclave_state_valid (enclave_state_value enclave_ID_inactive mem_range)
    end
  end.

(* Enclave Elimination *)
Definition enclave_elimination (state: enclave_state) (id: raw_enclave_ID): enclave_state :=
  match state with
  | enclave_state_value e memory_range => enclave_state_value e (NatMap.remove id memory_range)
  end.
