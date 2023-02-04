From Coq Require Import Init.Nat.
Require Import RuntimeDefinitions.

Fixpoint set_all_zeroes (mu: memory) (block: block_ID) (offset: data_offset) (block_size: nat) (current_size: nat) {struct current_size}: option memory :=
  match current_size with
  | 0 => Some mu
  | S new_size =>
    match (NatMap.find block mu) with
    | None => None
    | Some l =>
      match ((S offset) =? block_size) with
      | true => set_all_zeroes (NatMap.add block (NatMap.add offset (memory_value_data (data_value 0)) l) mu) (S block) 0 block_size new_size
      | false => set_all_zeroes (NatMap.add block (NatMap.add offset (memory_value_data (data_value 0)) l) mu) block (S offset) block_size new_size
      end
    end
  end.
Definition reinitialize_memory (e: raw_enclave_ID) (state: enclave_state) (mu: memory): option memory :=
  match state with
  | enclave_state_value _ E =>
    match (NatMap.find e E) with
    | None => None
    | Some mem_range =>
      match mem_range with
      | enclave_address_and_data l n =>
        match l with
        | address block offset =>
          match (NatMap.find block mu) with
          | None => None
          | Some x => set_all_zeroes mu block offset (length (NatMapProperties.to_list x)) n
          end
        end
      end
    end
  end.