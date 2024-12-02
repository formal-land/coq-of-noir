Require Import CoqOfNoir.CoqOfNoir.
Require Import CoqOfNoir.simulation.CoqOfNoir.


Module State.
  Class Trait (State Address : Set) : Type := {
    read : State -> Address -> option Value.t;
    alloc_write : State -> Address -> Value.t -> option State;
  }.
 
  Module Valid.
    (** A valid state should behave as map from address to optional values
        of the type given by the address. A value is [None] while not
        allocated, and [Some] once allocated. It is impossible to free
        allocated values. *)
    Record t `(Trait) : Prop := {
      (* [alloc_write] can only fail on new cells *)
      not_allocated (state : State) (address : Address) (value : Value.t) :
        match alloc_write state address value with
        | Some _ => True
        | None => read state address = None
        end;
      same (state : State) (address : Address) (value : Value.t) :
        match alloc_write state address value with
        | Some state => read state address = Some value
        | None => True
        end;
      different (state : State) (address1 address2 : Address) (value2 : Value.t) :
        address1 <> address2 ->
        match alloc_write state address2 value2 with
        | Some state' => read state' address1 = read state address1
        | None => True
        end;
        }.
  End Valid.
End State.

Module Run.
  Reserved Notation "{{ p , state_in | e ⇓ output | state_out }}".

  Inductive t {State Address : Set} `{State.Trait State Address}
      (p : Z) (output : Result.t) (state_out : State) :
      State -> M.t -> Prop :=
  | Pure :
    (* This should be the only case where the input and output states are the same. *)
    {{ p, state_out | LowM.Pure output ⇓ output | state_out }}
  | CallPrimitiveStateAlloc
      (value : Value.t)
      (address : Address)
      (k : Value.t -> M.t)
      (state_in state_in' : State) :
    let pointer := Pointer.Mutable (Pointer.Mutable.Make address []) in
    State.read state_in address = None ->
    State.alloc_write state_in address value = Some state_in' ->
    {{ p, state_in' | k (Value.Pointer pointer) ⇓ output | state_out }} ->
    {{ p, state_in | LowM.CallPrimitive (Primitive.StateAlloc value) k ⇓ output | state_out }}
  | CallPrimitiveStateRead
      (address : Address)
      (value : Value.t)
      (k : Value.t -> M.t)
      (state_in : State) :
    State.read state_in address = Some value ->
    {{ p, state_in | k value ⇓ output | state_out }} ->
    {{ p, state_in | LowM.CallPrimitive (Primitive.StateRead address) k ⇓ output | state_out }}
  | CallPrimitiveStateWrite
      (value : Value.t)
      (address : Address)
      (k : unit -> M.t)
      (state_in state_in' : State) :
    State.alloc_write state_in address value = Some state_in' ->
    {{ p, state_in' | k tt ⇓ output | state_out }} ->
    {{ p, state_in |
      LowM.CallPrimitive (Primitive.StateWrite address value) k ⇓ output
    | state_out }}
  | CallPrimitiveGetFieldPrime
      (k : Z -> M.t)
      (state_in : State) :
    {{ p, state_in | k p ⇓ output | state_out }} ->
    {{ p, state_in |
      LowM.CallPrimitive Primitive.GetFieldPrime k ⇓ output
    | state_out }}
  | CallPrimitiveIsEqualTrue
      (value1 value2 : Value.t)
      (k : bool -> M.t)
      (state_in : State) :
    (* The hypothesis of equality is explicit as this should be more convenient for the proofs *)
    value1 = value2 ->
    {{ p, state_in | k true ⇓ output | state_out }} ->
    {{ p, state_in | LowM.CallPrimitive (Primitive.IsEqual value1 value2) k ⇓ output | state_out }}
  | CallPrimitiveIsEqualFalse
      (value1 value2 : Value.t)
      (k : bool -> M.t)
      (state_in : State) :
    value1 <> value2 ->
    {{ p, state_in | k false ⇓ output | state_out }} ->
    {{ p, state_in | LowM.CallPrimitive (Primitive.IsEqual value1 value2) k ⇓ output | state_out }}
  | CallClosure
      (f : list Value.t -> M.t) (args : list Value.t)
      (k : Result.t -> M.t)
      (output_inter : Result.t)
      (state_in state_inter : State) :
    let closure := Value.Closure (existS (_, _) f) in
    {{ p, state_in | f args ⇓ output_inter | state_inter }} ->
    {{ p, state_inter | k output_inter ⇓ output | state_out }} ->
    {{ p, state_in | LowM.CallClosure closure args k ⇓ output | state_out }}
  | Let
      (e : M.t)
      (k : Result.t -> M.t)
      (output_inter : Result.t)
      (state_in state_inter : State) :
    {{ p, state_in | e ⇓ output_inter | state_inter }} ->
    {{ p, state_inter | k output_inter ⇓ output | state_out }} ->
    {{ p, state_in | LowM.Let e k ⇓ output | state_out }}
  | LetUnfold
      (e : M.t)
      (k : Result.t -> M.t)
      (state_in : State) :
    {{ p, state_in | LowM.let_ e k ⇓ output | state_out }} ->
    {{ p, state_in | LowM.Let e k ⇓ output | state_out }}
  | LetUnUnfold
      (e : M.t)
      (k : Result.t -> M.t)
      (state_in : State) :
    {{ p, state_in | LowM.Let e k ⇓ output | state_out }} ->
    {{ p, state_in | LowM.let_ e k ⇓ output | state_out }}

  where "{{ p , state_in | e ⇓ output | state_out }}" :=
    (t p output state_out state_in e).

  Lemma PureEq {State Address : Set} `{State.Trait State Address}
      (p : Z) (output output' : Result.t) (state state' : State) :
    output = output' ->
    state = state' ->
    {{ p, state | LowM.Pure output ⇓ output' | state' }}.
  Proof.
    intros -> ->.
    apply Pure.
  Qed.

  Lemma For {State Address : Set} `{State.Trait State Address}
      (p : Z) (state_in : State)
      (integer_kind : IntegerKind.t) (start : Z) (len : nat) (body : Value.t -> M.t)
      {Accumulator : Set}
      (inject : State -> Accumulator -> State)
      (accumulator_in : Accumulator)
      (body_expression : Z -> MS! Accumulator unit)
      (H_body : forall (accumulator_in : Accumulator) (i : Z),
        let output_accumulator_out := body_expression i accumulator_in in
        {{ p, inject state_in accumulator_in |
          body (M.alloc (Value.Integer integer_kind i)) ⇓
          Panic.to_result (fst output_accumulator_out)
        | inject state_in (snd output_accumulator_out) }}
      ) :
    let output_accumulator_out :=
      foldS!
        tt
        (List.map (fun offset => start + Z.of_nat offset) (List.seq 0 len))
        (fun (_ : unit) => body_expression)
        accumulator_in in
    {{ p, inject state_in accumulator_in |
      M.for_
        (Value.Integer integer_kind start)
        (Value.Integer integer_kind (start + Z.of_nat len))
        body ⇓
      Panic.to_result (fst output_accumulator_out)
    | inject state_in (snd output_accumulator_out) }}.
  Proof.
    revert start accumulator_in.
    induction len as [| len IHlen]; intros; unfold M.for_, M.for_Z in *; simpl in *.
    { replace (start + 0) with start by lia.
      replace (start - start) with 0 by lia.
      apply Pure.
    }
    { replace (Z.to_nat (start + _ - start)) with (S len) by lia.
      simpl.
      apply LetUnUnfold.
      eapply Let. {
        apply H_body.
      }
      replace (start + _ - _) with start by lia.
      unfold output_accumulator_out.
      replace (start + 0) with start by lia.
      unfold StatePanic.bind.
      destruct body_expression as [output accumulator_out]; simpl.
      destruct output as [ [] |]; simpl.
      { replace (start + Z.pos _) with (start + 1 + Z.of_nat len) by lia.
        pose proof (IHlen (start + 1) accumulator_out) as IHlen'.
        replace ((start + 1) + _ - (start + 1)) with (Z.of_nat len) in IHlen' by lia.
        replace (Z.to_nat (Z.of_nat len)) with len in IHlen' by lia.
        assert (H_map_seq_one :
          List.map (fun offset : nat => start + Z.of_nat offset) (List.seq 1 len) =
          List.map (fun offset : nat => start + 1 + Z.of_nat offset) (List.seq 0 len)
        ). {
          clear.
          generalize 0%nat as n.
          induction len; simpl; [reflexivity|]; intros.
          rewrite <- IHlen.
          f_equal.
          lia.
        }
        rewrite <- H_map_seq_one in IHlen'.
        apply IHlen'.
      }
      { apply Run.Pure. }
    }
  Qed.
End Run.

Module Singleton.
  Module State.
    Definition t : Set := option Value.t.
  End State.

  Module Address.
    Definition t : Set := unit.
  End Address.

  Global Instance IsState : State.Trait State.t Address.t := {
    read state _ := state;
    alloc_write state _ value := Some (Some value);
  }.

  Lemma IsStateValid : State.Valid.t IsState.
  Proof.
    sauto lq: on rew: off.
  Qed.
End Singleton.
