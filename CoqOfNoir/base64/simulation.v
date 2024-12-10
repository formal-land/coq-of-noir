Require Import CoqOfNoir.CoqOfNoir.
Require Import CoqOfNoir.proof.CoqOfNoir.
Require Import CoqOfNoir.simulation.CoqOfNoir.
Require CoqOfNoir.base64.polymorphic.

Import Run.

Module Base64EncodeBE.
  (*
  struct Base64EncodeBE {
      table: [u8; 64]
  }
  *)
  Record t : Set := {
    table : Array.t U8.t (U32.Build_t 64);
  }.

  Global Instance Impl_ToValue : ToValue.Trait t := {
    to_value (x : t) :=
      Value.Tuple [to_value x.(table)];
  }.

  Lemma rewrite_to_value (x : t) :
    Value.Tuple [to_value x.(table)] = to_value x.
  Proof. reflexivity. Qed.
  Global Hint Rewrite rewrite_to_value : to_value.

  Definition ascii_codes : list U8.t := List.map U8.Build_t [
    65; 66; 67; 68; 69; 70; 71; 72; 73; 74; 75; 76; 77; 78; 79; 80; 81; 82; 83; 84; 85; 86; 87; 88; 89; 90;
    97; 98; 99; 100; 101; 102; 103; 104; 105; 106; 107; 108; 109; 110; 111; 112; 113; 114; 115; 116; 117; 118; 119; 120; 121; 122;
    48; 49; 50; 51; 52; 53; 54; 55; 56; 57;
    43;
    47
  ].

  (*
  /// Creates a new encoder that uses the standard Base64 Alphabet (base64) specified in RFC 4648 
  /// (https://datatracker.ietf.org/doc/html/rfc4648#section-4)
  fn new() -> Self {
      Base64EncodeBE {
          // The alphabet values here are standard UTF-8 (and ASCII) byte encodings, so the index
          // in the table is the 6-bit Base64 value, and the value at that index is the UTF-8 
          // encoding of that value.
          table: [
              65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90,// 0-25 (A-Z)
              97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122,// 26-51 (a-z)
              48, 49, 50, 51, 52, 53, 54, 55, 56, 57,// 0-9
              43,// +
              47// /
          ]
      }
  }
  *)
  Definition new : t := {|
    table := Array.Build_t ascii_codes
  |}.

  Lemma run_new {State Address : Set} `{State.Trait State Address}
      (p : Z) (state : State) :
    {{ p, state ⏩
      polymorphic.Base64EncodeBE.new [] 🔽
      Result.Ok (to_value new)
    ⏩ state }}.
  Proof.
    unfold polymorphic.Base64EncodeBE.new, new.
    eapply Run.Let. {
      apply Run.Pure.
    }
    apply Run.Pure.
  Qed.
  Global Opaque new.

  (*
  fn get(self, idx: Field) -> u8 {
      self.table[idx]
  }
  *)
  Definition get (self : t) (idx : Field.t) : M! U8.t :=
    Array.read self.(table) idx.

  Lemma run_get {State Address : Set} `{State.Trait State Address}
      (p : Z) (state : State)
      (self : t) (idx : Field.t) :
    {{ p, state ⏩
      polymorphic.Base64EncodeBE.get [to_value self; to_value idx] 🔽
      Panic.to_result (get self idx)
    ⏩ state }}.
  Proof.
    unfold polymorphic.Base64EncodeBE.get, get, Array.read; cbn.
    rewrite List.nth_error_map.
    destruct List.nth_error; cbn; apply Run.Pure.
  Qed.
  Global Opaque get.

  (*
  (** How accessing the table of characters is used in practice *)
  Definition get_ascii_table (idx : Z) : Z :=
    List.nth_default 0 ascii_codes (Z.to_nat idx).

  Lemma get_ascii_table_eq (idx : Z)
      (H_idx : 0 <= idx < 64) :
    return! (U8.Build_t (get_ascii_table idx)) = get new (Field.Build_t idx).
  Proof.
    unfold get_ascii_table, ascii_codes; cbn.
    unfold List.nth_default.
    pose proof (List.nth_error_map U8.Build_t (Z.to_nat idx) ascii_codes) as H_eq.
    cbn in H_eq.
    rewrite H_eq.
    fold ascii_codes.
    clear H_eq.
    destruct List.nth_error eqn:?; cbn.
    { reflexivity. }
    { exfalso.
      apply (List.nth_error_Some ascii_codes (Z.to_nat idx)); trivial.
      cbn.
      lia.
    }
  Qed.

  Lemma run_get_ascii_table {State Address : Set} `{State.Trait State Address}
      (p : Z) (state : State)
      (idx : Z)
      (H_idx : 0 <= idx < 64) :
    {{ p, state ⏩
      polymorphic.Base64EncodeBE.get [to_value new; to_value (Field.Build_t idx)] 🔽
      Result.Ok (to_value (U8.Build_t (get_ascii_table idx)))
    ⏩ state }}.
  Proof.
    apply run_get.
    now rewrite get_ascii_table_eq.
  Qed.
  *)
End Base64EncodeBE.

Module base64_encode_elements.
  Module State.
    Record t : Set := {
      Base64Encoder : option Value.t;
      result : option Value.t;
    }.

    Definition init : t := {|
      Base64Encoder := None;
      result := None;
    |}.
  End State.

  Module Address.
    Inductive t : Set :=
    | Base64Encoder
    | result.
  End Address.

  Global Instance Impl_State : State.Trait State.t Address.t := {
    read state address :=
      match address with
      | Address.Base64Encoder => state.(State.Base64Encoder)
      | Address.result => state.(State.result)
      end;
    alloc_write state address value :=
      match address with
      | Address.Base64Encoder => Some (state <| State.Base64Encoder := Some value |>)
      | Address.result => Some (state <| State.result := Some value |>)
      end;
  }.

  Lemma IsStateValid : State.Valid.t Impl_State.
  Proof.
    sauto.
  Qed.
End base64_encode_elements.

Module State.
  Record t : Set := {
    base64_encode_elements : base64_encode_elements.State.t;
  }.

  Definition init : t := {|
    base64_encode_elements := base64_encode_elements.State.init;
  |}.
End State.

Module Address.
  Inductive t : Set :=
  | base64_encode_elements (address : base64_encode_elements.Address.t).
End Address.

Global Instance Impl_State : State.Trait State.t Address.t := {
  read state address :=
    match address with
    | Address.base64_encode_elements address =>
      State.read state.(State.base64_encode_elements) address
    end;
  alloc_write state address value :=
    match address with
    | Address.base64_encode_elements address =>
      match State.alloc_write state.(State.base64_encode_elements) address value with
      | Some base64_encode_elements =>
        Some (state <| State.base64_encode_elements := base64_encode_elements |>)
      | None => None
      end
    end;
}.

Lemma IsStateValid : State.Valid.t Impl_State.
Proof.
  sauto lq: on rew: off.
Qed.

(*
/**
 * @brief Take an array of ASCII values and convert into base64 values
 **/
pub fn base64_encode_elements<let InputElements: u32>(input: [u8; InputElements]) -> [u8; InputElements] {
    // for some reason, if the lookup table is not defined in a struct, access costs are expensive and ROM tables aren't being used :/
    let mut Base64Encoder = Base64EncodeBE::new();

    let mut result: [u8; InputElements] = [0; InputElements];

    for i in 0..InputElements {
        result[i] = Base64Encoder.get(input[i] as Field);
    }
    result
}
*)
Definition base64_encode_elements_for_init {InputElements : U32.t}
    (input : Array.t U8.t InputElements) :
    Array.t U8.t InputElements :=
  Array.repeat InputElements (U8.Build_t 0).

Definition base64_encode_elements_for_body (p : Z) {InputElements : U32.t}
    (input : Array.t U8.t InputElements) (i : Z) :
    MS! (Array.t U8.t InputElements) unit :=
  let i : U32.t := U32.Build_t i in
  letS! input_i := return!toS! (Array.read input i) in
  letS! input_i := return!toS! (cast_to_field p input_i) in
  letS! new_result_i :=
    return!toS! (Base64EncodeBE.get Base64EncodeBE.new input_i)in
  letS! result := readS! in
  letS! result := return!toS! (Array.write result i new_result_i) in
  writeS! result.

Definition base64_encode_elements (p : Z) {InputElements : U32.t}
    (input : Array.t U8.t InputElements) :
    M! (Array.t U8.t InputElements) * Array.t U8.t InputElements :=
  let Base64Encoder := Base64EncodeBE.new in

  (
    doS! (
      foldS!
        tt
        (List.map Z.of_nat (List.seq 0 (Z.to_nat (ToZ.to_Z InputElements))))
        (fun result i => base64_encode_elements_for_body p input i)
    ) in
    letS! result := readS! in
    returnS! result
  ) (base64_encode_elements_for_init input).

Lemma map_listUpdate_eq {A B : Type} (f : A -> B) (l : list A) (i : nat) (x : A) (y : B)
    (H_y : y = f x) :
  List.listUpdate (List.map f l) i y = List.map f (List.listUpdate l i x).
Proof.
  unfold List.listUpdate.
  rewrite List.firstn_map, List.skipn_map, List.map_app.
  sfirstorder.
Qed.

Lemma map_listUpdate_error_eq {A B : Type} (f : A -> B) (l : list A) (i : nat) (x : A) (y : B)
    (H_y : y = f x) :
  List.listUpdate_error (List.map f l) i y = option_map (List.map f) (List.listUpdate_error l i x).
Proof.
  unfold List.listUpdate_error.
  rewrite List.map_length.
  destruct (_ <? _)%nat; cbn; f_equal.
  now erewrite map_listUpdate_eq.
Qed.

Lemma run_base64_encode_elements
    (p : Z)
    {InputElements : U32.t}
    (input : Array.t U8.t InputElements)
    (H_InputElements : Integer.Valid.t InputElements)
    (H_input : Array.Valid.t input) :
  let output := base64_encode_elements p input in
  let state_end : State.t :=
    State.init <|
      State.base64_encode_elements := {|
        base64_encode_elements.State.Base64Encoder := Some (to_value Base64EncodeBE.new);
        base64_encode_elements.State.result := Some (to_value (snd output));
      |}
    |> in
    {{ p, State.init ⏩
      polymorphic.base64_encode_elements InputElements [to_value input] 🔽
      Panic.to_result (fst output)
    ⏩ state_end }}.
Proof.
  unfold polymorphic.base64_encode_elements, base64_encode_elements.
  eapply Run.Let. {
    eapply Run.CallClosure. {
      apply Base64EncodeBE.run_new.
    }
    eapply CallPrimitiveStateAlloc with (address :=
      Address.base64_encode_elements (base64_encode_elements.Address.Base64Encoder)
    );
      try reflexivity.
    apply Run.Pure.
  }
  eapply Run.Let. {
    eapply CallPrimitiveStateAlloc with (address :=
      Address.base64_encode_elements (base64_encode_elements.Address.result)
    );
      try reflexivity.
    apply Run.Pure.
  }
  fold @LowM.let_.
  eapply Run.Let. {
    eapply Run.For with
      (inject :=
        fun state accumulator =>
          state <| State.base64_encode_elements :=
            state.(State.base64_encode_elements) <|
              base64_encode_elements.State.result := Some (to_value accumulator)
            |>
          |>
      )
      (accumulator_in := base64_encode_elements_for_init input)
      (len := Z.to_nat InputElements.(U32.value))
      (body_expression := base64_encode_elements_for_body p input).
    2: {
      unfold set.
      repeat f_equal.
      cbn; f_equal.
      now rewrite List.map_repeat.
    }
    2: {
      reflexivity.
    }
    2: {
      unfold Integer.Valid.t in H_InputElements; cbn in *.
      f_equal.
      lia.
    }
    intros.
    eapply Run.CallPrimitiveStateRead; [reflexivity|].
    fold @LowM.let_.
    unfold set; cbn.
    unfold Array.read; cbn.
    rewrite List.nth_error_map.
    destruct List.nth_error as [result|]; cbn; [|apply Run.Pure].
    apply Run.CallPrimitiveGetFieldPrime.
    unfold cast_to_field; cbn.
    destruct (_ && _); cbn; [|apply Run.Pure].
    eapply Run.CallClosure. {
      autorewrite with to_value.
      match goal with
      | |- context[Value.Integer IntegerKind.Field ?i] =>
        change (Value.Integer IntegerKind.Field i) with (to_value (Field.Build_t i))
      end.
      apply Base64EncodeBE.run_get.
    }
    destruct Base64EncodeBE.get; cbn; [|apply Run.Pure].
    eapply Run.CallPrimitiveStateRead; [reflexivity|].
    unfold Array.write; cbn.
    rewrite List.nth_error_map.
    destruct List.nth_error as [unused|] eqn:H_nth_error; cbn.
    { clear H_nth_error unused.
      erewrite map_listUpdate_error_eq by reflexivity.
      unfold List.listUpdate_error.
      destruct (_ <? _)%nat; cbn; [|apply Run.Pure].
      eapply Run.CallPrimitiveStateWrite; [reflexivity|].
      unfold set; cbn.
      apply Run.Pure.
    }
    { assert (Datatypes.length accumulator_in.(Array.value) <= Z.to_nat i)%nat
         by hauto lq: on use: List.nth_error_None.
      unfold List.listUpdate_error.
      destruct (_ <? _)%nat eqn:?; [lia|].
      apply Run.Pure.
    }
  }
  fold @LowM.let_.
  unfold StatePanic.bind.
  destruct (foldS! _ _ _) as [status result].
  destruct status; cbn; [|apply Run.Pure].
  eapply Run.CallPrimitiveStateRead; [reflexivity|].
  apply Run.Pure.
Qed.

(* Lemma run_eq₂ {State Address : Set} `{State.Trait State Address}
    (state : State) (self other : Array.t U8.t 36) :
  {{ state |
    translation.eq₂ [to_value self; to_value other] 🔽
    Result.Ok (to_value (Eq.eq self other))
  ⏩ state }}.
Proof.
  unfold translation.eq₂. *)

(*
pub fn base64_encode<let InputBytes: u32, let OutputElements: u32>(input: [u8; InputBytes]) -> [u8; OutputElements] {
    // 240 bits fits 40 6-bit chunks and 30 8-bit chunks
    // we pack 40 base64 values into a field element and convert into 30 bytes
    // TODO: once we support arithmetic ops on generics, derive OutputBytes from InputBytes
    let mut result: [u8; OutputElements] = [0; OutputElements];
    let BASE64_ELEMENTS_PER_CHUNK: u32 = 40;
    let BYTES_PER_CHUNK: u32 = 30;
    let num_chunks = (InputBytes / BYTES_PER_CHUNK) + (InputBytes % BYTES_PER_CHUNK != 0) as u32;

    if num_chunks > 0 {
        for i in 0..num_chunks - 1 {
            let mut slice: Field = 0;
            for j in 0..BYTES_PER_CHUNK {
                slice *= 256;
                slice += input[i * BYTES_PER_CHUNK + j] as Field;
            }

            let slice_base64_chunks: [u8; 40] = slice.to_be_radix(64);
            for j in 0..BASE64_ELEMENTS_PER_CHUNK {
                result[i * BASE64_ELEMENTS_PER_CHUNK + j] = slice_base64_chunks[j];
            }
        }

        let bytes_in_final_chunk = InputBytes - ((num_chunks - 1) * BYTES_PER_CHUNK);

        let mut slice: Field = 0;
        for j in 0..bytes_in_final_chunk {
            slice *= 256;
            slice += input[(num_chunks - 1) * BYTES_PER_CHUNK + j] as Field;
        }
        for _ in bytes_in_final_chunk..BYTES_PER_CHUNK {
            slice *= 256;
        }

        // TODO: check is it cheaper to use a constant value in `to_be_bytes` or can we use `bytes_in_final_chunk`?
        let slice_base64_chunks: [u8; 40] = slice.to_be_radix(64);

        let num_elements_in_final_chunk = OutputElements - ((num_chunks - 1) * BASE64_ELEMENTS_PER_CHUNK);
        for i in 0..num_elements_in_final_chunk {
            result[(num_chunks - 1) * BASE64_ELEMENTS_PER_CHUNK + i] = slice_base64_chunks[i];
        }
        result = base64_encode_elements(result);
    }

    result
}
*)
(* Definition base64_encode {InputBytes OutputElements : U32.t} (input : Array.t U8.t InputBytes) :
    Array.t U8.t OutputElements :=
  let result : Array.t U8.t OutputElements := Array.repeat OutputElements (U8.Build_t 0) in
  let BASE64_ELEMENTS_PER_CHUNK : U32.t := U32.Build_t 40 in
  let BYTES_PER_CHUNK : U32.t := U32.Build_t 30 in
  let num_chunks : U32.t :=
    Integer.add
      (Integer.div InputBytes BYTES_PER_CHUNK)
      (Integer.of_bool (negb (Eq.eq (Integer.mod_ InputBytes BYTES_PER_CHUNK) (U32.Build_t 0)))) in

  if Integer.to_Z num_chunks >? 0 then
    M.for_ () *)
