Require Export Coq.Logic.FunctionalExtensionality.
Require Export Coq.Strings.Ascii.
Require Coq.Strings.HexString.
Require Export Coq.Strings.String.
Require Export Coq.ZArith.ZArith.
Require Coq.micromega.ZifyBool.
Require coqutil.Datatypes.List.
Require Export RecordUpdate.

Require Export Lia.
From Hammer Require Export Tactics.

(* Activate the modulo arithmetic in [lia] *)
Ltac Zify.zify_post_hook ::= Z.to_euclidean_division_equations.

Global Set Primitive Projections.
Global Set Printing Projections.
Global Open Scope char_scope.
Global Open Scope string_scope.
Global Open Scope list_scope.
Global Open Scope type_scope.
Global Open Scope Z_scope.
Global Open Scope bool_scope.

Export List.ListNotations.

Inductive sigS {A : Type} (P : A -> Set) : Set :=
| existS : forall (x : A), P x -> sigS P.
Arguments existS {_ _}.

Reserved Notation "{ x @ P }" (at level 0, x at level 99).
Reserved Notation "{ x : A @ P }" (at level 0, x at level 99).
Reserved Notation "{ ' pat : A @ P }"
  (at level 0, pat strict pattern, format "{ ' pat : A @ P }").

Notation "{ x @ P }" := (sigS (fun x => P)) : type_scope.
Notation "{ x : A @ P }" := (sigS (A := A) (fun x => P)) : type_scope.
Notation "{ ' pat : A @ P }" := (sigS (A := A) (fun pat => P)) : type_scope.

Module Pointer.
  Module Index.
    Inductive t : Set :=
    | Field (index : Z)
    | Index (index : Z).
  End Index.

  Module Path.
    Definition t : Set :=
      list Index.t.
  End Path.

  Module Mutable.
    Inductive t : Set :=
    | Make {Address : Set} (address : Address) (path : Path.t).
  End Mutable.

  Inductive t (Value : Set) : Set :=
  | Immediate (value : Value)
  | Mutable (mutable : Mutable.t).
  Arguments Immediate {_}.
  Arguments Mutable {_}.
End Pointer.

Module IntegerKind.
  Inductive t : Set :=
  | Field
  | U1
  | U8
  | U16
  | U32
  | U64
  | I1
  | I8
  | I16
  | I32
  | I64.
End IntegerKind.

Module Value.
  Inductive t : Set :=
  | Bool (b : bool)
  | Integer (kind : IntegerKind.t) (integer : Z)
  | String (s : string)
  | FmtStr : string -> Z -> t -> t
  | Pointer (pointer : Pointer.t t)
  | Array (values : list t)
  | Slice (values : list t)
  | Tuple (values : list t)
  | Closure : {'(Value, M) : (Set * Set) @ list Value -> M} -> t.

  Parameter fmt_str : string -> Z -> t -> t.

  (** Read the value at an index in a value. Useful to read sub-pointers. *)
  Definition read_index (value : t) (index : Pointer.Index.t) : option Value.t :=
    match index with
    | Pointer.Index.Field i =>
      match value with
      | Tuple values => List.nth_error values (Z.to_nat i)
      | _ => None
      end
    | Pointer.Index.Index i =>
      match value with
      | Array values => List.nth_error values (Z.to_nat i)
      | _ => None
      end
    end.

  Fixpoint read_path (value : t) (path : Pointer.Path.t) : option Value.t :=
    match path with
    | [] => Some value
    | index :: sub_path =>
      let sub_value := read_index value index in
      match sub_value with
      | Some sub_value => read_path sub_value sub_path
      | None => None
      end
    end.

  Definition write_index (value : t) (index : Pointer.Index.t) (update : Value.t) :
      option Value.t :=
    match index with
    | Pointer.Index.Field i =>
      match value with
      | Tuple values =>
        match List.listUpdate_error values (Z.to_nat i) update with
        | Some new_values => Some (Tuple new_values)
        | None => None
        end
      | _ => None
      end
    | Pointer.Index.Index i =>
      match value with
      | Array values =>
        match List.listUpdate_error values (Z.to_nat i) update with
        | Some new_values => Some (Array new_values)
        | None => None
        end
      | _ => None
      end
    end.

  Fixpoint write_path (value : t) (path : Pointer.Path.t) (update : Value.t) : option Value.t :=
    match path with
    | [] => Some update
    | index :: sub_path =>
      let sub_value := read_index value index in
      match sub_value with
      | Some sub_value =>
        match write_path sub_value sub_path update with
        | Some new_sub_value => write_index value index new_sub_value
        | None => None
        end
      | None => None
      end
    end.
End Value.

Module Primitive.
  Inductive t : Set -> Set :=
  | StateAlloc (value : Value.t) : t Value.t
  | StateRead {Address : Set} (address : Address) : t Value.t
  | StateWrite {Address : Set} (address : Address) (value : Value.t) : t unit
  | GetFieldPrime : t Z
  | IsEqual (value1 value2 : Value.t) : t bool.
End Primitive.

Module LowM.
  Inductive t (A : Set) : Set :=
  | Pure (value : A)
  | CallPrimitive {B : Set} (primitive : Primitive.t B) (k : B -> t A)
  | CallClosure (closure : Value.t) (args : list Value.t) (k : A -> t A)
  | Let (e : t A) (k : A -> t A)
  | Impossible (message : string).
  Arguments Pure {_}.
  Arguments CallPrimitive {_ _}.
  Arguments CallClosure {_}.
  Arguments Let {_}.
  Arguments Impossible {_}.

  Fixpoint let_ {A : Set} (e1 : t A) (e2 : A -> t A) : t A :=
    match e1 with
    | Pure v => e2 v
    | CallPrimitive primitive k =>
      CallPrimitive primitive (fun v => let_ (k v) e2)
    | CallClosure f args k =>
      CallClosure f args (fun v => let_ (k v) e2)
    | Let e k =>
      Let e (fun v => let_ (k v) e2)
    | Impossible message => Impossible message
    end.
End LowM.

Module Result.
  Inductive t : Set :=
  | Ok (value : Value.t)
  | Break
  | Continue
  | Panic.
End Result.

Module M.
  Definition t : Set :=
    LowM.t Result.t.

  Definition pure (value : Value.t) : M.t :=
    LowM.Pure (Result.Ok value).

  Definition let_ (e1 : M.t) (e2 : Value.t -> M.t) : M.t :=
    LowM.let_ e1 (fun v1 =>
    match v1 with
    | Result.Ok v1 => e2 v1
    | _ => LowM.Pure v1
    end).

  Definition let_strong (e1 : M.t) (e2 : Value.t -> M.t) : M.t :=
    LowM.Let e1 (fun v1 =>
    match v1 with
    | Result.Ok v1 => e2 v1
    | _ => LowM.Pure v1
    end).

  (** This parameter is used as a marker to allow a monadic notation
      without naming all intermediate results. Computation represented using
      this markers can be translated to a regular monadic computation using
      [M.monadic] tactic. *)
  Parameter run : M.t -> Value.t.

  Ltac monadic e :=
    lazymatch e with
    | context ctxt [let v := ?x in @?f v] =>
      refine (let_strong _ _);
        [ monadic x
        | let v' := fresh v in
          intro v';
          let y := (eval cbn beta in (f v')) in
          lazymatch context ctxt [let v := x in y] with
          | let _ := x in y => monadic y
          | _ =>
            refine (let_ _ _);
              [ monadic y
              | let w := fresh "v" in
                intro w;
                let z := context ctxt [w] in
                monadic z
              ]
          end
        ]
    | context ctxt [run ?x] =>
      lazymatch context ctxt [run x] with
      | run x => monadic x
      | _ =>
        refine (let_ _ _);
          [ monadic x
          | let v := fresh "v" in
            intro v;
            let y := context ctxt [v] in
            monadic y
          ]
      end
    | _ =>
      lazymatch type of e with
      | M.t => exact e
      | _ => exact (pure e)
      end
    end.

  Module Notations.
    Notation "'let-' a := b 'in' c" :=
      (LowM.let_ b (fun a => c))
        (at level 200, b at level 100, a name).

    Notation "'let*' a ':=' b 'in' c" :=
      (let_ b (fun a => c))
      (at level 200, a pattern, b at level 100, c at level 200).

    Notation "'let~' a := b 'in' c" :=
      (let_strong b (fun a => c))
        (at level 200, a pattern, b at level 100).

    Notation "'do~' a 'in' b" :=
      (let_strong a (fun _ => b))
      (at level 200).

    Notation "e (| e1 , .. , en |)" :=
      (run ((.. (e e1) ..) en))
      (at level 100).

    Notation "e (||)" :=
      (run e)
      (at level 100).

    Notation "[[ e ]]" :=
      (ltac:(M.monadic e))
      (* Use the version below for debugging and show errors that are made obscure by the tactic *)
      (* (M.pure e) *)
      (only parsing).
  End Notations.
  Import Notations.

  Definition call_closure (closure : Value.t) (args : list Value.t) : M.t :=
    LowM.CallClosure closure args LowM.Pure.

  Definition impossible (message : string) : M.t :=
    LowM.Impossible message.

  Definition panic {A : Set} (payload : A) : M.t :=
    LowM.Pure Result.Panic.
  (* We use the payload of this function for debugging but throw it away for the semantics *)
  Opaque panic.

  Definition alloc (value : Value.t) : Value.t :=
    Value.Pointer (Pointer.Immediate value).
  Arguments alloc /.

  Definition alloc_mutable (value : Value.t) : M.t :=
    LowM.CallPrimitive (Primitive.StateAlloc value) (fun value => pure value).
  Arguments alloc_mutable /.

  Definition read (r : Value.t) : M.t :=
    match r with
    | Value.Pointer pointer =>
      match pointer with
      | Pointer.Immediate value => pure value
      | Pointer.Mutable (Pointer.Mutable.Make address path) =>
        LowM.CallPrimitive (Primitive.StateRead address) (fun value =>
        match Value.read_path value path with
        | Some sub_value => pure sub_value
        | None => panic ("read: invalid sub-pointer", r)
        end)
      end
    | _ => impossible "read: expected a pointer"
    end.
  Arguments read /.

  Definition write (r update : Value.t) : M.t :=
    match r with
    | Value.Pointer (Pointer.Mutable (Pointer.Mutable.Make address path)) =>
      LowM.CallPrimitive (Primitive.StateRead address) (fun value =>
      match Value.write_path value path update with
      | Some new_value =>
        LowM.CallPrimitive (Primitive.StateWrite address new_value) (fun _ =>
        pure (Value.Tuple []))
      | None => panic ("write: invalid sub_pointer", r, update)
      end)
    | _ => impossible "write: expected a mutable pointer"
    end.
  Arguments write /.

  Definition copy (r : Value.t) : M.t :=
    let* v := read r in
    pure (alloc v).
  Arguments copy /.

  Definition copy_mutable (r : Value.t) : M.t :=
    let* v := read r in
    alloc_mutable v.
  Arguments copy /.

  Definition assert (condition : Value.t) (message : option Value.t) : M.t :=
    match condition with
    | Value.Bool b =>
      if b then
        pure (Value.Tuple [])
      else
        panic message
    | _ => LowM.Impossible "assert: expected a boolean"
    end.

  (** We only consider cast between integer values. We consider that the cast succeed if we are
      in the bounds of the target type. For casts to fields we need to retrieve the current
      field prime, which could change depending on the backend. *)
  Definition cast (value : Value.t) (integer_kind : IntegerKind.t) : M.t :=
    match value with
    | Value.Integer _ i =>
      match integer_kind with
      | IntegerKind.Field =>
        LowM.CallPrimitive Primitive.GetFieldPrime (fun p =>
        if (0 <=? i) && (i <? p) then
          pure (Value.Integer integer_kind i)
        else
          panic ("cast: out of bounds", value, integer_kind))
      | IntegerKind.U1 =>
        if (0 <=? i) && (i <? 2) then
          pure (Value.Integer integer_kind i)
        else
          panic ("cast: out of bounds", value, integer_kind)
      | IntegerKind.U8 =>
        if (0 <=? i) && (i <? 2^8) then
          pure (Value.Integer integer_kind i)
        else
          panic ("cast: out of bounds", value, integer_kind)
      | IntegerKind.U16 =>
        if (0 <=? i) && (i <? 2^16) then
          pure (Value.Integer integer_kind i)
        else
          panic ("cast: out of bounds", value, integer_kind)
      | IntegerKind.U32 =>
        if (0 <=? i) && (i <? 2^32) then
          pure (Value.Integer integer_kind i)
        else
          panic ("cast: out of bounds", value, integer_kind)
      | IntegerKind.U64 =>
        if (0 <=? i) && (i <? 2^64) then
          pure (Value.Integer integer_kind i)
        else
          panic ("cast: out of bounds", value, integer_kind)
      | IntegerKind.I1 =>
        if (-(2^0) <=? i) && (i <? 2^0) then
          pure (Value.Integer integer_kind i)
        else
          panic ("cast: out of bounds", value, integer_kind)
      | IntegerKind.I8 =>
        if (-(2^7) <=? i) && (i <? 2^7) then
          pure (Value.Integer integer_kind i)
        else
          panic ("cast: out of bounds", value, integer_kind)
      | IntegerKind.I16 =>
        if (-(2^15) <=? i) && (i <? 2^15) then
          pure (Value.Integer integer_kind i)
        else
          panic ("cast: out of bounds", value, integer_kind)
      | IntegerKind.I32 =>
        if (-(2^31) <=? i) && (i <? 2^31) then
          pure (Value.Integer integer_kind i)
        else
          panic ("cast: out of bounds", value, integer_kind)
      | IntegerKind.I64 =>
        if (-(2^63) <=? i) && (i <? 2^63) then
          pure (Value.Integer integer_kind i)
        else
          panic ("cast: out of bounds", value, integer_kind)
      end
    | _ => impossible "cast: expected an integer"
    end.

  Definition index (table idx : Value.t) : M.t :=
    match table with
    | Value.Pointer table_pointer =>
      match idx with
      | Value.Integer _ idx =>
        match table_pointer with
        | Pointer.Mutable (Pointer.Mutable.Make table_address path) =>
          pure (Value.Pointer (Pointer.Mutable (Pointer.Mutable.Make
            table_address
            (path ++ [Pointer.Index.Index idx])
          )))
        | Pointer.Immediate table_value =>
          match Value.read_index table_value (Pointer.Index.Index idx) with
          | Some value => pure (Value.Pointer (Pointer.Immediate value))
          | None => panic ("index: out of bounds", table, idx)
          end
        end
      | _ => impossible "index: expected an integer"
      end
    | _ => impossible "index: expected a pointer"
    end.

  Definition extract_tuple_field (tuple : Value.t) (field : Z) : M.t :=
    match tuple with
    | Value.Pointer tuple_pointer =>
      match tuple_pointer with
      | Pointer.Mutable (Pointer.Mutable.Make address path) =>
        pure (Value.Pointer (Pointer.Mutable (Pointer.Mutable.Make
          address
          (path ++ [Pointer.Index.Field field])
        )))
      | Pointer.Immediate tuple_value =>
        match Value.read_index tuple_value (Pointer.Index.Field field) with
        | Some value => pure (Value.Pointer (Pointer.Immediate value))
        | None => panic ("extract_tuple_field: out of bounds", tuple, field)
        end
      end
    | _ => impossible "extract_tuple_field: expected a pointer"
    end.

  Definition if_ (condition : Value.t) (then_ : M.t) (else_ : option M.t) : M.t :=
    match condition with
    | Value.Bool true => then_
    | Value.Bool false =>
      match else_ with
      | Some else_ => else_
      | None => pure (Value.Tuple [])
      end
    | _ => LowM.Impossible "if: expected a boolean"
    end.

  Fixpoint for_nat (end_ : Z) (fuel : nat) (body : Z -> M.t) {struct fuel} : M.t :=
    match fuel with
    | O => pure (alloc (Value.Tuple []))
    | S fuel' =>
      let* _ := body (end_ - Z.of_nat fuel) in
      for_nat end_ fuel' body
    end.

  Definition for_Z (start end_ : Z) (body : Z -> M.t) : M.t :=
    for_nat end_ (Z.to_nat (end_ - start)) body.

  Definition for_ (start end_ : Value.t) (body : Value.t -> M.t) : M.t :=
    match start, end_ with
    | Value.Integer integer_kind start, Value.Integer _ end_ =>
      (* We assume that the integer kind of the [end_] is the same and checked by the compiler. *)
      for_Z start end_ (fun i => body (alloc (Value.Integer integer_kind i)))
    | _, _ => impossible "for: expected integer values"
    end.
End M.

Export M.Notations.

Parameter get_function : forall (name : string) (id : Z), Value.t.

Definition closure (definition : list Value.t -> M.t) : Value.t :=
  Value.Closure (existS (Value.t, M.t) definition).

Module Builtin.
  Parameter __to_be_radix : Value.t.

  Parameter as_bytes : Value.t.

  Parameter assert_constant : Value.t.

  Parameter is_unconstrained : Value.t.

  Parameter len : Value.t.
End Builtin.

(*
pub enum UnaryOp {
    Minus,
    Not,
    MutableReference,
    Dereference {
        implicitly_added: bool,
    },
}
*)
Module Unary.
  Parameter minus : Value.t -> M.t.

  Parameter not : Value.t -> M.t.

  Parameter mutable_reference : Value.t -> M.t.

  Parameter dereference : Value.t -> M.t.
End Unary.

(*
pub enum BinaryOpKind {
    Add,
    Subtract,
    Multiply,
    Divide,
    Equal,
    NotEqual,
    Less,
    LessEqual,
    Greater,
    GreaterEqual,
    And,
    Or,
    Xor,
    ShiftRight,
    ShiftLeft,
    Modulo,
}
*)
Module Binary.
  Parameter add : Value.t -> Value.t -> M.t.

  Parameter subtract : Value.t -> Value.t -> M.t.

  Parameter multiply : Value.t -> Value.t -> M.t.

  Parameter divide : Value.t -> Value.t -> M.t.

  Definition equal (value1 value2 : Value.t) : M.t :=
    LowM.CallPrimitive (Primitive.IsEqual value1 value2) (fun b => M.pure (Value.Bool b)).

  Parameter not_equal : Value.t -> Value.t -> M.t.

  Parameter less : Value.t -> Value.t -> M.t.

  Parameter less_equal : Value.t -> Value.t -> M.t.

  Parameter greater : Value.t -> Value.t -> M.t.

  Parameter greater_equal : Value.t -> Value.t -> M.t.

  Parameter and_ : Value.t -> Value.t -> M.t.

  Parameter or_ : Value.t -> Value.t -> M.t.

  Parameter xor : Value.t -> Value.t -> M.t.

  Parameter shift_right : Value.t -> Value.t -> M.t.

  Parameter shift_left : Value.t -> Value.t -> M.t.

  Parameter modulo : Value.t -> Value.t -> M.t.
End Binary.
