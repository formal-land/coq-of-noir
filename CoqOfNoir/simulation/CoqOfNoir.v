Require Import CoqOfNoir.CoqOfNoir.

Module ToValue.
  Class Trait (Self : Set) : Set := {
    to_value : Self -> Value.t;
  }.
End ToValue.
Export ToValue.

Module Panic.
  Inductive t (A : Set) : Set :=
  | Success : A -> t A
  (** We put the payload on the parameter on a smart contructor, that is actually an opaque function
      that forgets about its parameter. *)
  | Error : t A.
  Arguments Success {_}.
  Arguments Error {_}.

  Definition to_result {A : Set} `{ToValue.Trait A} (value : t A) : Result.t :=
    match value with
    | Success value => Result.Ok (to_value value)
    | Error => Result.Panic
    end.

  (** For some intermediate results, we need to make an allocation to be like in the translated
      code *)
  Definition to_result_alloc {A : Set} `{ToValue.Trait A} (value : t A) : Result.t :=
    match value with
    | Success value => Result.Ok (M.alloc (to_value value))
    | Error => Result.Panic
    end.

  Definition return_ {A : Set} (value : A) : t A :=
    Success value.
  Arguments return_ /.

  Definition panic {A E : Set} (error : E) : t A :=
    Error.
  (* So that the error payload appears for debugging *)
  Opaque panic.

  Definition bind {A B : Set} (value : t A) (f : A -> t B) : t B :=
    match value with
    | Success value => f value
    | Error => Error
    end.

  Definition fold_left {A B : Set} (init : A) (l : list B) (f : A -> B -> t A) : t A :=
    List.fold_left (fun acc x => bind acc (fun acc => f acc x)) l (return_ init).
End Panic.

Module PanicNotations.
  Notation "M!" := Panic.t.

  Notation "return!" := Panic.return_.
  Notation "panic!" := Panic.panic.

  Notation "'let!' x ':=' X 'in' Y" :=
    (Panic.bind X (fun x => Y))
    (at level 200, x pattern, X at level 100, Y at level 200).

  Notation "'do!' X 'in' Y" :=
    (Panic.bind X (fun (_ : unit) => Y))
    (at level 200, X at level 100, Y at level 200).

  Notation "fold!" := Panic.fold_left.
End PanicNotations.

Module StatePanic.
  Definition t (State : Set) (A : Set) : Set :=
    State -> Panic.t A * State.

  Definition return_ {State A : Set} (value : A) : t State A :=
    fun state => (Panic.return_ value, state).

  Definition bind {State A B : Set} (value : t State A) (f : A -> t State B) : t State B :=
    fun state =>
      let '(output, state) := value state in
      match output with
      | Panic.Success value => f value state
      | Panic.Error => (Panic.Error, state)
      end.

  Fixpoint fold_left {State A B : Set}
      (init : A) (l : list B) (f : A -> B -> t State A) {struct l} :
      t State A :=
    match l with
    | [] => return_ init
    | x :: l => bind (f init x) (fun init => fold_left init l f)
    end.

  Definition lift_from_panic {State A : Set} (value : Panic.t A) : t State A :=
    fun state => (value, state).

  Definition read {State : Set} : t State State :=
    fun state => (Panic.return_ state, state).

  Definition write {State : Set} (state : State) : t State unit :=
    fun _ => (Panic.return_ tt, state).
End StatePanic.

Module StatePanicNotations.
  Notation "MS!" := StatePanic.t.

  Notation "returnS!" := StatePanic.return_.
  Notation "panic!" := Panic.panic.

  Notation "'letS!' x ':=' X 'in' Y" :=
    (StatePanic.bind X (fun x => Y))
    (at level 200, x pattern, X at level 100, Y at level 200).

  Notation "'doS!' X 'in' Y" :=
    (StatePanic.bind X (fun (_ : unit) => Y))
    (at level 200, X at level 100, Y at level 200).

  Notation "foldS!" := StatePanic.fold_left.

  Notation "return!toS!" := StatePanic.lift_from_panic.

  Notation "readS!" := StatePanic.read.

  Notation "writeS!" := StatePanic.write.
End StatePanicNotations.

Export PanicNotations.
Export StatePanicNotations.

Global Instance Impl_ToValue_for_unit : ToValue.Trait unit := {
  to_value (_ : unit) :=
    Value.Tuple [];
}.

Lemma rewrite_to_value_unit :
  Value.Tuple [] = to_value tt.
Proof. reflexivity. Qed.
Global Hint Rewrite rewrite_to_value_unit : to_value.

Global Instance Impl_ToValue_for_bool : ToValue.Trait bool := {
  to_value (b : bool) :=
    Value.Bool b;
}.

Lemma rewrite_to_value_bool :
  Value.Bool = to_value.
Proof. reflexivity. Qed.
Global Hint Rewrite rewrite_to_value_bool : to_value.

Module Field.
  Record t : Set := {
    value : Z;
  }.

  Global Instance Impl_ToValue : ToValue.Trait t := {
    to_value (i : t) :=
      Value.Integer IntegerKind.Field i.(value);
  }.

  Lemma rewrite_to_value :
    (fun i => Value.Integer IntegerKind.Field i.(value)) = to_value.
  Proof. reflexivity. Qed.
  Global Hint Rewrite rewrite_to_value : to_value.
End Field.

Module U1.
  Record t : Set := {
    value : Z;
  }.

  Global Instance Impl_ToValue : ToValue.Trait t := {
    to_value (i : t) :=
      Value.Integer IntegerKind.U1 i.(value);
  }.

  Lemma rewrite_to_value :
    (fun i => Value.Integer IntegerKind.U1 i.(value)) = to_value.
  Proof. reflexivity. Qed.
  Global Hint Rewrite rewrite_to_value : to_value.
End U1.

Module U8.
  Record t : Set := {
    value : Z;
  }.

  Global Instance Impl_ToValue : ToValue.Trait t := {
    to_value (i : t) :=
      Value.Integer IntegerKind.U8 i.(value);
  }.

  Lemma rewrite_to_value :
    (fun i => Value.Integer IntegerKind.U8 i.(value)) = to_value.
  Proof. reflexivity. Qed.
  Global Hint Rewrite rewrite_to_value : to_value.
End U8.

Module U16.
  Record t : Set := {
    value : Z;
  }.

  Global Instance Impl_ToValue : ToValue.Trait t := {
    to_value (i : t) :=
      Value.Integer IntegerKind.U16 i.(value);
  }.

  Lemma rewrite_to_value :
    (fun i => Value.Integer IntegerKind.U16 i.(value)) = to_value.
  Proof. reflexivity. Qed.
  Global Hint Rewrite rewrite_to_value : to_value.
End U16.

Module U32.
  Record t : Set := {
    value : Z;
  }.

  Global Instance Impl_ToValue : ToValue.Trait t := {
    to_value (i : t) :=
      Value.Integer IntegerKind.U32 i.(value);
  }.

  Lemma rewrite_to_value :
    (fun i => Value.Integer IntegerKind.U32 i.(value)) = to_value.
  Proof. reflexivity. Qed.
  Global Hint Rewrite rewrite_to_value : to_value.
End U32.

Module U64.
  Record t : Set := {
    value : Z;
  }.

  Global Instance Impl_ToValue : ToValue.Trait t := {
    to_value (i : t) :=
      Value.Integer IntegerKind.U64 i.(value);
  }.

  Lemma rewrite_to_value :
    (fun i => Value.Integer IntegerKind.U64 i.(value)) = to_value.
  Proof. reflexivity. Qed.
  Global Hint Rewrite rewrite_to_value : to_value.
End U64.

Module I1.
  Record t : Set := {
    value : Z;
  }.

  Global Instance Impl_ToValue : ToValue.Trait t := {
    to_value (i : t) :=
      Value.Integer IntegerKind.I1 i.(value);
  }.

  Lemma rewrite_to_value :
    (fun i => Value.Integer IntegerKind.I1 i.(value)) = to_value.
  Proof. reflexivity. Qed.
  Global Hint Rewrite rewrite_to_value : to_value.
End I1.

Module I8.
  Record t : Set := {
    value : Z;
  }.

  Global Instance Impl_ToValue : ToValue.Trait t := {
    to_value (i : t) :=
      Value.Integer IntegerKind.I8 i.(value);
  }.

  Lemma rewrite_to_value :
    (fun i => Value.Integer IntegerKind.I8 i.(value)) = to_value.
  Proof. reflexivity. Qed.
  Global Hint Rewrite rewrite_to_value : to_value.
End I8.

Module I16.
  Record t : Set := {
    value : Z;
  }.

  Global Instance Impl_ToValue : ToValue.Trait t := {
    to_value (i : t) :=
      Value.Integer IntegerKind.I16 i.(value);
  }.

  Lemma rewrite_to_value :
    (fun i => Value.Integer IntegerKind.I16 i.(value)) = to_value.
  Proof. reflexivity. Qed.
  Global Hint Rewrite rewrite_to_value : to_value.
End I16.

Module I32.
  Record t : Set := {
    value : Z;
  }.

  Global Instance Impl_ToValue : ToValue.Trait t := {
    to_value (i : t) :=
      Value.Integer IntegerKind.I32 i.(value);
  }.

  Lemma rewrite_to_value :
    (fun i => Value.Integer IntegerKind.I32 i.(value)) = to_value.
  Proof. reflexivity. Qed.
  Global Hint Rewrite rewrite_to_value : to_value.
End I32.

Module I64.
  Record t : Set := {
    value : Z;
  }.

  Global Instance Impl_ToValue : ToValue.Trait t := {
    to_value (i : t) :=
      Value.Integer IntegerKind.I64 i.(value);
  }.

  Lemma rewrite_to_value :
    (fun i => Value.Integer IntegerKind.I64 i.(value)) = to_value.
  Proof. reflexivity. Qed.
  Global Hint Rewrite rewrite_to_value : to_value.
End I64.

Module Integer.
  Class Trait (Self : Set) : Set := {
    to_Z : Self -> Z;
    of_Z : Z -> Self;
    min : Z;
    max : Z;
  }.

  Definition add {Self : Set} `{Trait Self} (self other : Self) : Self :=
    of_Z (Integer.to_Z self + Integer.to_Z other).

  Definition sub {Self : Set} `{Trait Self} (self other : Self) : Self :=
    of_Z (Integer.to_Z self - Integer.to_Z other).

  Definition mul {Self : Set} `{Trait Self} (self other : Self) : Self :=
    of_Z (Integer.to_Z self * Integer.to_Z other).

  Definition div {Self : Set} `{Trait Self} (self other : Self) : Self :=
    of_Z (Integer.to_Z self / Integer.to_Z other).

  Definition mod_ {Self : Set} `{Trait Self} (self other : Self) : Self :=
    of_Z (Integer.to_Z self mod Integer.to_Z other).

  Definition of_bool {Self : Set} `{Trait Self} (b : bool) : Self :=
    of_Z (if b then 1 else 0).
End Integer.

Global Instance Impl_Integer_for_U1 : Integer.Trait U1.t := {
  Integer.to_Z (i : U1.t) :=
    i.(U1.value);
  Integer.of_Z (i : Z) :=
    U1.Build_t (i mod (2^1));
  Integer.min := 0;
  Integer.max := 1;
}.

Global Instance Impl_Integer_for_U8 : Integer.Trait U8.t := {
  Integer.to_Z (i : U8.t) :=
    i.(U8.value);
  Integer.of_Z (i : Z) :=
    U8.Build_t (i mod (2^8));
  Integer.min := 0;
  Integer.max := 2^8 - 1;
}.

Global Instance Impl_Integer_for_U16 : Integer.Trait U16.t := {
  Integer.to_Z (i : U16.t) :=
    i.(U16.value);
  Integer.of_Z (i : Z) :=
    U16.Build_t (i mod (2^16));
  Integer.min := 0;
  Integer.max := 2^16 - 1;
}.

Global Instance Impl_Integer_for_U32 : Integer.Trait U32.t := {
  Integer.to_Z (i : U32.t) :=
    i.(U32.value);
  Integer.of_Z (i : Z) :=
    U32.Build_t (i mod (2^32));
  Integer.min := 0;
  Integer.max := 2^32 - 1;
}.

Global Instance Impl_Integer_for_U64 : Integer.Trait U64.t := {
  Integer.to_Z (i : U64.t) :=
    i.(U64.value);
  Integer.of_Z (i : Z) :=
    U64.Build_t (i mod (2^64));
  Integer.min := 0;
  Integer.max := 2^64 - 1;
}.

Global Instance Impl_Integer_for_I1 : Integer.Trait I1.t := {
  Integer.to_Z (i : I1.t) :=
    i.(I1.value);
  Integer.of_Z (i : Z) :=
    I1.Build_t (((i + 2^0) mod (2^1)) - 2^0);
  Integer.min := -1;
  Integer.max := 0;
}.

Global Instance Impl_Integer_for_I8 : Integer.Trait I8.t := {
  Integer.to_Z (i : I8.t) :=
    i.(I8.value);
  Integer.of_Z (i : Z) :=
    I8.Build_t (((i + 2^7) mod (2^8)) - 2^7);
  Integer.min := -2^7;
  Integer.max := 2^7 - 1;
}.

Global Instance Impl_Integer_for_I16 : Integer.Trait I16.t := {
  Integer.to_Z (i : I16.t) :=
    i.(I16.value);
  Integer.of_Z (i : Z) :=
    I16.Build_t (((i + 2^15) mod (2^16)) - 2^15);
  Integer.min := -2^15;
  Integer.max := 2^15 - 1;
}.

Global Instance Impl_Integer_for_I32 : Integer.Trait I32.t := {
  Integer.to_Z (i : I32.t) :=
    i.(I32.value);
  Integer.of_Z (i : Z) :=
    I32.Build_t (((i + 2^31) mod (2^32)) - 2^31);
  Integer.min := -2^31;
  Integer.max := 2^31 - 1;
}.

Global Instance Impl_Integer_for_I64 : Integer.Trait I64.t := {
  Integer.to_Z (i : I64.t) :=
    i.(I64.value);
  Integer.of_Z (i : Z) :=
    I64.Build_t (((i + 2^63) mod (2^64)) - 2^63);
  Integer.min := -2^63;
  Integer.max := 2^63 - 1;
}.

(** With this trait, we can take into account both standard integers and fields, whose size depends
    on a parameter [p]. *)
Module ToZ.
  Class Trait (Self : Set) : Set := {
    to_Z : Self -> Z;
  }.
End ToZ.

Global Instance Impl_ToZ_for_Field : ToZ.Trait Field.t := {
  ToZ.to_Z (i : Field.t) :=
    i.(Field.value);
}.

Global Instance Impl_ToZ_for_Integer {A : Set} `{Integer.Trait A} : ToZ.Trait A := {
  ToZ.to_Z (i : A) :=
    Integer.to_Z i;
}.

Module Array.
  (** We keep the [size] explicit even if this is not needed as we represent things with a list. We
      use it as a marker to guide the type-classes inference mechanism as this is done in Noir. *)
  Record t {A : Set} {size : U32.t} : Set := {
    value : list A;
  }.
  Arguments t : clear implicits.
  Arguments Build_t {_ _}.

  Global Instance Impl_ToValue {A : Set} `{ToValue.Trait A} {size : U32.t} :
      ToValue.Trait (t A size) := {
    to_value (array : t A size) :=
      Value.Array (List.map to_value array.(value));
  }.

  Lemma rewrite_to_value {A : Set} `{ToValue.Trait A} {size : U32.t} (array : t A size) :
    Value.Array (List.map to_value array.(value)) = to_value array.
  Proof. reflexivity. Qed.
  Global Hint Rewrite @rewrite_to_value : to_value.

  Definition repeat {A : Set} (size : U32.t) (value : A) : t A size :=
    {|
      value := List.repeat value (Z.to_nat (Integer.to_Z size))
    |}.

  Definition read {A Index: Set} `{ToZ.Trait Index} {size : U32.t}
      (array : t A size) (index : Index) :
      M! A :=
    match List.nth_error array.(value) (Z.to_nat (ToZ.to_Z index)) with
    | Some result => return! result
    | None => panic! ("Array.get: index out of bounds", array, index)
    end.

  Definition write {A Index: Set} `{ToZ.Trait Index} {size : U32.t}
      (array : t A size) (index : Index) (update : A) :
      M! (t A size) :=
    match List.listUpdate_error array.(value) (Z.to_nat (ToZ.to_Z index)) update with
    | Some array => return! (Build_t array)
    | None => panic! ("Array.write: index out of bounds", array, index)
    end.
End Array.

Module Eq.
  Class Trait (Self : Set) : Set := {
    eq : Self -> Self -> bool;
  }.
End Eq.

Global Instance Impl_Eq_for_Integer {A : Set} `{Integer.Trait A} : Eq.Trait A := {
  Eq.eq (self other : A) :=
    Integer.to_Z self =? Integer.to_Z other;
}.

Global Instance Impl_Eq_for_Array {A : Set} `{Eq.Trait A} {size : U32.t} :
    Eq.Trait (Array.t A size) := {
  Eq.eq (self other : Array.t A size) :=
    List.fold_left andb (List.zip Eq.eq self.(Array.value) other.(Array.value)) true;
}.

Definition cast_to_integer {A B : Set} `{ToZ.Trait A} `{Integer.Trait B} (value : A) : M! B :=
  let value := ToZ.to_Z value in
  if (Integer.min <=? value) && (value <=? Integer.max) then
    return! (Integer.of_Z value)
  else
    panic! ("cast: out of bounds", value).

Definition cast_to_field {A : Set} `{ToZ.Trait A} (p : Z) (value : A) : M! Field.t :=
  let value := ToZ.to_Z value in
  if (0 <=? value) && (value <? p) then
    return! (Field.Build_t value)
  else
    panic! ("cast: out of bounds", value).
