Require Import CoqOfNoir.CoqOfNoir.

(*
  fn encode_and_decode$f0() -> () {
      let input$0 = The quick brown fox jumps over the lazy dog, while 42 ravens perch atop a rusty mailbox.;
      let base64_encoded$1 = VGhlIHF1aWNrIGJyb3duIGZveCBqdW1wcyBvdmVyIHRoZSBsYXp5IGRvZywgd2hpbGUgNDIgcmF2ZW5zIHBlcmNoIGF0b3AgYSBydXN0eSBtYWlsYm94Lg;
      let encoded$2 = base64_encode$f1(as_bytes$str_as_bytes(input$l0));
      constrain eq$f2(encoded$l2, as_bytes$str_as_bytes(base64_encoded$l1));
      let decoded$3 = base64_decode$f3(encoded$l2);
      constrain eq$f4(decoded$l3, as_bytes$str_as_bytes(input$l0))
  }
*)
Definition encode_and_decode₀ (α : list Value.t) : M.t :=
  match α with
  | [] =>
    let* result :=
      let~ input := [[ M.copy (|
        M.alloc (Value.String "The quick brown fox jumps over the lazy dog, while 42 ravens perch atop a rusty mailbox.")
      |) ]] in
      let~ base64_encoded := [[ M.copy (|
        M.alloc (Value.String "VGhlIHF1aWNrIGJyb3duIGZveCBqdW1wcyBvdmVyIHRoZSBsYXp5IGRvZywgd2hpbGUgNDIgcmF2ZW5zIHBlcmNoIGF0b3AgYSBydXN0eSBtYWlsYm94Lg")
      |) ]] in
      let~ encoded := [[ M.copy (|
        M.alloc (M.call_closure (|
          get_function "base64_encode" 1,
          [
            M.call_closure (|
              M.read (| Builtin.as_bytes |),
              [
                M.read (| input |)
              ]
            |)
          ]
        |))
      |) ]] in
      do~ [[
        M.alloc (M.assert (|
          M.call_closure (|
            get_function "eq" 2,
            [
              M.read (| encoded |);
              M.call_closure (|
                M.read (| Builtin.as_bytes |),
                [
                  M.read (| base64_encoded |)
                ]
              |)
            ]
          |),
          None
        |))
      ]] in
      let~ decoded := [[ M.copy (|
        M.alloc (M.call_closure (|
          get_function "base64_decode" 3,
          [
            M.read (| encoded |)
          ]
        |))
      |) ]] in
      [[
        M.alloc (M.assert (|
          M.call_closure (|
            get_function "eq" 4,
            [
              M.read (| decoded |);
              M.call_closure (|
                M.read (| Builtin.as_bytes |),
                [
                  M.read (| input |)
                ]
              |)
            ]
          |),
          None
        |))
      ]] in
    M.read result
  | _ => M.impossible "wrong number of arguments"
  end.

Axiom get_function_encode_and_decode₀ :
  get_function "encode_and_decode" 0 =
  closure encode_and_decode₀.
Global Hint Rewrite get_function_encode_and_decode₀ : get_function.

(*
  fn base64_encode$f1(input$l4: [u8; 88]) -> [u8; 118] {
      let result$5 = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
      let BASE64_ELEMENTS_PER_CHUNK$6 = 40;
      let BYTES_PER_CHUNK$7 = 30;
      let num_chunks$8 = ((88 / BYTES_PER_CHUNK$l7) + (((88 % BYTES_PER_CHUNK$l7) != 0) as u32));
      if (num_chunks$l8 > 0) {
          for i$9 in 0 .. (num_chunks$l8 - 1) {
              let slice$10 = 0;
              for j$11 in 0 .. BYTES_PER_CHUNK$l7 {
                  slice$l10 = (slice$l10 * 2⁸);
                  slice$l10 = (slice$l10 + (input$l4[((i$l9 * BYTES_PER_CHUNK$l7) + j$l11)] as Field))
              };
              let slice_base64_chunks$12 = to_be_radix$f5(slice$l10, 2⁶);
              for j$13 in 0 .. BASE64_ELEMENTS_PER_CHUNK$l6 {
                  result$l5[((i$l9 * BASE64_ELEMENTS_PER_CHUNK$l6) + j$l13)] = slice_base64_chunks$l12[j$l13]
              }
          };
          let bytes_in_final_chunk$14 = (88 - ((num_chunks$l8 - 1) * BYTES_PER_CHUNK$l7));
          let slice$15 = 0;
          for j$16 in 0 .. bytes_in_final_chunk$l14 {
              slice$l15 = (slice$l15 * 2⁸);
              slice$l15 = (slice$l15 + (input$l4[(((num_chunks$l8 - 1) * BYTES_PER_CHUNK$l7) + j$l16)] as Field))
          };
          for _$17 in bytes_in_final_chunk$l14 .. BYTES_PER_CHUNK$l7 {
              slice$l15 = (slice$l15 * 2⁸)
          };
          let slice_base64_chunks$18 = to_be_radix$f5(slice$l15, 2⁶);
          let num_elements_in_final_chunk$19 = (118 - ((num_chunks$l8 - 1) * BASE64_ELEMENTS_PER_CHUNK$l6));
          for i$20 in 0 .. num_elements_in_final_chunk$l19 {
              result$l5[(((num_chunks$l8 - 1) * BASE64_ELEMENTS_PER_CHUNK$l6) + i$l20)] = slice_base64_chunks$l18[i$l20]
          };
          result$l5 = base64_encode_elements$f6(result$l5)
      };
      result$l5
  }
*)
Definition base64_encode₁ (α : list Value.t) : M.t :=
  match α with
  | [input] =>
    let input := M.alloc input in
    let* result :=
      let~ result := [[ M.copy_mutable (|
        M.alloc (Value.Array [
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0
        ])
      |) ]] in
      let~ BASE64_ELEMENTS_PER_CHUNK := [[ M.copy (|
        M.alloc (Value.Integer IntegerKind.U32 40)
      |) ]] in
      let~ BYTES_PER_CHUNK := [[ M.copy (|
        M.alloc (Value.Integer IntegerKind.U32 30)
      |) ]] in
      let~ num_chunks := [[ M.copy (|
        M.alloc (Binary.add (|
          Binary.divide (|
            Value.Integer IntegerKind.U32 88,
            M.read (| BYTES_PER_CHUNK |)
          |),
          M.cast (|
            Binary.not_equal (|
              Binary.modulo (|
                Value.Integer IntegerKind.U32 88,
                M.read (| BYTES_PER_CHUNK |)
              |),
              Value.Integer IntegerKind.U32 0
            |),
            IntegerKind.U32
          |)
        |))
      |) ]] in
      do~ [[
        M.if_ (|
          Binary.greater (|
            M.read (| num_chunks |),
            Value.Integer IntegerKind.U32 0
          |),
          do~ [[
            M.for_ (|
              Value.Integer IntegerKind.U32 0,
              Binary.subtract (|
                M.read (| num_chunks |),
                Value.Integer IntegerKind.U32 1
              |),
              fun (i : Value.t) =>
              let~ slice := [[ M.copy_mutable (|
                M.alloc (Value.Integer IntegerKind.Field 0)
              |) ]] in
              do~ [[
                M.for_ (|
                  Value.Integer IntegerKind.U32 0,
                  M.read (| BYTES_PER_CHUNK |),
                  fun (j : Value.t) =>
                  do~ [[
                    M.alloc (M.write (|
                      slice,
                      Binary.multiply (|
                        M.read (| slice |),
                        Value.Integer IntegerKind.Field 256
                      |)
                    |))
                  ]] in
                  [[
                    M.alloc (M.write (|
                      slice,
                      Binary.add (|
                        M.read (| slice |),
                        M.cast (|
                          M.read (| M.index (|
                            input,
                            Binary.add (|
                              Binary.multiply (|
                                M.read (| i |),
                                M.read (| BYTES_PER_CHUNK |)
                              |),
                              M.read (| j |)
                            |)
                          |) |),
                          IntegerKind.Field
                        |)
                      |)
                    |))
                  ]]
                |)
              ]] in
              let~ slice_base64_chunks := [[ M.copy (|
                M.alloc (M.call_closure (|
                  get_function "to_be_radix" 5,
                  [
                    M.read (| slice |);
                    Value.Integer IntegerKind.U32 64
                  ]
                |))
              |) ]] in
              [[
                M.for_ (|
                  Value.Integer IntegerKind.U32 0,
                  M.read (| BASE64_ELEMENTS_PER_CHUNK |),
                  fun (j : Value.t) =>
                  [[
                    M.alloc (M.write (|
                      M.index (|
                        result,
                        Binary.add (|
                          Binary.multiply (|
                            M.read (| i |),
                            M.read (| BASE64_ELEMENTS_PER_CHUNK |)
                          |),
                          M.read (| j |)
                        |)
                      |),
                      M.read (| M.index (|
                        slice_base64_chunks,
                        M.read (| j |)
                      |) |)
                    |))
                  ]]
                |)
              ]]
            |)
          ]] in
          let~ bytes_in_final_chunk := [[ M.copy (|
            M.alloc (Binary.subtract (|
              Value.Integer IntegerKind.U32 88,
              Binary.multiply (|
                Binary.subtract (|
                  M.read (| num_chunks |),
                  Value.Integer IntegerKind.U32 1
                |),
                M.read (| BYTES_PER_CHUNK |)
              |)
            |))
          |) ]] in
          let~ slice := [[ M.copy_mutable (|
            M.alloc (Value.Integer IntegerKind.Field 0)
          |) ]] in
          do~ [[
            M.for_ (|
              Value.Integer IntegerKind.U32 0,
              M.read (| bytes_in_final_chunk |),
              fun (j : Value.t) =>
              do~ [[
                M.alloc (M.write (|
                  slice,
                  Binary.multiply (|
                    M.read (| slice |),
                    Value.Integer IntegerKind.Field 256
                  |)
                |))
              ]] in
              [[
                M.alloc (M.write (|
                  slice,
                  Binary.add (|
                    M.read (| slice |),
                    M.cast (|
                      M.read (| M.index (|
                        input,
                        Binary.add (|
                          Binary.multiply (|
                            Binary.subtract (|
                              M.read (| num_chunks |),
                              Value.Integer IntegerKind.U32 1
                            |),
                            M.read (| BYTES_PER_CHUNK |)
                          |),
                          M.read (| j |)
                        |)
                      |) |),
                      IntegerKind.Field
                    |)
                  |)
                |))
              ]]
            |)
          ]] in
          do~ [[
            M.for_ (|
              M.read (| bytes_in_final_chunk |),
              M.read (| BYTES_PER_CHUNK |),
              fun (_ : Value.t) =>
              [[
                M.alloc (M.write (|
                  slice,
                  Binary.multiply (|
                    M.read (| slice |),
                    Value.Integer IntegerKind.Field 256
                  |)
                |))
              ]]
            |)
          ]] in
          let~ slice_base64_chunks := [[ M.copy (|
            M.alloc (M.call_closure (|
              get_function "to_be_radix" 5,
              [
                M.read (| slice |);
                Value.Integer IntegerKind.U32 64
              ]
            |))
          |) ]] in
          let~ num_elements_in_final_chunk := [[ M.copy (|
            M.alloc (Binary.subtract (|
              Value.Integer IntegerKind.U32 118,
              Binary.multiply (|
                Binary.subtract (|
                  M.read (| num_chunks |),
                  Value.Integer IntegerKind.U32 1
                |),
                M.read (| BASE64_ELEMENTS_PER_CHUNK |)
              |)
            |))
          |) ]] in
          do~ [[
            M.for_ (|
              Value.Integer IntegerKind.U32 0,
              M.read (| num_elements_in_final_chunk |),
              fun (i : Value.t) =>
              [[
                M.alloc (M.write (|
                  M.index (|
                    result,
                    Binary.add (|
                      Binary.multiply (|
                        Binary.subtract (|
                          M.read (| num_chunks |),
                          Value.Integer IntegerKind.U32 1
                        |),
                        M.read (| BASE64_ELEMENTS_PER_CHUNK |)
                      |),
                      M.read (| i |)
                    |)
                  |),
                  M.read (| M.index (|
                    slice_base64_chunks,
                    M.read (| i |)
                  |) |)
                |))
              ]]
            |)
          ]] in
          [[
            M.alloc (M.write (|
              result,
              M.call_closure (|
                get_function "base64_encode_elements" 6,
                [
                  M.read (| result |)
                ]
              |)
            |))
          ]],
          None
        |)
      ]] in
      [[
        result
      ]] in
    M.read result
  | _ => M.impossible "wrong number of arguments"
  end.

Axiom get_function_base64_encode₁ :
  get_function "base64_encode" 1 =
  closure base64_encode₁.
Global Hint Rewrite get_function_base64_encode₁ : get_function.

(*
  fn eq$f2(self$l21: [u8; 118], other$l22: [u8; 118]) -> bool {
      let result$23 = true;
      for i$24 in 0 .. len$array_len(self$l21) {
          result$l23 = (result$l23 & eq$f7(self$l21[i$l24], other$l22[i$l24]))
      };
      result$l23
  }
*)
Definition eq₂ (α : list Value.t) : M.t :=
  match α with
  | [self; other] =>
    let self := M.alloc self in
    let other := M.alloc other in
    let* result :=
      let~ result := [[ M.copy_mutable (|
        M.alloc (Value.Bool true)
      |) ]] in
      do~ [[
        M.for_ (|
          Value.Integer IntegerKind.U32 0,
          M.call_closure (|
            M.read (| Builtin.len |),
            [
              M.read (| self |)
            ]
          |),
          fun (i : Value.t) =>
          [[
            M.alloc (M.write (|
              result,
              Binary.and_ (|
                M.read (| result |),
                M.call_closure (|
                  get_function "eq" 7,
                  [
                    M.read (| M.index (|
                      self,
                      M.read (| i |)
                    |) |);
                    M.read (| M.index (|
                      other,
                      M.read (| i |)
                    |) |)
                  ]
                |)
              |)
            |))
          ]]
        |)
      ]] in
      [[
        result
      ]] in
    M.read result
  | _ => M.impossible "wrong number of arguments"
  end.

Axiom get_function_eq₂ :
  get_function "eq" 2 =
  closure eq₂.
Global Hint Rewrite get_function_eq₂ : get_function.

(*
  fn base64_decode$f3(input$l25: [u8; 118]) -> [u8; 88] {
      let decoded$26 = base64_decode_elements$f8(input$l25);
      let result$27 = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
      let BASE64_ELEMENTS_PER_CHUNK$28 = 40;
      let BYTES_PER_CHUNK$29 = 30;
      let num_chunks$30 = ((118 / BASE64_ELEMENTS_PER_CHUNK$l28) + (((118 % BASE64_ELEMENTS_PER_CHUNK$l28) != 0) as u32));
      if (num_chunks$l30 > 0) {
          for i$31 in 0 .. (num_chunks$l30 - 1) {
              let slice$32 = 0;
              for j$33 in 0 .. BASE64_ELEMENTS_PER_CHUNK$l28 {
                  slice$l32 = (slice$l32 * 2⁶);
                  slice$l32 = (slice$l32 + (decoded$l26[((i$l31 * BASE64_ELEMENTS_PER_CHUNK$l28) + j$l33)] as Field))
              };
              let slice_bytes$34 = to_be_bytes$f9(slice$l32);
              for j$35 in 0 .. BYTES_PER_CHUNK$l29 {
                  result$l27[((i$l31 * BYTES_PER_CHUNK$l29) + j$l35)] = slice_bytes$l34[j$l35]
              }
          };
          let base64_elements_in_final_chunk$36 = (118 - ((num_chunks$l30 - 1) * BASE64_ELEMENTS_PER_CHUNK$l28));
          let slice$37 = 0;
          for j$38 in 0 .. base64_elements_in_final_chunk$l36 {
              slice$l37 = (slice$l37 * 2⁶);
              slice$l37 = (slice$l37 + (decoded$l26[(((num_chunks$l30 - 1) * BASE64_ELEMENTS_PER_CHUNK$l28) + j$l38)] as Field))
          };
          for _$39 in base64_elements_in_final_chunk$l36 .. BASE64_ELEMENTS_PER_CHUNK$l28 {
              slice$l37 = (slice$l37 * 2⁶)
          };
          let slice_bytes$40 = to_be_bytes$f9(slice$l37);
          let num_bytes_in_final_chunk$41 = (88 - ((num_chunks$l30 - 1) * BYTES_PER_CHUNK$l29));
          for i$42 in 0 .. num_bytes_in_final_chunk$l41 {
              result$l27[(((num_chunks$l30 - 1) * BYTES_PER_CHUNK$l29) + i$l42)] = slice_bytes$l40[i$l42]
          }
      };
      result$l27
  }
*)
Definition base64_decode₃ (α : list Value.t) : M.t :=
  match α with
  | [input] =>
    let input := M.alloc input in
    let* result :=
      let~ decoded := [[ M.copy (|
        M.alloc (M.call_closure (|
          get_function "base64_decode_elements" 8,
          [
            M.read (| input |)
          ]
        |))
      |) ]] in
      let~ result := [[ M.copy_mutable (|
        M.alloc (Value.Array [
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0
        ])
      |) ]] in
      let~ BASE64_ELEMENTS_PER_CHUNK := [[ M.copy (|
        M.alloc (Value.Integer IntegerKind.U32 40)
      |) ]] in
      let~ BYTES_PER_CHUNK := [[ M.copy (|
        M.alloc (Value.Integer IntegerKind.U32 30)
      |) ]] in
      let~ num_chunks := [[ M.copy (|
        M.alloc (Binary.add (|
          Binary.divide (|
            Value.Integer IntegerKind.U32 118,
            M.read (| BASE64_ELEMENTS_PER_CHUNK |)
          |),
          M.cast (|
            Binary.not_equal (|
              Binary.modulo (|
                Value.Integer IntegerKind.U32 118,
                M.read (| BASE64_ELEMENTS_PER_CHUNK |)
              |),
              Value.Integer IntegerKind.U32 0
            |),
            IntegerKind.U32
          |)
        |))
      |) ]] in
      do~ [[
        M.if_ (|
          Binary.greater (|
            M.read (| num_chunks |),
            Value.Integer IntegerKind.U32 0
          |),
          do~ [[
            M.for_ (|
              Value.Integer IntegerKind.U32 0,
              Binary.subtract (|
                M.read (| num_chunks |),
                Value.Integer IntegerKind.U32 1
              |),
              fun (i : Value.t) =>
              let~ slice := [[ M.copy_mutable (|
                M.alloc (Value.Integer IntegerKind.Field 0)
              |) ]] in
              do~ [[
                M.for_ (|
                  Value.Integer IntegerKind.U32 0,
                  M.read (| BASE64_ELEMENTS_PER_CHUNK |),
                  fun (j : Value.t) =>
                  do~ [[
                    M.alloc (M.write (|
                      slice,
                      Binary.multiply (|
                        M.read (| slice |),
                        Value.Integer IntegerKind.Field 64
                      |)
                    |))
                  ]] in
                  [[
                    M.alloc (M.write (|
                      slice,
                      Binary.add (|
                        M.read (| slice |),
                        M.cast (|
                          M.read (| M.index (|
                            decoded,
                            Binary.add (|
                              Binary.multiply (|
                                M.read (| i |),
                                M.read (| BASE64_ELEMENTS_PER_CHUNK |)
                              |),
                              M.read (| j |)
                            |)
                          |) |),
                          IntegerKind.Field
                        |)
                      |)
                    |))
                  ]]
                |)
              ]] in
              let~ slice_bytes := [[ M.copy (|
                M.alloc (M.call_closure (|
                  get_function "to_be_bytes" 9,
                  [
                    M.read (| slice |)
                  ]
                |))
              |) ]] in
              [[
                M.for_ (|
                  Value.Integer IntegerKind.U32 0,
                  M.read (| BYTES_PER_CHUNK |),
                  fun (j : Value.t) =>
                  [[
                    M.alloc (M.write (|
                      M.index (|
                        result,
                        Binary.add (|
                          Binary.multiply (|
                            M.read (| i |),
                            M.read (| BYTES_PER_CHUNK |)
                          |),
                          M.read (| j |)
                        |)
                      |),
                      M.read (| M.index (|
                        slice_bytes,
                        M.read (| j |)
                      |) |)
                    |))
                  ]]
                |)
              ]]
            |)
          ]] in
          let~ base64_elements_in_final_chunk := [[ M.copy (|
            M.alloc (Binary.subtract (|
              Value.Integer IntegerKind.U32 118,
              Binary.multiply (|
                Binary.subtract (|
                  M.read (| num_chunks |),
                  Value.Integer IntegerKind.U32 1
                |),
                M.read (| BASE64_ELEMENTS_PER_CHUNK |)
              |)
            |))
          |) ]] in
          let~ slice := [[ M.copy_mutable (|
            M.alloc (Value.Integer IntegerKind.Field 0)
          |) ]] in
          do~ [[
            M.for_ (|
              Value.Integer IntegerKind.U32 0,
              M.read (| base64_elements_in_final_chunk |),
              fun (j : Value.t) =>
              do~ [[
                M.alloc (M.write (|
                  slice,
                  Binary.multiply (|
                    M.read (| slice |),
                    Value.Integer IntegerKind.Field 64
                  |)
                |))
              ]] in
              [[
                M.alloc (M.write (|
                  slice,
                  Binary.add (|
                    M.read (| slice |),
                    M.cast (|
                      M.read (| M.index (|
                        decoded,
                        Binary.add (|
                          Binary.multiply (|
                            Binary.subtract (|
                              M.read (| num_chunks |),
                              Value.Integer IntegerKind.U32 1
                            |),
                            M.read (| BASE64_ELEMENTS_PER_CHUNK |)
                          |),
                          M.read (| j |)
                        |)
                      |) |),
                      IntegerKind.Field
                    |)
                  |)
                |))
              ]]
            |)
          ]] in
          do~ [[
            M.for_ (|
              M.read (| base64_elements_in_final_chunk |),
              M.read (| BASE64_ELEMENTS_PER_CHUNK |),
              fun (_ : Value.t) =>
              [[
                M.alloc (M.write (|
                  slice,
                  Binary.multiply (|
                    M.read (| slice |),
                    Value.Integer IntegerKind.Field 64
                  |)
                |))
              ]]
            |)
          ]] in
          let~ slice_bytes := [[ M.copy (|
            M.alloc (M.call_closure (|
              get_function "to_be_bytes" 9,
              [
                M.read (| slice |)
              ]
            |))
          |) ]] in
          let~ num_bytes_in_final_chunk := [[ M.copy (|
            M.alloc (Binary.subtract (|
              Value.Integer IntegerKind.U32 88,
              Binary.multiply (|
                Binary.subtract (|
                  M.read (| num_chunks |),
                  Value.Integer IntegerKind.U32 1
                |),
                M.read (| BYTES_PER_CHUNK |)
              |)
            |))
          |) ]] in
          [[
            M.for_ (|
              Value.Integer IntegerKind.U32 0,
              M.read (| num_bytes_in_final_chunk |),
              fun (i : Value.t) =>
              [[
                M.alloc (M.write (|
                  M.index (|
                    result,
                    Binary.add (|
                      Binary.multiply (|
                        Binary.subtract (|
                          M.read (| num_chunks |),
                          Value.Integer IntegerKind.U32 1
                        |),
                        M.read (| BYTES_PER_CHUNK |)
                      |),
                      M.read (| i |)
                    |)
                  |),
                  M.read (| M.index (|
                    slice_bytes,
                    M.read (| i |)
                  |) |)
                |))
              ]]
            |)
          ]],
          None
        |)
      ]] in
      [[
        result
      ]] in
    M.read result
  | _ => M.impossible "wrong number of arguments"
  end.

Axiom get_function_base64_decode₃ :
  get_function "base64_decode" 3 =
  closure base64_decode₃.
Global Hint Rewrite get_function_base64_decode₃ : get_function.

(*
  fn eq$f4(self$l43: [u8; 88], other$l44: [u8; 88]) -> bool {
      let result$45 = true;
      for i$46 in 0 .. len$array_len(self$l43) {
          result$l45 = (result$l45 & eq$f7(self$l43[i$l46], other$l44[i$l46]))
      };
      result$l45
  }
*)
Definition eq₄ (α : list Value.t) : M.t :=
  match α with
  | [self; other] =>
    let self := M.alloc self in
    let other := M.alloc other in
    let* result :=
      let~ result := [[ M.copy_mutable (|
        M.alloc (Value.Bool true)
      |) ]] in
      do~ [[
        M.for_ (|
          Value.Integer IntegerKind.U32 0,
          M.call_closure (|
            M.read (| Builtin.len |),
            [
              M.read (| self |)
            ]
          |),
          fun (i : Value.t) =>
          [[
            M.alloc (M.write (|
              result,
              Binary.and_ (|
                M.read (| result |),
                M.call_closure (|
                  get_function "eq" 7,
                  [
                    M.read (| M.index (|
                      self,
                      M.read (| i |)
                    |) |);
                    M.read (| M.index (|
                      other,
                      M.read (| i |)
                    |) |)
                  ]
                |)
              |)
            |))
          ]]
        |)
      ]] in
      [[
        result
      ]] in
    M.read result
  | _ => M.impossible "wrong number of arguments"
  end.

Axiom get_function_eq₄ :
  get_function "eq" 4 =
  closure eq₄.
Global Hint Rewrite get_function_eq₄ : get_function.

(*
  fn to_be_radix$f5(self$l47: Field, radix$l48: u32) -> [u8; 40] {
      assert_constant$assert_constant(radix$l48);;
      __to_be_radix$to_be_radix(self$l47, radix$l48)
  }
*)
Definition to_be_radix₅ (α : list Value.t) : M.t :=
  match α with
  | [self; radix] =>
    let self := M.alloc self in
    let radix := M.alloc radix in
    let* result :=
      do~ [[
        M.alloc (M.call_closure (|
          M.read (| Builtin.assert_constant |),
          [
            M.read (| radix |)
          ]
        |))
      ]] in
      [[
        M.alloc (M.call_closure (|
          M.read (| Builtin.__to_be_radix |),
          [
            M.read (| self |);
            M.read (| radix |)
          ]
        |))
      ]] in
    M.read result
  | _ => M.impossible "wrong number of arguments"
  end.

Axiom get_function_to_be_radix₅ :
  get_function "to_be_radix" 5 =
  closure to_be_radix₅.
Global Hint Rewrite get_function_to_be_radix₅ : get_function.

(*
  fn base64_encode_elements$f6(input$l49: [u8; 118]) -> [u8; 118] {
      let Base64Encoder$50 = new$f10();
      let result$51 = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
      for i$52 in 0 .. 118 {
          result$l51[i$l52] = get$f11(Base64Encoder$l50, (input$l49[i$l52] as Field))
      };
      result$l51
  }
*)
Definition base64_encode_elements₆ (α : list Value.t) : M.t :=
  match α with
  | [input] =>
    let input := M.alloc input in
    let* result :=
      let~ Base64Encoder := [[ M.copy_mutable (|
        M.alloc (M.call_closure (|
          get_function "new" 10,
          []
        |))
      |) ]] in
      let~ result := [[ M.copy_mutable (|
        M.alloc (Value.Array [
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0
        ])
      |) ]] in
      do~ [[
        M.for_ (|
          Value.Integer IntegerKind.U32 0,
          Value.Integer IntegerKind.U32 118,
          fun (i : Value.t) =>
          [[
            M.alloc (M.write (|
              M.index (|
                result,
                M.read (| i |)
              |),
              M.call_closure (|
                get_function "get" 11,
                [
                  M.read (| Base64Encoder |);
                  M.cast (|
                    M.read (| M.index (|
                      input,
                      M.read (| i |)
                    |) |),
                    IntegerKind.Field
                  |)
                ]
              |)
            |))
          ]]
        |)
      ]] in
      [[
        result
      ]] in
    M.read result
  | _ => M.impossible "wrong number of arguments"
  end.

Axiom get_function_base64_encode_elements₆ :
  get_function "base64_encode_elements" 6 =
  closure base64_encode_elements₆.
Global Hint Rewrite get_function_base64_encode_elements₆ : get_function.

(*
  fn eq$f7(self$l53: u8, other$l54: u8) -> bool {
      (self$l53 == other$l54)
  }
*)
Definition eq₇ (α : list Value.t) : M.t :=
  match α with
  | [self; other] =>
    let self := M.alloc self in
    let other := M.alloc other in
    let* result :=
      [[
        M.alloc (Binary.equal (|
          M.read (| self |),
          M.read (| other |)
        |))
      ]] in
    M.read result
  | _ => M.impossible "wrong number of arguments"
  end.

Axiom get_function_eq₇ :
  get_function "eq" 7 =
  closure eq₇.
Global Hint Rewrite get_function_eq₇ : get_function.

(*
  fn base64_decode_elements$f8(input$l55: [u8; 118]) -> [u8; 118] {
      let Base64Decoder$56 = new$f12();
      let result$57 = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
      for i$58 in 0 .. 118 {
          let input_byte$59 = input$l55[i$l58];
          result$l57[i$l58] = get$f13(Base64Decoder$l56, (input_byte$l59 as Field));
          constrain (result$l57[i$l58] != 255)
      };
      result$l57
  }
*)
Definition base64_decode_elements₈ (α : list Value.t) : M.t :=
  match α with
  | [input] =>
    let input := M.alloc input in
    let* result :=
      let~ Base64Decoder := [[ M.copy_mutable (|
        M.alloc (M.call_closure (|
          get_function "new" 12,
          []
        |))
      |) ]] in
      let~ result := [[ M.copy_mutable (|
        M.alloc (Value.Array [
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0
        ])
      |) ]] in
      do~ [[
        M.for_ (|
          Value.Integer IntegerKind.U32 0,
          Value.Integer IntegerKind.U32 118,
          fun (i : Value.t) =>
          let~ input_byte := [[ M.copy (|
            M.index (|
              input,
              M.read (| i |)
            |)
          |) ]] in
          do~ [[
            M.alloc (M.write (|
              M.index (|
                result,
                M.read (| i |)
              |),
              M.call_closure (|
                get_function "get" 13,
                [
                  M.read (| Base64Decoder |);
                  M.cast (|
                    M.read (| input_byte |),
                    IntegerKind.Field
                  |)
                ]
              |)
            |))
          ]] in
          [[
            M.alloc (M.assert (|
              Binary.not_equal (|
                M.read (| M.index (|
                  result,
                  M.read (| i |)
                |) |),
                Value.Integer IntegerKind.U8 255
              |),
              Some (Value.fmt_str "DecodeError: invalid symbol {input_byte}, offset {i}." 2(M.alloc (Value.Tuple [M.read (| input_byte |); M.read (| i |)])))
            |))
          ]]
        |)
      ]] in
      [[
        result
      ]] in
    M.read result
  | _ => M.impossible "wrong number of arguments"
  end.

Axiom get_function_base64_decode_elements₈ :
  get_function "base64_decode_elements" 8 =
  closure base64_decode_elements₈.
Global Hint Rewrite get_function_base64_decode_elements₈ : get_function.

(*
  fn to_be_bytes$f9(self$l60: Field) -> [u8; 30] {
      let bytes$61 = to_be_radix$f14(self$l60, 2⁸);
      if (!is_unconstrained$is_unconstrained()) {
          let p$62 = &[2⁴×3, 100, 78, 114, 225, 49, 2⁴×10, 41, 184, 2⁴×5, 69, 182, 129, 129, 88, 93, 40, 51, 232, 72, 121, 185, 2⁴×7, 145, 67, 225, 245, 147, 2⁴×15, 0, 0, 1];
          constrain (len$array_len(bytes$l61) <= len$array_len(p$l62));
          let ok$63 = (len$array_len(bytes$l61) != len$array_len(p$l62));
          for i$64 in 0 .. 30 {
              if (!ok$l63) {
                  if (bytes$l61[i$l64] != p$l62[i$l64]) {
                      constrain (bytes$l61[i$l64] < p$l62[i$l64]);
                      ok$l63 = true
                  }
              }
          };
          constrain ok$l63
      };
      bytes$l61
  }
*)
Definition to_be_bytes₉ (α : list Value.t) : M.t :=
  match α with
  | [self] =>
    let self := M.alloc self in
    let* result :=
      let~ bytes := [[ M.copy (|
        M.alloc (M.call_closure (|
          get_function "to_be_radix" 14,
          [
            M.read (| self |);
            Value.Integer IntegerKind.U32 256
          ]
        |))
      |) ]] in
      do~ [[
        M.if_ (|
          Unary.not (|
            M.call_closure (|
              M.read (| Builtin.is_unconstrained |),
              []
            |)
          |),
          let~ p := [[ M.copy (|
            M.alloc (Value.Slice [
              Value.Integer IntegerKind.U8 48;
              Value.Integer IntegerKind.U8 100;
              Value.Integer IntegerKind.U8 78;
              Value.Integer IntegerKind.U8 114;
              Value.Integer IntegerKind.U8 225;
              Value.Integer IntegerKind.U8 49;
              Value.Integer IntegerKind.U8 160;
              Value.Integer IntegerKind.U8 41;
              Value.Integer IntegerKind.U8 184;
              Value.Integer IntegerKind.U8 80;
              Value.Integer IntegerKind.U8 69;
              Value.Integer IntegerKind.U8 182;
              Value.Integer IntegerKind.U8 129;
              Value.Integer IntegerKind.U8 129;
              Value.Integer IntegerKind.U8 88;
              Value.Integer IntegerKind.U8 93;
              Value.Integer IntegerKind.U8 40;
              Value.Integer IntegerKind.U8 51;
              Value.Integer IntegerKind.U8 232;
              Value.Integer IntegerKind.U8 72;
              Value.Integer IntegerKind.U8 121;
              Value.Integer IntegerKind.U8 185;
              Value.Integer IntegerKind.U8 112;
              Value.Integer IntegerKind.U8 145;
              Value.Integer IntegerKind.U8 67;
              Value.Integer IntegerKind.U8 225;
              Value.Integer IntegerKind.U8 245;
              Value.Integer IntegerKind.U8 147;
              Value.Integer IntegerKind.U8 240;
              Value.Integer IntegerKind.U8 0;
              Value.Integer IntegerKind.U8 0;
              Value.Integer IntegerKind.U8 1
            ])
          |) ]] in
          do~ [[
            M.alloc (M.assert (|
              Binary.less_equal (|
                M.call_closure (|
                  M.read (| Builtin.len |),
                  [
                    M.read (| bytes |)
                  ]
                |),
                M.call_closure (|
                  M.read (| Builtin.len |),
                  [
                    M.read (| p |)
                  ]
                |)
              |),
              None
            |))
          ]] in
          let~ ok := [[ M.copy_mutable (|
            M.alloc (Binary.not_equal (|
              M.call_closure (|
                M.read (| Builtin.len |),
                [
                  M.read (| bytes |)
                ]
              |),
              M.call_closure (|
                M.read (| Builtin.len |),
                [
                  M.read (| p |)
                ]
              |)
            |))
          |) ]] in
          do~ [[
            M.for_ (|
              Value.Integer IntegerKind.U32 0,
              Value.Integer IntegerKind.U32 30,
              fun (i : Value.t) =>
              [[
                M.if_ (|
                  Unary.not (|
                    M.read (| ok |)
                  |),
                  [[
                    M.if_ (|
                      Binary.not_equal (|
                        M.read (| M.index (|
                          bytes,
                          M.read (| i |)
                        |) |),
                        M.read (| M.index (|
                          p,
                          M.read (| i |)
                        |) |)
                      |),
                      do~ [[
                        M.alloc (M.assert (|
                          Binary.less (|
                            M.read (| M.index (|
                              bytes,
                              M.read (| i |)
                            |) |),
                            M.read (| M.index (|
                              p,
                              M.read (| i |)
                            |) |)
                          |),
                          None
                        |))
                      ]] in
                      [[
                        M.alloc (M.write (|
                          ok,
                          Value.Bool true
                        |))
                      ]],
                      None
                    |)
                  ]],
                  None
                |)
              ]]
            |)
          ]] in
          [[
            M.alloc (M.assert (|
              M.read (| ok |),
              None
            |))
          ]],
          None
        |)
      ]] in
      [[
        bytes
      ]] in
    M.read result
  | _ => M.impossible "wrong number of arguments"
  end.

Axiom get_function_to_be_bytes₉ :
  get_function "to_be_bytes" 9 =
  closure to_be_bytes₉.
Global Hint Rewrite get_function_to_be_bytes₉ : get_function.

(*
  fn new$f10() -> ([u8; 64]) {
      {
          let table$65 = [65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 2⁴×5, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 2⁴×7, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 2⁴×3, 49, 50, 51, 52, 53, 54, 55, 56, 57, 43, 47];
          (table$l65)
      }
  }
*)
Definition new₁₀ (α : list Value.t) : M.t :=
  match α with
  | [] =>
    let* result :=
      [[
        let~ table := [[ M.copy (|
          M.alloc (Value.Array [
            Value.Integer IntegerKind.U8 65;
            Value.Integer IntegerKind.U8 66;
            Value.Integer IntegerKind.U8 67;
            Value.Integer IntegerKind.U8 68;
            Value.Integer IntegerKind.U8 69;
            Value.Integer IntegerKind.U8 70;
            Value.Integer IntegerKind.U8 71;
            Value.Integer IntegerKind.U8 72;
            Value.Integer IntegerKind.U8 73;
            Value.Integer IntegerKind.U8 74;
            Value.Integer IntegerKind.U8 75;
            Value.Integer IntegerKind.U8 76;
            Value.Integer IntegerKind.U8 77;
            Value.Integer IntegerKind.U8 78;
            Value.Integer IntegerKind.U8 79;
            Value.Integer IntegerKind.U8 80;
            Value.Integer IntegerKind.U8 81;
            Value.Integer IntegerKind.U8 82;
            Value.Integer IntegerKind.U8 83;
            Value.Integer IntegerKind.U8 84;
            Value.Integer IntegerKind.U8 85;
            Value.Integer IntegerKind.U8 86;
            Value.Integer IntegerKind.U8 87;
            Value.Integer IntegerKind.U8 88;
            Value.Integer IntegerKind.U8 89;
            Value.Integer IntegerKind.U8 90;
            Value.Integer IntegerKind.U8 97;
            Value.Integer IntegerKind.U8 98;
            Value.Integer IntegerKind.U8 99;
            Value.Integer IntegerKind.U8 100;
            Value.Integer IntegerKind.U8 101;
            Value.Integer IntegerKind.U8 102;
            Value.Integer IntegerKind.U8 103;
            Value.Integer IntegerKind.U8 104;
            Value.Integer IntegerKind.U8 105;
            Value.Integer IntegerKind.U8 106;
            Value.Integer IntegerKind.U8 107;
            Value.Integer IntegerKind.U8 108;
            Value.Integer IntegerKind.U8 109;
            Value.Integer IntegerKind.U8 110;
            Value.Integer IntegerKind.U8 111;
            Value.Integer IntegerKind.U8 112;
            Value.Integer IntegerKind.U8 113;
            Value.Integer IntegerKind.U8 114;
            Value.Integer IntegerKind.U8 115;
            Value.Integer IntegerKind.U8 116;
            Value.Integer IntegerKind.U8 117;
            Value.Integer IntegerKind.U8 118;
            Value.Integer IntegerKind.U8 119;
            Value.Integer IntegerKind.U8 120;
            Value.Integer IntegerKind.U8 121;
            Value.Integer IntegerKind.U8 122;
            Value.Integer IntegerKind.U8 48;
            Value.Integer IntegerKind.U8 49;
            Value.Integer IntegerKind.U8 50;
            Value.Integer IntegerKind.U8 51;
            Value.Integer IntegerKind.U8 52;
            Value.Integer IntegerKind.U8 53;
            Value.Integer IntegerKind.U8 54;
            Value.Integer IntegerKind.U8 55;
            Value.Integer IntegerKind.U8 56;
            Value.Integer IntegerKind.U8 57;
            Value.Integer IntegerKind.U8 43;
            Value.Integer IntegerKind.U8 47
          ])
        |) ]] in
        [[
          M.alloc (Value.Tuple [M.read (| table |)])
        ]]
      ]] in
    M.read result
  | _ => M.impossible "wrong number of arguments"
  end.

Axiom get_function_new₁₀ :
  get_function "new" 10 =
  closure new₁₀.
Global Hint Rewrite get_function_new₁₀ : get_function.

(*
  fn get$f11(self$l66: ([u8; 64]), idx$l67: Field) -> u8 {
      self$l66.0[idx$l67]
  }
*)
Definition get₁₁ (α : list Value.t) : M.t :=
  match α with
  | [self; idx] =>
    let self := M.alloc self in
    let idx := M.alloc idx in
    let* result :=
      [[
        M.index (|
          M.extract_tuple_field (|
              self,
            0
          |),
          M.read (| idx |)
        |)
      ]] in
    M.read result
  | _ => M.impossible "wrong number of arguments"
  end.

Axiom get_function_get₁₁ :
  get_function "get" 11 =
  closure get₁₁.
Global Hint Rewrite get_function_get₁₁ : get_function.

(*
  fn new$f12() -> ([u8; 256]) {
      {
          let table$68 = [255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 62, 255, 255, 255, 63, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 255, 255, 255, 255, 255, 255, 255, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 2⁴, 17, 18, 19, 20, 21, 22, 23, 24, 25, 255, 255, 255, 255, 255, 255, 26, 27, 28, 29, 30, 31, 2⁵, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 2⁴×3, 49, 50, 51, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255];
          (table$l68)
      }
  }
*)
Definition new₁₂ (α : list Value.t) : M.t :=
  match α with
  | [] =>
    let* result :=
      [[
        let~ table := [[ M.copy (|
          M.alloc (Value.Array [
            Value.Integer IntegerKind.U8 255;
            Value.Integer IntegerKind.U8 255;
            Value.Integer IntegerKind.U8 255;
            Value.Integer IntegerKind.U8 255;
            Value.Integer IntegerKind.U8 255;
            Value.Integer IntegerKind.U8 255;
            Value.Integer IntegerKind.U8 255;
            Value.Integer IntegerKind.U8 255;
            Value.Integer IntegerKind.U8 255;
            Value.Integer IntegerKind.U8 255;
            Value.Integer IntegerKind.U8 255;
            Value.Integer IntegerKind.U8 255;
            Value.Integer IntegerKind.U8 255;
            Value.Integer IntegerKind.U8 255;
            Value.Integer IntegerKind.U8 255;
            Value.Integer IntegerKind.U8 255;
            Value.Integer IntegerKind.U8 255;
            Value.Integer IntegerKind.U8 255;
            Value.Integer IntegerKind.U8 255;
            Value.Integer IntegerKind.U8 255;
            Value.Integer IntegerKind.U8 255;
            Value.Integer IntegerKind.U8 255;
            Value.Integer IntegerKind.U8 255;
            Value.Integer IntegerKind.U8 255;
            Value.Integer IntegerKind.U8 255;
            Value.Integer IntegerKind.U8 255;
            Value.Integer IntegerKind.U8 255;
            Value.Integer IntegerKind.U8 255;
            Value.Integer IntegerKind.U8 255;
            Value.Integer IntegerKind.U8 255;
            Value.Integer IntegerKind.U8 255;
            Value.Integer IntegerKind.U8 255;
            Value.Integer IntegerKind.U8 255;
            Value.Integer IntegerKind.U8 255;
            Value.Integer IntegerKind.U8 255;
            Value.Integer IntegerKind.U8 255;
            Value.Integer IntegerKind.U8 255;
            Value.Integer IntegerKind.U8 255;
            Value.Integer IntegerKind.U8 255;
            Value.Integer IntegerKind.U8 255;
            Value.Integer IntegerKind.U8 255;
            Value.Integer IntegerKind.U8 255;
            Value.Integer IntegerKind.U8 255;
            Value.Integer IntegerKind.U8 62;
            Value.Integer IntegerKind.U8 255;
            Value.Integer IntegerKind.U8 255;
            Value.Integer IntegerKind.U8 255;
            Value.Integer IntegerKind.U8 63;
            Value.Integer IntegerKind.U8 52;
            Value.Integer IntegerKind.U8 53;
            Value.Integer IntegerKind.U8 54;
            Value.Integer IntegerKind.U8 55;
            Value.Integer IntegerKind.U8 56;
            Value.Integer IntegerKind.U8 57;
            Value.Integer IntegerKind.U8 58;
            Value.Integer IntegerKind.U8 59;
            Value.Integer IntegerKind.U8 60;
            Value.Integer IntegerKind.U8 61;
            Value.Integer IntegerKind.U8 255;
            Value.Integer IntegerKind.U8 255;
            Value.Integer IntegerKind.U8 255;
            Value.Integer IntegerKind.U8 255;
            Value.Integer IntegerKind.U8 255;
            Value.Integer IntegerKind.U8 255;
            Value.Integer IntegerKind.U8 255;
            Value.Integer IntegerKind.U8 0;
            Value.Integer IntegerKind.U8 1;
            Value.Integer IntegerKind.U8 2;
            Value.Integer IntegerKind.U8 3;
            Value.Integer IntegerKind.U8 4;
            Value.Integer IntegerKind.U8 5;
            Value.Integer IntegerKind.U8 6;
            Value.Integer IntegerKind.U8 7;
            Value.Integer IntegerKind.U8 8;
            Value.Integer IntegerKind.U8 9;
            Value.Integer IntegerKind.U8 10;
            Value.Integer IntegerKind.U8 11;
            Value.Integer IntegerKind.U8 12;
            Value.Integer IntegerKind.U8 13;
            Value.Integer IntegerKind.U8 14;
            Value.Integer IntegerKind.U8 15;
            Value.Integer IntegerKind.U8 16;
            Value.Integer IntegerKind.U8 17;
            Value.Integer IntegerKind.U8 18;
            Value.Integer IntegerKind.U8 19;
            Value.Integer IntegerKind.U8 20;
            Value.Integer IntegerKind.U8 21;
            Value.Integer IntegerKind.U8 22;
            Value.Integer IntegerKind.U8 23;
            Value.Integer IntegerKind.U8 24;
            Value.Integer IntegerKind.U8 25;
            Value.Integer IntegerKind.U8 255;
            Value.Integer IntegerKind.U8 255;
            Value.Integer IntegerKind.U8 255;
            Value.Integer IntegerKind.U8 255;
            Value.Integer IntegerKind.U8 255;
            Value.Integer IntegerKind.U8 255;
            Value.Integer IntegerKind.U8 26;
            Value.Integer IntegerKind.U8 27;
            Value.Integer IntegerKind.U8 28;
            Value.Integer IntegerKind.U8 29;
            Value.Integer IntegerKind.U8 30;
            Value.Integer IntegerKind.U8 31;
            Value.Integer IntegerKind.U8 32;
            Value.Integer IntegerKind.U8 33;
            Value.Integer IntegerKind.U8 34;
            Value.Integer IntegerKind.U8 35;
            Value.Integer IntegerKind.U8 36;
            Value.Integer IntegerKind.U8 37;
            Value.Integer IntegerKind.U8 38;
            Value.Integer IntegerKind.U8 39;
            Value.Integer IntegerKind.U8 40;
            Value.Integer IntegerKind.U8 41;
            Value.Integer IntegerKind.U8 42;
            Value.Integer IntegerKind.U8 43;
            Value.Integer IntegerKind.U8 44;
            Value.Integer IntegerKind.U8 45;
            Value.Integer IntegerKind.U8 46;
            Value.Integer IntegerKind.U8 47;
            Value.Integer IntegerKind.U8 48;
            Value.Integer IntegerKind.U8 49;
            Value.Integer IntegerKind.U8 50;
            Value.Integer IntegerKind.U8 51;
            Value.Integer IntegerKind.U8 255;
            Value.Integer IntegerKind.U8 255;
            Value.Integer IntegerKind.U8 255;
            Value.Integer IntegerKind.U8 255;
            Value.Integer IntegerKind.U8 255;
            Value.Integer IntegerKind.U8 255;
            Value.Integer IntegerKind.U8 255;
            Value.Integer IntegerKind.U8 255;
            Value.Integer IntegerKind.U8 255;
            Value.Integer IntegerKind.U8 255;
            Value.Integer IntegerKind.U8 255;
            Value.Integer IntegerKind.U8 255;
            Value.Integer IntegerKind.U8 255;
            Value.Integer IntegerKind.U8 255;
            Value.Integer IntegerKind.U8 255;
            Value.Integer IntegerKind.U8 255;
            Value.Integer IntegerKind.U8 255;
            Value.Integer IntegerKind.U8 255;
            Value.Integer IntegerKind.U8 255;
            Value.Integer IntegerKind.U8 255;
            Value.Integer IntegerKind.U8 255;
            Value.Integer IntegerKind.U8 255;
            Value.Integer IntegerKind.U8 255;
            Value.Integer IntegerKind.U8 255;
            Value.Integer IntegerKind.U8 255;
            Value.Integer IntegerKind.U8 255;
            Value.Integer IntegerKind.U8 255;
            Value.Integer IntegerKind.U8 255;
            Value.Integer IntegerKind.U8 255;
            Value.Integer IntegerKind.U8 255;
            Value.Integer IntegerKind.U8 255;
            Value.Integer IntegerKind.U8 255;
            Value.Integer IntegerKind.U8 255;
            Value.Integer IntegerKind.U8 255;
            Value.Integer IntegerKind.U8 255;
            Value.Integer IntegerKind.U8 255;
            Value.Integer IntegerKind.U8 255;
            Value.Integer IntegerKind.U8 255;
            Value.Integer IntegerKind.U8 255;
            Value.Integer IntegerKind.U8 255;
            Value.Integer IntegerKind.U8 255;
            Value.Integer IntegerKind.U8 255;
            Value.Integer IntegerKind.U8 255;
            Value.Integer IntegerKind.U8 255;
            Value.Integer IntegerKind.U8 255;
            Value.Integer IntegerKind.U8 255;
            Value.Integer IntegerKind.U8 255;
            Value.Integer IntegerKind.U8 255;
            Value.Integer IntegerKind.U8 255;
            Value.Integer IntegerKind.U8 255;
            Value.Integer IntegerKind.U8 255;
            Value.Integer IntegerKind.U8 255;
            Value.Integer IntegerKind.U8 255;
            Value.Integer IntegerKind.U8 255;
            Value.Integer IntegerKind.U8 255;
            Value.Integer IntegerKind.U8 255;
            Value.Integer IntegerKind.U8 255;
            Value.Integer IntegerKind.U8 255;
            Value.Integer IntegerKind.U8 255;
            Value.Integer IntegerKind.U8 255;
            Value.Integer IntegerKind.U8 255;
            Value.Integer IntegerKind.U8 255;
            Value.Integer IntegerKind.U8 255;
            Value.Integer IntegerKind.U8 255;
            Value.Integer IntegerKind.U8 255;
            Value.Integer IntegerKind.U8 255;
            Value.Integer IntegerKind.U8 255;
            Value.Integer IntegerKind.U8 255;
            Value.Integer IntegerKind.U8 255;
            Value.Integer IntegerKind.U8 255;
            Value.Integer IntegerKind.U8 255;
            Value.Integer IntegerKind.U8 255;
            Value.Integer IntegerKind.U8 255;
            Value.Integer IntegerKind.U8 255;
            Value.Integer IntegerKind.U8 255;
            Value.Integer IntegerKind.U8 255;
            Value.Integer IntegerKind.U8 255;
            Value.Integer IntegerKind.U8 255;
            Value.Integer IntegerKind.U8 255;
            Value.Integer IntegerKind.U8 255;
            Value.Integer IntegerKind.U8 255;
            Value.Integer IntegerKind.U8 255;
            Value.Integer IntegerKind.U8 255;
            Value.Integer IntegerKind.U8 255;
            Value.Integer IntegerKind.U8 255;
            Value.Integer IntegerKind.U8 255;
            Value.Integer IntegerKind.U8 255;
            Value.Integer IntegerKind.U8 255;
            Value.Integer IntegerKind.U8 255;
            Value.Integer IntegerKind.U8 255;
            Value.Integer IntegerKind.U8 255;
            Value.Integer IntegerKind.U8 255;
            Value.Integer IntegerKind.U8 255;
            Value.Integer IntegerKind.U8 255;
            Value.Integer IntegerKind.U8 255;
            Value.Integer IntegerKind.U8 255;
            Value.Integer IntegerKind.U8 255;
            Value.Integer IntegerKind.U8 255;
            Value.Integer IntegerKind.U8 255;
            Value.Integer IntegerKind.U8 255;
            Value.Integer IntegerKind.U8 255;
            Value.Integer IntegerKind.U8 255;
            Value.Integer IntegerKind.U8 255;
            Value.Integer IntegerKind.U8 255;
            Value.Integer IntegerKind.U8 255;
            Value.Integer IntegerKind.U8 255;
            Value.Integer IntegerKind.U8 255;
            Value.Integer IntegerKind.U8 255;
            Value.Integer IntegerKind.U8 255;
            Value.Integer IntegerKind.U8 255;
            Value.Integer IntegerKind.U8 255;
            Value.Integer IntegerKind.U8 255;
            Value.Integer IntegerKind.U8 255;
            Value.Integer IntegerKind.U8 255;
            Value.Integer IntegerKind.U8 255;
            Value.Integer IntegerKind.U8 255;
            Value.Integer IntegerKind.U8 255;
            Value.Integer IntegerKind.U8 255;
            Value.Integer IntegerKind.U8 255;
            Value.Integer IntegerKind.U8 255;
            Value.Integer IntegerKind.U8 255;
            Value.Integer IntegerKind.U8 255;
            Value.Integer IntegerKind.U8 255;
            Value.Integer IntegerKind.U8 255;
            Value.Integer IntegerKind.U8 255;
            Value.Integer IntegerKind.U8 255;
            Value.Integer IntegerKind.U8 255;
            Value.Integer IntegerKind.U8 255;
            Value.Integer IntegerKind.U8 255;
            Value.Integer IntegerKind.U8 255;
            Value.Integer IntegerKind.U8 255;
            Value.Integer IntegerKind.U8 255;
            Value.Integer IntegerKind.U8 255
          ])
        |) ]] in
        [[
          M.alloc (Value.Tuple [M.read (| table |)])
        ]]
      ]] in
    M.read result
  | _ => M.impossible "wrong number of arguments"
  end.

Axiom get_function_new₁₂ :
  get_function "new" 12 =
  closure new₁₂.
Global Hint Rewrite get_function_new₁₂ : get_function.

(*
  fn get$f13(self$l69: ([u8; 256]), idx$l70: Field) -> u8 {
      self$l69.0[idx$l70]
  }
*)
Definition get₁₃ (α : list Value.t) : M.t :=
  match α with
  | [self; idx] =>
    let self := M.alloc self in
    let idx := M.alloc idx in
    let* result :=
      [[
        M.index (|
          M.extract_tuple_field (|
              self,
            0
          |),
          M.read (| idx |)
        |)
      ]] in
    M.read result
  | _ => M.impossible "wrong number of arguments"
  end.

Axiom get_function_get₁₃ :
  get_function "get" 13 =
  closure get₁₃.
Global Hint Rewrite get_function_get₁₃ : get_function.

(*
  fn to_be_radix$f14(self$l71: Field, radix$l72: u32) -> [u8; 30] {
      assert_constant$assert_constant(radix$l72);;
      __to_be_radix$to_be_radix(self$l71, radix$l72)
  }
*)
Definition to_be_radix₁₄ (α : list Value.t) : M.t :=
  match α with
  | [self; radix] =>
    let self := M.alloc self in
    let radix := M.alloc radix in
    let* result :=
      do~ [[
        M.alloc (M.call_closure (|
          M.read (| Builtin.assert_constant |),
          [
            M.read (| radix |)
          ]
        |))
      ]] in
      [[
        M.alloc (M.call_closure (|
          M.read (| Builtin.__to_be_radix |),
          [
            M.read (| self |);
            M.read (| radix |)
          ]
        |))
      ]] in
    M.read result
  | _ => M.impossible "wrong number of arguments"
  end.

Axiom get_function_to_be_radix₁₄ :
  get_function "to_be_radix" 14 =
  closure to_be_radix₁₄.
Global Hint Rewrite get_function_to_be_radix₁₄ : get_function.
