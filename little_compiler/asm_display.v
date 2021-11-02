Require Import ZArith List.
From Semantics Require Import syntax little little_w_string parser asm.
Require Import String.
Import ListNotations.
Open Scope string_scope.

(* The file little contains a definition of the little language as a functor,
  where the actual type for strings is left abstract.  The advantage is that
  this parameter can be instantiated by Ocaml string in extracted code, or
  by Coq string in interactive experiments. *)

(* The file little_w_string contains the instantiation to be used in Coq
  interactive experiments.   The compiler defined in asm is also in a functor.
  To play with it in interactive experiments, we also instantiated with
  the Coq strings. *)
Module scomp := compiler str.
Import scomp.

(* If we want to compile an example, it is convenient to first parse this
  example to obtain an expression in the little datatype. *)
Definition little_cp s : list assembly :=
  match parse_program (tokenize s Start "") with
    Some (env, i) =>
    scomp.compile_instr (map fst env) 0 i
  | None => nil
  end.

(* Here is little example of a program.  This program computes the sum of
   the first 4 natural numbers. *)
Definition pg := little_cp
"variables x 0; y 0 in 
while x < 4 do
x := x + 1;
y := x + y
done
end".

(* The following computation illustrates the program that we can obtain. *)
Compute pg.

(* The following computation illustrates the state of the stack machine
  after 4 steps of execution. *)
Compute exec_asm 4 pg nil [0%Z;0%Z] 0.
Compute nth_error pg 4.


(* The rest of the file illustrates how we can use the proof mode to step
  through the execution of the compiled program:
  we create two hypotheses, one is used to display the next instruction to
  execute, the other is used to display the current state of the machine:
  the stack, the memory, and the program counter. *)

(* This is a phantom type used to display the next instruction. *)
Definition ph (_ : option assembly) (_ : list Z * list Z * nat):= True.

Ltac xc :=
  match goal with
  id1 : ph _ (exec_asm ?n ?pg ?stk ?mem ?pc),
  id2 : ph _ _ |- _ =>
  clear id1 id2;
  let n' := constr:(S n) in
  let v := eval compute in (exec_asm n' pg stk mem pc) in
  let i := eval compute in (nth_error pg (snd v)) in
  assert (id1 : ph None (exec_asm n' pg stk mem pc)) by exact I;
  assert (id2 : ph i v) by reflexivity
  end.


Goal True.
assert (input : ph None (exec_asm 0 pg nil [0%Z; 0%Z] 0)) by exact I.
assert (state : ph None (nil, nil, 0%nat)) by exact I.
xc.
xc.
xc.
xc.
xc.
xc.
xc.
xc.
xc.
xc.
xc.
xc.
xc.
xc.
xc.
xc.
xc.
xc.
xc.
xc.
xc.
xc.
xc.
xc.
xc.
xc.
xc.
xc.
xc.
xc.
xc.
xc.
xc.
xc.
xc.
xc.
xc.
xc.
xc.
xc.
xc.
xc.
xc.
xc.
xc.
xc.
xc.
xc.
xc.
xc.
xc.
xc.
xc.
xc.
xc.
xc.
exact I.
Qed.
