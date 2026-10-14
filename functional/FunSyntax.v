From BootstrapExp.utils Require Import Core.
From Stdlib Require Import NArith Lists.List.
Import ListNotations.

Open Scope N.

Notation name := N (only parsing).

Inductive op : Type :=
| Add
| Sub
| Div
| Mul
| Cons
| Head
| Tail.

Inductive test : Type :=
| Less
| Equal.

Inductive exp : Type :=
| Const (n: N)                                 (* constant number            *)
| Var (n: name)                                (* local variable             *)
| Op (o: op) (args: list exp)                  (* primitive operations       *)
| If (t: test) (conds: list exp) (e1 e2: exp)  (* if test .. then .. else .. *)
| Let (n: name) (e1 e2: exp)                   (* let name = .. in ..        *)
| Call (f: name) (args: list exp).             (* call a function            *)

Inductive defun: Type :=
| Defun (n: name) (params: list name) (body: exp). (* func name, formal params, body *)

(* No programs since I/O will be handled elsewhere *)
