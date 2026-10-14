From BootstrapExp.utils Require Import Core.
From BootstrapExp.functional Require Import FunSyntax FunValues.
From BootstrapExp.functional Require Export FunEnv.

Hint Resolve FEnv.lookup_insert_eq : fenvDb.
Hint Resolve FEnv.lookup_insert_neq : fenvDb.
Hint Resolve FEnv.insert_insert_eq : fenvDb.
Hint Resolve FEnv.insert_insert_neq : fenvDb.
Hint Resolve FEnv.insert_remove : fenvDb.
Hint Resolve FEnv.lookup_empty : fenvDb.
Hint Resolve FEnv.insert_lookup_self : fenvDb.

Inductive err : Type :=
  | TimeOut
  | Crash.

Inductive result {A : Type} : Type :=
  | Res (v : A)
  | Err (e : err).
Arguments result : clear implicits.

Definition defunEnv := list FunSyntax.defun.

Definition fail {A}: result A :=
  Err Crash.

Definition eval_op (f : FunSyntax.op) (vs : list Value): result Value :=
  match f, vs with
  | FunSyntax.Add, [Num n1; Num n2] => Res (Num (n1 + n2))
  | FunSyntax.Sub, [Num n1; Num n2] => Res (Num (n1 - n2))
  | FunSyntax.Mul, [Num n1; Num n2] => Res (Num (n1 * n2))
  | FunSyntax.Div, [Num n1; Num n2] =>
    if n2 =? 0 then fail else Res (Num (n1 / n2))
  | FunSyntax.Cons, [x; y] => Res (Pair x y)
  | FunSyntax.Head, [Pair x y] => Res x
  | FunSyntax.Tail, [Pair x y] => Res y
  | _, _ => fail
  end.

Definition take_branch (test : FunSyntax.test) (vs : list Value): result bool :=
  match test, vs with
  | FunSyntax.Equal, [Pair x y; Num 0] => Res false
  | FunSyntax.Equal, [Num m; Num n] => Res (m =? n)
  | FunSyntax.Less, [Num m; Num n] => Res (m <? n)
  | _, _ => fail
  end.

Fixpoint make_env (keys : list name) (values : list Value) (acc : FEnv.env) : FEnv.env :=
  match keys, values with
  | [], [] => acc
  | k :: ks, v :: vs => make_env ks vs (FEnv.insert (k, Some v) acc)
  | _, _ => acc
  end.

Fixpoint lookup_fun (n : name) (fs : defunEnv) : option (list name * FunSyntax.exp) :=
  match fs with
  | [] => None
  | Defun k ps body :: rest => if (k =? n)%N then Some (ps, body) else lookup_fun n rest
  end.

Definition env_and_body (n : name) (args : list Value) (s : defunEnv) : option (FEnv.env * exp) :=
  match lookup_fun n s with
  | None => None
  | Some (params, body) => 
      if (List.length params =? List.length args)%nat then Some (make_env params args FEnv.empty, body) else None
  end.

Definition init_state (funs : list FunSyntax.defun) : defunEnv := funs.

Reserved Notation "funs ; env '|--' es '--->' vs " (at level 40, es at next level, vs at next level).

Inductive eval (funs : defunEnv) : FEnv.env -> list FunSyntax.exp -> list Value -> Prop :=
| Eval_Nil : forall env,
  funs; env |-- [] ---> []
| Eval_Cons : forall env exp1 v exp2 exps vs,
  forall
    (EVAL_HEAD : funs; env |-- [exp1] ---> [v])
    (EVAL_TAIL : funs; env |-- (exp2 :: exps) ---> vs),
  funs; env |-- (exp1 :: exp2 :: exps) ---> (v :: vs)
| Eval_Const : forall env n,
  funs; env |-- [FunSyntax.Const n] ---> [Num n]
| Eval_Var : forall env n v,
  forall
  (ENV_LOOKUP : FEnv.lookup env n = Some v),
  funs; env |-- [FunSyntax.Var n] ---> [v]
| Eval_Op : forall env exps vs op v,
  forall
    (EVAL_ARGS : funs; env |-- exps ---> vs)
    (EVAL_OP : eval_op op vs = Res v),
  funs; env |-- [FunSyntax.Op op exps] ---> [v]
| Eval_Let : forall env exp1 exp2 v1 n v2,
  forall
    (EVAL_RHS : funs; env |-- [exp1] ---> [v1])
    (EVAL_RES : funs; (FEnv.insert (n, Some v1) env) |-- [exp2] ---> [v2]),
  funs; env |-- [FunSyntax.Let n exp1 exp2] ---> [v2]
| Eval_If : forall env exps vs test b expt expf v,
  forall
    (EVAL_COND : funs; env |-- exps ---> vs)
    (TAKE_BRANCH : take_branch test vs = Res b)
    (EVAL_RES : funs; env |-- [if b then expt else expf] ---> [v]),
  funs; env |-- [FunSyntax.If test exps expt expf] ---> [v]
| Eval_Call : forall env exps vs fname v new_env body,
  forall
    (EVAL_ARGS : funs; env |--exps ---> vs)
    (ENV_BODY : env_and_body fname vs funs = Some (new_env, body))
    (EVAL_BODY : funs; new_env |-- [body] ---> [v]),
  funs; env |-- [FunSyntax.Call fname exps] ---> [v]
where "funs ; env '|--' es '--->' vs " := (eval funs env es vs).

Inductive eval_app (funs: defunEnv) : name -> list Value -> Value -> Prop :=
| App_intro : forall fname vs v new_env body,
  env_and_body fname vs funs = Some (new_env, body) ->
  funs; new_env |-- [body] ---> [v] ->
  eval_app funs fname vs v.

Theorem Eval_Call_thm :
  forall funs env exps vs fname v,
  funs; env |-- exps ---> vs ->
  eval_app funs fname vs v ->
  funs; env |-- [FunSyntax.Call fname exps] ---> [v].
Proof.
  intros funs env exps vs fname v H_eval_args H_app.
  inversion H_app; subst.
  eapply Eval_Call; eauto.
Qed.
