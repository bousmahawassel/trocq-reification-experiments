From BootstrapExp.utils Require Import Core.
From BootstrapExp.functional Require Import FunSyntax FunSemantics FunValues FunEnv.

Lemma Eval_deterministic funs : forall e env a1v,
  funs; env |-- e ---> a1v ->
  forall a2v,
    funs; env |-- e ---> a2v ->
    a1v = a2v.
Proof.
  induction 1; inversion 1; simpl in *; subst; try congruence.
  - apply IHeval1 in EVAL_HEAD; inversion EVAL_HEAD; subst.
    apply IHeval2 in EVAL_TAIL; inversion EVAL_TAIL; subst.
    reflexivity.
  - apply IHeval in EVAL_ARGS. congruence.
  - apply IHeval1 in EVAL_RHS; inversion EVAL_RHS; subst.
    apply IHeval2 in EVAL_RES; inversion EVAL_RES; subst.
    reflexivity.
  - apply IHeval1 in EVAL_COND; inversion EVAL_COND; subst.
    rewrite TAKE_BRANCH in TAKE_BRANCH0. inversion TAKE_BRANCH0; subst.
    apply IHeval2 in EVAL_RES; inversion EVAL_RES; subst.
    reflexivity.
  - apply IHeval1 in EVAL_ARGS; inversion EVAL_ARGS; subst.
    rewrite ENV_BODY in ENV_BODY0. inversion ENV_BODY0; subst.
    apply IHeval2 in EVAL_BODY; inversion EVAL_BODY; subst.
    reflexivity.
Qed.

Ltac cleanup :=
  repeat match goal with
  | [ H : context[fst ?x] |- _ ] => destruct x; simpl in *
  | [ |- exists _, _ ] => eexists
  | [ |- _ /\ _ ] => split
  | [ H : _ /\ _ |- _ ] => destruct H
  | [ H : exists _, _ |- _ ] => destruct H
  | _ => intros
  | _ => progress subst
  | _ => progress eauto
  | _ => progress simpl in *
  | _ => constructor
  | _ => congruence
  end.

Lemma Call_eq funs: forall fname xs env a1v,
  funs; env |-- [Call fname xs] ---> a1v <->
  exists vs v,
    funs; env |-- xs ---> vs /\
    eval_app funs fname vs v /\ a1v = [v].
Proof.
  repeat split; intros; try inversion H; subst; try constructor.
  all: repeat match goal with
  | [ H : context[fst ?x] |- _ ] => destruct x; simpl in *
  | [ |- exists _, _ ] => eexists
  | [ |- _ /\ _ ] => split
  | [ H : _ /\ _ |- _ ] => destruct H
  | [ H : exists _, _ |- _ ] => destruct H
  | _ => progress subst
  | _ => progress eauto
  | _ => progress simpl in *
  | _ => constructor
  | _ => congruence
  end.
  - eapply App_intro; eauto.
  - inversion H2; inversion H3; inversion H1; subst.
    eapply Eval_Call; eauto.
Qed.

Theorem Eval_eq :
  (forall funs env a1vs, funs; env |-- [] ---> a1vs <-> a1vs = []) /\
  (forall funs y xs x env a1vs,
     funs; env |-- x :: y :: xs ---> a1vs <->
     exists v vs,
       a1vs = v::vs /\
       (funs; env |-- [x] ---> [v]) /\
       (funs; env |-- y :: xs ---> vs)) /\
  (forall funs v env a1vs, funs; env |-- [Const v] ---> a1vs <-> a1vs = [Num v]) /\
  (forall funs n env a1vs,
     funs; env |-- [Var n] ---> a1vs <->
     exists v, a1vs = [v] /\ FEnv.lookup env n = Some v) /\
  (forall funs xs f env a1vs,
     funs; env |-- [Op f xs] ---> a1vs <->
     exists vs v,
       a1vs = [v] /\
       funs; env |-- xs ---> vs /\
       eval_op f vs = Res v) /\
  (forall funs y x n env a1vs,
     funs; env |-- [Let n x y] ---> a1vs <->
     exists v1 v2,
       a1vs = [v2] /\
       funs; env |-- [x] ---> [v1] /\
       funs; (FEnv.insert (n, Some v1) env) |-- [y] ---> [v2]) /\
  (forall funs z y xs test env a1vs,
     funs; env |-- [If test xs y z] ---> a1vs <->
     exists vs b v,
       a1vs = [v] /\
       funs; env |-- xs ---> vs /\
       take_branch test vs = Res b /\
       funs; env |-- [if b then y else z] ---> [v]) /\
  (forall funs xs fname env a1vs,
     funs; env |-- [Call fname xs] ---> a1vs <->
     exists vs v,
       funs; env |-- xs ---> vs /\
       eval_app funs fname vs v /\
       a1vs = [v]).
Proof.
  repeat split; intros; try inversion H; subst; try constructor.
  all: repeat match goal with
  | [ H : context[fst ?x] |- _ ] => destruct x; simpl in *
  | [ |- exists _, _ ] => eexists
  | [ |- _ /\ _ ] => split
  | [ H : _ /\ _ |- _ ] => destruct H
  | [ H : exists _, _ |- _ ] => destruct H
  | [ H : (_, _) = _ |- _ ] => inversion H; subst
  | _ => progress subst
  | _ => progress eauto
  | _ => progress simpl in *
  | _ => constructor
  | _ => congruence
  end.
  (*- eapply Eval_Cons; eauto.
  - rewrite H1 in H2; inversion H2; subst.
    eapply Eval_Var; eauto.*)
  - eapply Eval_Op; inversion H0; eauto.
  - eapply Eval_Let; inversion H0; eauto.
  - eapply Eval_If; inversion H0; eauto.
  - eapply App_intro; eauto.
  - inversion H2; subst.
    eapply (Call_eq funs fname xs env [x0]).
    eexists _, _; eauto.
Qed.

Lemma Eval_eq_Nil funs : forall env a1v, funs; env |-- [] ---> a1v <-> a1v = [].
Proof.
  edestruct Eval_eq; eauto.
Qed.

Lemma Eval_eq_Cons funs : forall y xs x env a1v,
  funs; env |-- x :: y :: xs ---> a1v <->
  exists v vs,
    a1v = v::vs /\
    (funs; env |-- [x] ---> [v]) /\
    (funs; env |-- y :: xs ---> vs).
Proof.
  apply Eval_eq.
Qed.

Lemma Eval_eq_Const funs : forall v env a1v,
  funs; env |-- [Const v] ---> a1v <-> a1v = [Num v].
Proof.
  apply Eval_eq.
Qed.

Lemma Eval_eq_Var : forall funs n env a1vs,
     funs; env |-- [Var n] ---> a1vs <->
     exists v, a1vs = [v] /\ FEnv.lookup env n = Some v.
Proof.
  apply Eval_eq.
Qed.

Lemma Eval_eq_Op : forall funs xs f env a1vs,
     funs; env |-- [Op f xs] ---> a1vs <->
     exists vs v,
       a1vs = [v] /\
       funs; env |-- xs ---> vs /\
       eval_op f vs = Res v.
Proof.
  apply Eval_eq.
Qed.

Lemma Eval_eq_Let : forall funs y x n env a1vs,
     funs; env |-- [Let n x y] ---> a1vs <->
     exists v1 v2,
       a1vs = [v2] /\
       funs; env |-- [x] ---> [v1] /\
       funs; (FEnv.insert (n, Some v1) env) |-- [y] ---> [v2].
Proof.
  apply Eval_eq.
Qed.

Lemma Eval_eq_If : forall funs z y xs test env a1vs,
     funs; env |-- [If test xs y z] ---> a1vs <->
     exists vs b v,
       a1vs = [v] /\
       funs; env |-- xs ---> vs /\
       take_branch test vs = Res b /\
       funs; env |-- [if b then y else z] ---> [v].
Proof.
  apply Eval_eq.
Qed.

Lemma Eval_eq_Call : forall funs xs fname env a1vs,
     funs; env |-- [Call fname xs] ---> a1vs <->
     exists vs v,
       funs; env |-- xs ---> vs /\
       eval_app funs fname vs v /\
       a1vs = [v].
Proof.
  apply Eval_eq.
Qed.

Fixpoint free_vars (e : exp) : list name :=
  match e with
  | Const _ => []
  | Var n => [n]
  | Op _ xs => flat_map free_vars xs
  | Let n x y => free_vars x ++ remove N.eq_dec n (free_vars y)
  | If _ xs y z => flat_map free_vars xs ++ free_vars y ++ free_vars z
  | Call _ xs => flat_map free_vars xs
  end.

Lemma not_In_app :
  forall {A : Type} (n : A) (xs ys : list A),
    ~ In n (xs ++ ys) <-> ~ In n xs /\ ~ In n ys.
Proof.
  intros.
  rewrite in_app_iff.
  tauto.
Qed.

Lemma in_remove_rw :
  forall {A : Type} {eq_dec : forall (x y : A), {x = y} + {x <> y}}
    (n : A) (n0 : A) (xs : list A),
  In n (remove eq_dec n0 xs) <-> In n xs /\ n <> n0.
Proof.
  intros; split.
  - apply in_remove.
  - intros; destruct H.
    apply in_in_remove; auto.
Qed.

Theorem delete_env_update :
  forall funs env xs vs n x,
   funs; env |-- xs ---> vs ->
    ~ In n (flat_map free_vars xs) ->
    funs; (FEnv.insert (n, x) env) |-- xs ---> vs.
Proof.
  intros funs env xs vs n x H Hnotin.
  induction H; subst; simpl flat_map in *.
  - constructor; auto.
  - econstructor; eauto.
    + eapply IHeval1; eauto.
      rewrite app_nil_r.
      repeat rewrite not_In_app in Hnotin; destruct Hnotin; auto.
    + eapply IHeval2; eauto.
      rewrite not_In_app in Hnotin; destruct Hnotin; auto.
  - econstructor; eauto.
  - econstructor; eauto.
    unfold In in Hnotin; simpl in Hnotin.
    destruct (N.eq_dec n n0); subst; [tauto|].
    rewrite FEnv.lookup_insert_neq; eauto.
  - econstructor; eauto.
    eapply IHeval; eauto.
    rewrite app_nil_r in Hnotin; assumption.
  - rewrite app_nil_r in *.
    rewrite not_In_app in *; destruct Hnotin.
    econstructor; eauto.
    rewrite in_remove_rw in H2.
    destruct (N.eq_dec n n0); subst.
    + rewrite FEnv.insert_insert_eq in *.
      assumption.
    + assert (~ In n (free_vars exp2)) by tauto.
      specialize IHeval2 with (1 := H3).
      rewrite FEnv.insert_insert_neq; auto.
  - rewrite app_nil_r in *.
    repeat rewrite not_In_app in *; destruct Hnotin; destruct H2.
    econstructor; eauto.
    eapply IHeval2; eauto.
    destruct b; eauto.
  - rewrite app_nil_r in *.
    econstructor; eauto.
Qed.

Theorem remove_env_update :
  forall funs n x0 env v res,
  ~ In n (free_vars x0) ->
  funs; (FEnv.insert (n, v) env) |-- [x0] ---> res <-> funs; env |-- [x0] ---> res.
Proof.
  intros funs n x0 env v res Hnotin.
  split; intros H.
  - eapply delete_env_update with (n := n) (x := FEnv.lookup env n) in H; eauto.
    2: unfold flat_map in *; rewrite app_nil_r; assumption.
    rewrite FEnv.insert_insert_eq in H.
    assert (FEnv.insert (n, FEnv.lookup env n) env = env).
    2: rewrite <- H0; assumption.
    apply FEnv.insert_lookup_self.
  - eapply delete_env_update; eauto.
    unfold flat_map.
    rewrite app_nil_r.
    assumption.
Qed.
