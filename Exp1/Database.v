From Stdlib Require Import List.
Import ListNotations.
From Trocq Require Import Trocq.
From BootstrapExp.utils Require Import Core.
From BootstrapExp.functional Require Import FunEnv FunValues FunSyntax FunSemantics FunProperties.

Definition Rdlet00 A A' (HA: Param00.Rel A A') B B' (HB: Param00.Rel B B')
  a a' (Ha: HA a a') f f' (Hf: forall a a', HA a a' -> HB (f a) (f' a')):
  HB (dlet a f) (dlet a' f').
Proof.
  unfold dlet. apply Hf; assumption.
Qed.

Trocq Use Rdlet00.

Definition sigT_rel A A' (RA: A -> A' -> Type) P P' (RP: forall a a', RA a a' -> P a -> P' a' -> Type)
  (p: sigT P) (p': sigT P') : Type :=
  sigT (fun (Ra: RA (projT1 p) (projT1 p')) => RP _ _ Ra (projT2 p) (projT2 p')).

Definition sigT_rmap A A' (RA: Param02a.Rel A A') P P' (RP: forall a a', RA a a' -> Param01.Rel (P a) (P' a'))
  (p: sigT P') : sigT P :=
  existT P (comap RA (projT1 p)) (comap (RP _ (projT1 p) (comap_in_R _ _ _ eq_refl)) (projT2 p)).

Definition sigT_coHas1 A A' (RA: Param02a.Rel A A') P P' (RP: forall a a', RA a a' -> Param01.Rel (P a) (P' a')):
  Map1.Has (sym_rel (sigT_rel A A' RA P P' RP)) := Map1.BuildHas _ _ _ (sigT_rmap A A' RA P P' RP).

Definition sigT01  A A' (RA: Param02a.Rel A A') P P' (RP: forall a a', RA a a' -> Param01.Rel (P a) (P' a')):
  Param01.Rel (sigT P) (sigT P') := 
  Param01.BuildRel _ _ (sigT_rel A A' RA P P' RP) (Map0.BuildHas _ _ _) (sigT_coHas1 A A' RA P P' RP).

Trocq Use sigT01.

Definition Rref_rel_tmp (funs: defunEnv) (env: FEnv.env) (A: Type) `{Refinable A} (a: A) e : Type :=
  funs & env |-- [e] ---> [encode a].

Definition Rref_tmp (funs: defunEnv) (env: FEnv.env) (A: Type) `{Refinable A} : Param00.Rel A exp :=
  Param00.BuildRel A exp (Rref_rel_tmp funs env A) (Map0.BuildHas _ _ _) (Map0.BuildHas _ _ _).

Definition O_exp := Const 0.

Lemma Eval_eq_O_exp funs env vs : funs & env |-- [O_exp] ---> vs <-> vs = [Num 0].
Proof.
  unfold O_exp. apply Eval_eq_Const.
Qed.

Definition R0N_tmp funs env : Rref_tmp funs env N 0 O_exp.
Proof.
  apply Eval_eq_Const. reflexivity.
Qed.

Definition R0nat_tmp funs env : Rref_tmp funs env nat 0%nat O_exp.
Proof.
  apply Eval_eq_Const. reflexivity.
Qed.

Definition plus_exp (e e': exp) := Op Add [e; e'].

Lemma Eval_eq_plus_exp funs env e e' vs :
  funs & env |-- [plus_exp e e'] ---> vs <->
    exists n m, funs & env |-- [e] ---> [Num n] /\ funs & env |-- [e'] ---> [Num m] /\ vs = [Num (n + m)].
Proof.
  unfold plus_exp. rewrite Eval_eq_Op.
  split.
  - intros [vs' [v [? [Heval Heval_op]]]]. subst. apply Eval_eq_Cons in Heval as [v' [vs [? [He He']]]]. subst.
    simpl in *. destruct v' as [|n], vs as [|[|m] []]; try discriminate. inversion Heval_op. subst. clear Heval_op.
    exists n, m. intuition.
  - intros [n [m [He [He' Heq]]]]. subst. eexists [Num n; Num m], _. intuition auto.
    apply Eval_eq_Cons. eexists _, _; intuition.
Qed.

Definition RplusN_tmp funs env n e (H: Rref_tmp funs env N n e) m e' (H': Rref_tmp funs env N m e') :
  Rref_tmp funs env N (n + m) (plus_exp e e').
Proof.
  apply Eval_eq_plus_exp. eexists _, _. (intuition auto); assumption.
Qed.

Definition Rplusnat_tmp funs env n e (H: Rref_tmp funs env nat n e) m e' (H': Rref_tmp funs env nat m e') :
  Rref_rel_tmp funs env nat (n + m)%nat (plus_exp e e').
Proof.
  unfold Rref_rel_tmp. simpl. rewrite Nnat.Nat2N.inj_add. apply RplusN_tmp; auto.
Qed.

Definition S_exp (e: exp) := plus_exp (Const 1) e.

Lemma Eval_eq_S_exp funs env e vs : 
  funs & env |-- [S_exp e] ---> vs <-> 
    exists n, funs & env |-- [e] ---> [Num n] /\ vs = [Num (N.succ n)].
Proof.
  unfold S_exp. rewrite Eval_eq_plus_exp. split.
  - intros [n [m [H1 [He ?]]]]. subst. exists m. apply Eval_eq_Const in H1. inversion H1. split; auto.
    do 2 f_equal. apply N.add_1_l.
  - intros [n [He ?]]. subst. exists 1, n. intuition.
    + apply Eval_eq_Const. auto.
    + do 2 f_equal. symmetry. apply N.add_1_l.
Qed.

Definition RsuccN_tmp funs env n e (H: Rref_tmp funs env N n e):
  Rref_tmp funs env N (N.succ n) (S_exp e).
Proof.
  apply Eval_eq_S_exp. exists n. split; auto.
Qed.

Definition RSnat_tmp funs env n e (H: Rref_tmp funs env nat n e):
  Rref_tmp funs env nat (S n) (S_exp e).
Proof.
  unfold Rref_tmp, rel. change (funs & env |-- [S_exp e] ---> [Num (N.of_nat (S n))]). rewrite Nnat.Nat2N.inj_succ.
  apply RsuccN_tmp; auto.
Qed.

Definition sub_exp (e e': exp) := Op Sub [e; e'].

Definition RsubN_tmp funs env n e (H: Rref_tmp funs env N n e) m e' (H': Rref_tmp funs env N m e') :
  Rref_tmp funs env N (n - m) (sub_exp e e').
Proof.
  apply Eval_eq_Op. eexists [encode n; encode m], _. split; eauto. simpl. split; auto.
  apply Eval_eq_Cons. eexists _, _. auto.
Qed.

Definition Rsubnat_tmp funs env n e (H: Rref_tmp funs env nat n e) m e' (H': Rref_tmp funs env nat m e') :
  Rref_rel_tmp funs env nat (n - m)%nat (sub_exp e e').
Proof.
  unfold Rref_rel_tmp. simpl. rewrite Nnat.Nat2N.inj_sub. apply RsubN_tmp; auto.
Qed.

Definition mul_exp (e e': exp) := Op Mul [e; e'].

Definition RmulN_tmp funs env n e (H: Rref_tmp funs env N n e) m e' (H': Rref_tmp funs env N m e') :
  Rref_tmp funs env N (n * m) (mul_exp e e').
Proof.
  apply Eval_eq_Op. eexists [encode n; encode m], _. split; eauto. simpl. split; auto.
  apply Eval_eq_Cons. eexists _, _. auto.
Qed.

Definition Rmulnat_tmp funs env n e (H: Rref_tmp funs env nat n e) m e' (H': Rref_tmp funs env nat m e') :
  Rref_rel_tmp funs env nat (n * m)%nat (mul_exp e e').
Proof.
  unfold Rref_rel_tmp. simpl. rewrite Nnat.Nat2N.inj_mul. apply RmulN_tmp; auto.
Qed.

Definition div_exp (e e': exp) := If Equal [e'; Const 0] (Const 0) (Op Div [e; e']).

Definition RdivN_tmp funs env n e (H: Rref_tmp funs env N n e) m e' (H': Rref_tmp funs env N m e') :
  Rref_tmp funs env N (n / m) (div_exp e e').
Proof.
  apply Eval_eq_If. simpl. eexists [encode m; _], _, _. split; auto. simpl. split; eauto using Eval_eq_Cons.
  { apply Eval_eq_Cons. eexists _, _. split; auto. split; auto. apply Eval_eq_Const. auto. } simpl. split; auto.
  pose proof (Heq := N.eqb_spec m 0). destruct (m =? 0) eqn: etest; inversion_clear Heq; subst.
  { apply Eval_eq_Const. simpl. repeat f_equal. apply N.div_0_r. }
  apply Eval_eq_Op. eexists [encode n; encode m], _. split; eauto. simpl. rewrite etest. split; auto.
  apply Eval_eq_Cons. eexists _, _. auto.
Qed.

Definition Rdivnat_tmp funs env n e (H: Rref_tmp funs env nat n e) m e' (H': Rref_tmp funs env nat m e') :
  Rref_rel_tmp funs env nat (n / m)%nat (div_exp e e').
Proof.
  unfold Rref_rel_tmp. simpl. rewrite Nnat.Nat2N.inj_div. apply RdivN_tmp; auto.
Qed.

Definition Rnil_tmp {A} `{Refinable A} funs env : Rref_tmp funs env (list A) [] O_exp.
Proof.
  apply Eval_eq_Const. reflexivity.
Qed.

Definition cons_exp (e e': exp) : exp := Op Cons [e; e'].

Definition Rcons_tmp {A} `{Refinable A} funs env a e `(Rref_tmp funs env A a e) l e' 
  `(Rref_tmp funs env (list A) l e') : Rref_tmp funs env (list A) (a::l) (cons_exp e e').
Proof.
  apply Eval_eq_Op. simpl. eexists [encode a; encode l], _. intuition auto.
  apply Eval_eq_Cons. eexists _, _. auto.
Qed.

Definition hd_exp e' e := If Equal [e; Const 0] e' (Op Head [e]).

Definition Rhd_tmp {A} `{Refinable A} funs env a e `(Rref_tmp funs env A a e) l e' 
  `(Rref_tmp funs env (list A) l e') : Rref_tmp funs env A (hd a l) (hd_exp e e').
Proof.
  apply Eval_eq_If. simpl. eexists [encode l; _], (list_isk_nil _ l), _. split; auto. split; eauto using Eval_eq_Cons.
  { apply Eval_eq_Cons. eexists _, _. split; auto. split; auto. apply Eval_eq_Const. auto. } cbn iota. destruct l; simpl;
  split; auto. apply Eval_eq_Op. eauto.
Qed.

Definition tl_exp e := If Equal [e; Const 0] (Const 0) (Op Tail [e]).

Definition Rtl_tmp {A} `{Refinable A} funs env l e `(Rref_tmp funs env (list A) l e) : 
  Rref_tmp funs env (list A) (tl l) (tl_exp e).
Proof.
  apply Eval_eq_If. simpl. eexists [encode l; _], (list_isk_nil _ l), _. split; auto.
  split; eauto using Eval_eq_Cons.
  { apply Eval_eq_Cons. eexists _, _. split; auto. split; auto. apply Eval_eq_Const. auto. } cbn iota. destruct l; simpl;
    split; auto. { apply Eval_eq_Const. auto. }
  apply Eval_eq_Op. eauto.
Qed.

Definition Rexp_rel_tmp funs env e e' : Type :=
  forall v, funs & env |-- [e] ---> [v] <-> funs & env |-- [e'] ---> [v].

Definition Rexp_comap_in_R_tmp funs env (e': exp) (e: exp) : e' = e -> Rexp_rel_tmp funs env e e' := 
  fun H _ => match H with eq_refl => iff_refl _ end.

Definition Rexp_tmp funs env : Param02a.Rel exp exp :=
  Param02a.BuildRel _ _ (Rexp_rel_tmp funs env) (Map0.BuildHas _ _ _) 
    (Map2a.BuildHas _ _ _ (fun e => e) (Rexp_comap_in_R_tmp funs env)).

Definition exp_rel_term_tmp funs env e e' : Type :=
  exists v, funs & env |-- [e] ---> [v] /\ funs & env |-- [e'] ---> [v].

Definition exp_rel_term_Rexp_rel funs env e e' : exp_rel_term_tmp funs env e e' -> Rexp_rel_tmp funs env e e'.
  intros H v'.
  refine (match H with ex_intro _ v (conj He He') => conj _ _ end).
  - intro Hv'. refine (match Eval_deterministic funs [e] env [v] He [v'] Hv' with eq_refl => He' end).
  - intro Hv'. refine (match Eval_deterministic funs [e'] env [v] He' [v'] Hv' with eq_refl => He end).
Defined.

Definition Rref_rmap funs env {A} `{Refinable A} (a: A) (res: exp) (Ha: Rref_tmp funs env A a res)
  (e e': exp) (He: Rexp_tmp funs env e e') (Hres : exp_rel_term_tmp funs env res e') : Rref_tmp funs env A a e.
refine (proj2 (He (encode a)) _).
refine (proj1 _ Ha).
refine (exp_rel_term_Rexp_rel funs env _ _ Hres _).
Defined.

Definition Rref_tmp01 funs env {A} `{Refinable A} (a: A) (res: exp) (Ha: Rref_tmp funs env A a res)
  (e e': exp) (He: Rexp_tmp funs env e e') : Param01.Rel (Rref_rel_tmp funs env A a e) (exp_rel_term_tmp funs env res e')
  := mkParam01 (Rref_rmap funs env a res Ha e e' He).

Module Demos.

  Module Simple.
    
    Definition f1 : nat := 
      let/d n := 2%nat in
      (n + 1)%nat.
    
    Definition funs: defunEnv := [].
    Definition env := FEnv.empty.

    Definition nat_rel : nat -> exp -> Type := Rref_rel_tmp funs env nat.

    Definition Rnat : Param00.Rel nat exp := Rref_tmp funs env nat.

    Definition R0nat : Rnat 0%nat O_exp := R0nat_tmp funs env.
    Definition RSnat : forall n e, Rnat n e -> Rnat (S n) (S_exp e) := RSnat_tmp funs env.
    Definition Rplusnat : forall n e, Rnat n e -> forall m e', Rnat m e' -> Rnat (n + m)%nat (plus_exp e e') :=
      Rplusnat_tmp funs env.

    Definition exp_rel : exp -> exp -> Type := Rexp_rel_tmp funs env.

    Definition Rexp : Param02a.Rel exp exp := Rexp_tmp funs env.

    Definition exp_rel_term : exp -> exp -> Type := exp_rel_term_tmp funs env.

    Definition Rnat01 : 
      forall n res, Rnat n res -> forall e e', Rexp e e' -> Param01.Rel (nat_rel n e) (exp_rel_term res e') :=
      Rref_tmp01 funs env.

    Trocq Use Rnat R0nat RSnat Rplusnat.
    Trocq Use Rexp Rnat01.

    Set Universe Polymorphism.

    Definition f1_derived : sigT (nat_rel f1).
      unfold f1. trocq.
      exists (Let 0 (Const 2) (plus_exp (Var 0) (Const 1))).
      eexists.
      split.
      - simpl. apply Eval_eq_plus_exp. eexists _, _. intuition auto.
        + apply Eval_eq_S_exp. eexists. intuition auto. apply Eval_eq_S_exp. eexists. intuition auto.
          apply Eval_eq_O_exp. auto.
        + apply Eval_eq_S_exp. eexists. intuition auto. apply Eval_eq_O_exp. auto.
      - apply Eval_eq_Let. eexists _, _. intuition auto.
        +  apply Eval_eq_Const. auto.
        + apply Eval_eq_plus_exp. eexists _, _. split; [|split].
          * apply Eval_eq_Var. eexists. split; auto. reflexivity.
          * apply Eval_eq_Const. auto.
          * reflexivity.
    Defined.
    
    Definition f1_prog := Eval compute in (projT1 f1_derived).
    Definition f1_res : nat_rel f1 f1_prog := projT2 f1_derived.

  End Simple.
    
End Demos.
