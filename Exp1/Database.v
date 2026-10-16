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

Lemma Eval_eq_sub_exp funs env e e' vs :
  funs & env |-- [sub_exp e e'] ---> vs <->
    exists n m, funs & env |-- [e] ---> [Num n] /\ funs & env |-- [e'] ---> [Num m] /\ vs = [Num (n - m)].
Proof.
  unfold sub_exp. rewrite Eval_eq_Op.
  split.
  - intros [vs' [v [? [Heval Heval_op]]]]. subst. apply Eval_eq_Cons in Heval as [v' [vs [? [He He']]]]. subst.
    simpl in *. destruct v' as [|n], vs as [|[|m] []]; try discriminate. inversion Heval_op. subst. clear Heval_op.
    exists n, m. intuition.
  - intros [n [m [He [He' Heq]]]]. subst. eexists [Num n; Num m], _. intuition auto.
    apply Eval_eq_Cons. eexists _, _; intuition.
Qed.

Definition RsubN_tmp funs env n e (H: Rref_tmp funs env N n e) m e' (H': Rref_tmp funs env N m e') :
  Rref_tmp funs env N (n - m) (sub_exp e e').
Proof.
  apply Eval_eq_sub_exp. eexists _, _. (intuition auto); assumption.
Qed.

Definition Rsubnat_tmp funs env n e (H: Rref_tmp funs env nat n e) m e' (H': Rref_tmp funs env nat m e') :
  Rref_rel_tmp funs env nat (n - m)%nat (sub_exp e e').
Proof.
  unfold Rref_rel_tmp. simpl. rewrite Nnat.Nat2N.inj_sub. apply RsubN_tmp; auto.
Qed.

Definition mul_exp (e e': exp) := Op Mul [e; e'].

Lemma Eval_eq_mul_exp funs env e e' vs :
  funs & env |-- [mul_exp e e'] ---> vs <->
    exists n m, funs & env |-- [e] ---> [Num n] /\ funs & env |-- [e'] ---> [Num m] /\ vs = [Num (n * m)].
Proof.
  unfold mul_exp. rewrite Eval_eq_Op.
  split.
  - intros [vs' [v [? [Heval Heval_op]]]]. subst. apply Eval_eq_Cons in Heval as [v' [vs [? [He He']]]]. subst.
    simpl in *. destruct v' as [|n], vs as [|[|m] []]; try discriminate. inversion Heval_op. subst. clear Heval_op.
    exists n, m. intuition.
  - intros [n [m [He [He' Heq]]]]. subst. eexists [Num n; Num m], _. intuition auto.
    apply Eval_eq_Cons. eexists _, _; intuition.
Qed.

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

  Module NRFunction.

    Definition f_four (n: N) :=
      let/d n2 := n * n in
      n2 * n2.

    Section reify_body.
      
      Context (n: N) (x : name := 0). 
      (* for simplicity of the translation, we chose a specific value for x; otherwise we would need to
         have a procedure to pick a `y` different from x, which would pollute the proof *)
      Definition funs : defunEnv := [].
      Definition env := FEnv.insert_some (x, encode n) FEnv.empty.

      Definition Nrel : N -> exp -> Type := Rref_rel_tmp funs env N.

      Definition RN : Param00.Rel N exp := Rref_tmp funs env N.

      Definition R0N : RN 0 O_exp := R0N_tmp funs env.
      Definition RmulN : forall n e, RN n e -> forall m e', RN m e' -> RN (n * m) (mul_exp e e') :=
        RmulN_tmp funs env.

      Definition var_n : exp := Var x.

      Lemma Eval_eq_var_n vs : funs & env |-- [var_n] ---> vs <-> vs = [Num n].
      Proof.
        split.
        - intro Hvar. apply Eval_eq_Var in Hvar as [v [? Henv]]. subst. f_equal.
          unfold env, FEnv.insert_some in Henv. rewrite FEnv.lookup_insert_eq in Henv. simpl in *. inversion Henv; auto.
        - intro. subst. apply Eval_eq_Var. eexists; split; auto.
      Qed.

      Definition Rn : RN n var_n.
        apply Eval_eq_var_n. auto.
      Qed.

      Definition exp_rel : exp -> exp -> Type := Rexp_rel_tmp funs env.

      Definition Rexp : Param02a.Rel exp exp := Rexp_tmp funs env.

      Definition exp_rel_term : exp -> exp -> Type := exp_rel_term_tmp funs env.

      Definition RN01 : 
        forall n res, RN n res -> forall e e', Rexp e e' -> Param01.Rel (Nrel n e) (exp_rel_term res e') :=
        Rref_tmp01 funs env.

      Trocq Use RN R0N RmulN Rn.
      Trocq Use Rexp RN01.

      Definition f_four_body_derived : sigT (Nrel (f_four n)).
        unfold f_four. trocq.
        exists (Let 1 (mul_exp var_n var_n) (mul_exp (Var 1) (Var 1))).
        pose proof (fun vs => proj2 (Eval_eq_var_n vs)).
        eexists.
        split.
        - simpl. apply Eval_eq_mul_exp. eexists _, _. intuition auto.
          + apply Eval_eq_mul_exp. eexists _, _. intuition auto.
          + apply Eval_eq_mul_exp. eexists _, _. intuition auto.
        - apply Eval_eq_Let. eexists _, _. intuition auto.
          + apply Eval_eq_mul_exp. eexists _, _. intuition auto.
          + apply Eval_eq_mul_exp. eexists _, _. split; [|split].
            * apply Eval_eq_Var. eexists. split; auto. reflexivity.
            * apply Eval_eq_Var. eexists. split; auto. reflexivity.
            * reflexivity.
      Defined.

      Definition f_four_body_prog := Eval compute in projT1 f_four_body_derived.
      Definition f_four_body_spec : Nrel (f_four n) f_four_body_prog := projT2 f_four_body_derived.

    End reify_body.

    Definition f_four_defun : defun :=
      Defun 0 [0] f_four_body_prog.

    Definition funs' := [f_four_defun].

    Lemma eval_app_f_four_defun n : eval_app funs' 0 [encode n] (encode (f_four n)).
    Proof.
      econstructor. { reflexivity. } simpl. apply insert_new_fun; auto.
      apply f_four_body_spec.
    Qed.

  End NRFunction.

  Module RecFunction.

    Fixpoint fact (n: nat) : nat :=
      match n with
      | 0%nat => 1
      | S n => S n * fact n
      end.

    Definition case0 := 1%nat.

    Definition caseS (n: nat) (res: nat) : nat := S n * res.

    Definition fact' : nat -> nat := nat_rect (fun _ => nat) case0 caseS.

    Lemma fact_fact' n : fact n = fact' n.
      unfold fact', case0, caseS. induction n; simpl; f_equal; auto.
    Qed.

    Module Case0Translation.

      Section Case0.

        Context (funs: defunEnv) (env: FEnv.env).
        
        Definition nat_rel : nat -> exp -> Type := Rref_rel_tmp funs env nat.
        
        Definition Rnat : Param00.Rel nat exp := Rref_tmp funs env nat.

        Definition R0nat : Rnat 0%nat O_exp := R0nat_tmp funs env.
        Definition RSnat : forall n e, Rnat n e -> Rnat (S n) (S_exp e) := RSnat_tmp funs env.
        Definition Rplusnat : forall n e, Rnat n e -> forall m e', Rnat m e' -> Rnat (n + m)%nat (plus_exp e e') :=
          Rplusnat_tmp funs env.
        Definition Rmulnat : forall n e, Rnat n e -> forall m e', Rnat m e' -> Rnat (n * m)%nat (mul_exp e e') :=
          Rmulnat_tmp funs env.

        Definition exp_rel : exp -> exp -> Type := Rexp_rel_tmp funs env.

        Definition Rexp : Param02a.Rel exp exp := Rexp_tmp funs env.

        Definition exp_rel_term : exp -> exp -> Type := exp_rel_term_tmp funs env.

        Definition Rnat01 : 
          forall n res, Rnat n res -> forall e e', Rexp e e' -> Param01.Rel (nat_rel n e) (exp_rel_term res e') :=
          Rref_tmp01 funs env.

        Trocq Use Rnat R0nat RSnat Rplusnat Rmulnat.
        Trocq Use Rexp Rnat01.

        Definition case0_derived : sigT (nat_rel case0).
          unfold case0. trocq. exists (Const 1). exists (Num 1). split.
          - apply Eval_eq_S_exp. eexists. split.
            + apply Eval_eq_O_exp. auto.
            + auto.
          - apply Eval_eq_Const. auto.
        Defined.

        Definition case0_prog := Eval compute in projT1 case0_derived.

        Definition case0_spec : nat_rel case0 case0_prog := projT2 case0_derived.

      End Case0.

    End Case0Translation.

    Module CaseSTranslation.

      Section CaseS.

        Context (funs: defunEnv) (env: FEnv.env).
        
        Definition nat_rel : nat -> exp -> Type := Rref_rel_tmp funs env nat.
        
        Context (n: nat) (en: exp) (Hen: nat_rel n en) (res: nat) (eres: exp) (Heres: nat_rel res eres).
        
        Definition Rnat : Param00.Rel nat exp := Rref_tmp funs env nat.

        Definition R0nat : Rnat 0%nat O_exp := R0nat_tmp funs env.
        Definition Rn : Rnat n en := Hen.
        Definition Rres : Rnat res eres := Heres.

        Definition RSnat : forall n e, Rnat n e -> Rnat (S n) (S_exp e) := RSnat_tmp funs env.
        Definition Rplusnat : forall n e, Rnat n e -> forall m e', Rnat m e' -> Rnat (n + m)%nat (plus_exp e e') :=
          Rplusnat_tmp funs env.
        Definition Rmulnat : forall n e, Rnat n e -> forall m e', Rnat m e' -> Rnat (n * m)%nat (mul_exp e e') :=
          Rmulnat_tmp funs env.

        Definition exp_rel : exp -> exp -> Type := Rexp_rel_tmp funs env.

        Definition Rexp : Param02a.Rel exp exp := Rexp_tmp funs env.

        Definition exp_rel_term : exp -> exp -> Type := exp_rel_term_tmp funs env.

        Definition Rnat01 : 
          forall n res, Rnat n res -> forall e e', Rexp e e' -> Param01.Rel (nat_rel n e) (exp_rel_term res e') :=
          Rref_tmp01 funs env.

        Trocq Use Rnat R0nat Rn Rres RSnat Rplusnat Rmulnat.
        Trocq Use Rexp Rnat01.

        Definition caseS_derived : sigT (nat_rel (caseS n res)).
          unfold caseS. trocq. eexists _, _. eenough (e: _) by (exact (conj e e)).
          apply Eval_eq_mul_exp. eexists _, _. split; [|split]; try reflexivity.
          - apply Eval_eq_S_exp. eexists. split; try reflexivity. apply Hen.
          - apply Heres.
        Defined.

        Definition caseS_prog := Eval compute in projT1 caseS_derived.

        Definition caseS_spec : nat_rel (caseS n res) caseS_prog := projT2 caseS_derived.

      End CaseS.

    End CaseSTranslation.

    Definition nat_rect_1arg_translation fun_name arg_name case0_exp caseS_exp :=
        If Equal [Var arg_name; Const 0] case0_exp 
          (Let 0 (sub_exp (Var arg_name) (Const 1)) (caseS_exp (Var 0) (Call fun_name [Var 0]))).

    Lemma encode_nat_rect_1arg_spec {A} `{Refinable A} funs arg_name fun_name (case0: A) case0_exp 
      (caseS: nat -> A -> A) (caseS_exp: exp -> exp -> exp) arg:
        lookup_fun fun_name funs = 
          Some (Defun fun_name [arg_name] (nat_rect_1arg_translation fun_name arg_name case0_exp caseS_exp))
        -> (forall env, Rref_rel_tmp funs env A case0 case0_exp) ->
        (forall env n e x e', Rref_rel_tmp funs env nat n e -> Rref_rel_tmp funs env A x e' -> 
                              Rref_rel_tmp funs env A (caseS n x) (caseS_exp e e')) ->
        eval_app funs fun_name [encode arg] (encode (nat_rect (fun _ => A) case0 caseS arg)).
    Proof.
      intros Hfun Hcase0 HcaseS. induction arg; econstructor.
      1, 3: unfold env_and_body; rewrite Hfun; simpl; reflexivity.
      - simpl. apply Eval_eq_If. eexists _, true, _. intuition auto.
        + apply Eval_eq_Cons. eexists _, _. (intuition auto); [apply Eval_eq_Var | apply Eval_eq_Const]; auto.
          eexists. intuition auto. apply FEnv.lookup_insert_eq.
        + auto.
        + apply Hcase0.
      - simpl. apply Eval_eq_If. eexists _, false, _. intuition auto.
        + apply Eval_eq_Cons. eexists _, _. (intuition auto); [apply Eval_eq_Var | apply Eval_eq_Const]; auto.
          eexists. intuition auto. apply FEnv.lookup_insert_eq.
        + auto.
        + apply  Eval_eq_Let. eexists _, _. intuition; swap 1 2.
          * apply HcaseS. { apply Eval_eq_Var. eexists. intuition eauto. } apply Eval_eq_Call.
            eexists _, _. intuition eauto. apply Eval_eq_Var. eexists; eauto.
          * apply Eval_eq_sub_exp. eexists _, _. intuition.
            -- apply Eval_eq_Var. eexists. intuition auto. apply FEnv.lookup_insert_eq.
            -- apply Eval_eq_Const. auto.
            -- fold (N.of_nat (S arg)). change 1 with (N.succ 0). rewrite Nnat.Nat2N.inj_succ, N.sub_succ, N.sub_0_r.
               auto.
    Qed.

    Definition fact'_derived : 
      sigT (fun def => forall funs n, lookup_fun (defun_name def) funs = Some def -> 
                                      eval_app funs (def_name def) [encode n] (encode (fact' n))).
      eexists (Defun 0 [0] (nat_rect_1arg_translation _ _ _ _)). intros funs n H. unfold fact'.
      eapply encode_nat_rect_1arg_spec; eauto.
      - intro. apply Case0Translation.case0_spec.
      - intros. apply CaseSTranslation.caseS_spec; eauto.
    Defined.
    
    Definition fact_def := Eval compute in projT1 fact'_derived.

    Definition fact'_def_spec : forall funs n,
        lookup_fun (defun_name fact_def) funs = Some fact_def ->
        eval_app funs (def_name fact_def) [encode n] (encode (fact' n)) := projT2 fact'_derived.
    
    Lemma fact_def_spec : forall funs n,
        lookup_fun (defun_name fact_def) funs = Some fact_def ->
        eval_app funs (def_name fact_def) [encode n] (encode (fact n)).
      intros ? ?. rewrite fact_fact'. apply fact'_def_spec.
    Qed.

  End RecFunction.
    
End Demos.
