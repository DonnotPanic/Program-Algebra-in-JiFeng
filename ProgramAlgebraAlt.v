Require Import Streams List.
Import ListNotations.
Module ProgramAlgebraAlt.

Class UserParams : Type := {
  Var : Type;
  GLOBVARS : list Var;
  eqb: Var -> Var -> bool;
  Constraint : Prop;
}.

Declare Scope alg_scope.
Open Scope alg_scope.

Section Assign.
  Context {UserVar : UserParams}.
  Definition Exp := (list Var) -> (list Var).

  Record Assign := makeAssign {
    ids : (list Var);
    values : Exp;
  }.

  Definition refl_exp : Exp := (fun x => x).

  Definition empty_assn : Assign :=
    makeAssign GLOBVARS refl_exp.
End Assign.

Section Bool.
  Context {UserVar : UserParams}.
  Definition Boolexp : Type := (list Var) -> bool.
  Definition true_stat : Boolexp := (fun x => true).
  Definition false_stat : Boolexp := (fun x => false).
End Bool.

Section alg.
  Context {UserVar : UserParams}.
  Inductive Atomic : Type :=
  | Chaos : Atomic
  | Assn : Assign -> Atomic.

  Inductive Attach : Type :=
  | Seq : Attach
  | UDC : Attach
  | CDC : Boolexp -> Attach.
  Print Typing Flags.
  Inductive Alg : Type :=
  | Lift : Atomic -> Alg
  | Comb : Attach -> Alg -> Alg -> Alg.

  Definition UDCList (l : list Alg) : Alg :=
    match l with
    | [] => Lift (Assn empty_assn)
    | h :: tl => fold_left (fun a b => (Comb UDC a b)) tl h
    end.
End alg.

Section rwtrel.
  Context {UserVar : UserParams}.
  Inductive rwtrel (a : Alg) : Alg -> Prop :=
    | rwt_refl : rwtrel a a
    | rwt_trans : forall (b c : Alg), rwtrel a b ->
      rwtrel b c -> rwtrel a c.
  Axiom rwt_comm : forall (a b : Alg), rwtrel a b -> rwtrel b a.
  Axiom rwt_comb : forall (a b c d : Alg) (e : Attach), rwtrel a b ->
      rwtrel c d -> rwtrel (Comb e a c) (Comb e b d).
End rwtrel.

Notation "var :== exp" := (makeAssign var exp)(at level 51) : alg_scope.
Notation "@{ e }" := (Lift (Assn e)) (at level 10): alg_scope.
Notation "_|_" := (Lift Chaos)(at level 10) : alg_scope.
Notation "a <--> b" := (rwtrel a b) (at level 20, left associativity) : alg_scope.
Notation "p <| b |> q" := (Comb (CDC b) p q) (at level 15): alg_scope.
Notation "p ;; q" := (Comb Seq p q)(at level 14, left associativity): alg_scope.
Notation "p /-\ q" := (Comb UDC p q)(at level 13, left associativity): alg_scope.
Notation "var :== exp" := (makeAssign var exp)(at level 51): alg_scope.
Notation "|-| l" := (UDCList l)(at level 10): alg_scope.

Section Fact.
  Context {UserVar : UserParams}.

  (* LAW *)
  (** Law A.1 *)
  (** Law A.1.1 *)
  Axiom Chaos_zero_Choice_l : forall (p : Alg), ((_|_) /-\ p) <--> _|_.
  Axiom Chaos_zero_Seq_l : forall (p : Alg), ((_|_) ;; p) <--> _|_.
  Axiom Chaos_zero_Seq_r : forall (p : Alg), (p ;; (_|_)) <--> _|_.

  (** Law A.1.2 *)
  Axiom Choice_comm : forall (p q : Alg), (p /-\ q) <--> (q /-\ p).
  Theorem Chaos_zero_Choice_r : forall (p : Alg), (p /-\ (_|_)) <--> _|_.
  Proof. intros. apply (rwt_trans _ ((_|_) /-\ p)). apply Choice_comm.
   apply Chaos_zero_Choice_l. Qed.
  Axiom Choice_assoc : forall (p q r : Alg),
   ((p /-\ q) /-\ r) <--> (p /-\ (q /-\ r)).

  (** Law A.1.3 *)
  Axiom Cond_rev : forall (p q : Alg) (b : Boolexp),
    (p <| b |> q) <--> (q <| (fun g => negb (b g)) |> p).

  (** Law A.1.4 *)
  Axiom Seq_assoc : forall (p q r : Alg), 
    ((p ;; q) ;; r) <--> (p ;; (q ;; r)).

  (** Law A.2 *)
  (** Law A.2.1 *)
  Fixpoint lookup_help (a: Var) (vs rs: (list Var)) : Var :=
  match vs, rs with
  | _, [] => a
  | [], _ => a
  | v::vl, r::rl => if (eqb a v) then r else lookup_help a vl rl
  end.
  Fixpoint extends_mapping_help (us rs k : (list Var)) : (list Var) :=
    match k with
    | [] => []
    | v::vl => lookup_help v us rs :: extends_mapping_help us rs vl
    end.
  Definition extends_mapping (us : (list Var)) (m : (list Var) -> (list Var)) :=
   fun k => (extends_mapping_help us (m us) k).
  Definition extends_assign (v : Assign) :=
     makeAssign
       GLOBVARS
       (extends_mapping v.(ids) v.(values)).
  Axiom Assign_extends : forall (v : Assign),
   @{v} <--> @{extends_assign v}.

  (** Law A.2.2 *)
  Axiom Assign_Seq : forall (v : list Var) (g h : Exp),
    @{v :== g} ;; @{v :== h} <--> @{v :== (fun x => h (g x))}.

  (** Law A.2.3 *)
  Definition exp_Cond (g h : Exp) b : Exp :=
   fun x =>
     match (b x) with
     | true => g x
     | false => h x
     end.

  Axiom Assign_Cond : forall (v : (list Var)) (g h : Exp) (b : Boolexp) ,
    @{v :== g} <| b |> @{v :== h} <--> @{ v :== exp_Cond g h b }.

  (** Law A.2.4 *)
  Axiom Assign_to_NF : forall (v : (list Var)) (e : Exp),
    @{v :== e} <--> (_|_) <| false_stat |> (|-| [@{v :== e}]).
  
  (** Law A.2.5 *)
  Axiom Chaos_to_NF : forall p, (_|_) <--> ((_|_) <| true_stat |> (|-| p)).

  (** TH1 *)

  Definition Total_Assign (a : Assign) := forall x, In x GLOBVARS -> In x a.(ids).
  Theorem Assign_is_Total : forall a : Assign, exists b : Assign, @{a} <--> @{b} /\ Total_Assign b.
  Proof.
    intros. exists (extends_assign a). split.
    - apply Assign_extends.
    - unfold Total_Assign. unfold extends_assign. auto.
  Qed.

  Theorem Assign_elim_Seq : forall (a b: Assign),
       exists (c: Assign), @{a} ;; @{b} <--> @{c} /\ Total_Assign c.
  Proof.
    intros. eexists;split. apply (rwt_trans _ (@{extends_assign a} ;; @{extends_assign b})).
    - apply rwt_comb;apply Assign_extends.
    - unfold extends_assign. apply Assign_Seq.
    - unfold Total_Assign. auto.
  Qed.

  Theorem Assign_elim_Cond : forall (a b: Assign) (d : Boolexp),
       exists (c: Assign), @{a} <| d |> @{b} <--> @{c} /\ Total_Assign c.
  Proof.
    intros. eexists;split. apply (rwt_trans _ (@{extends_assign a} <| d |> @{extends_assign b})).
    - apply rwt_comb;apply Assign_extends.
    - unfold extends_assign. apply Assign_Cond.
    - unfold Total_Assign. auto.
  Qed.

  (** Law A.3 *)
  Definition CH (p : list Alg) : Prop :=
    forall (x : Alg), In x p -> exists y, x <--> @{y} /\ Total_Assign y.

  (** Law A.3.1 *)
  Axiom Choice_distr : forall (a b : list Alg),
    CH a -> CH b -> ((|-| a) /-\ (|-| b)) <--> (|-| (a ++ b)).

  (** Law A.3.2 *)
  Axiom Cond_over_Choice : forall (a b : list Alg) (bexp : Boolexp),
    CH a -> CH b ->
    (|-| a) <| bexp |> (|-| b) <--> |-| (map (fun g => (fst g) <| bexp |> (snd g)) (list_prod a b)).

  (** Law A.3.3 *)
  Axiom Seq_over_Choice : forall (a b : list Alg),
    CH a -> CH b ->
    (|-| a) ;; (|-| b) <--> |-| (map (fun g => (fst g) ;; (snd g)) (list_prod a b)).

  (** Law A.3.4 *)
  Axiom Choice_to_NF : forall (a : list Alg) b,
    CH a -> b GLOBVARS = false ->
    (|-| a) <--> (_|_) <| b |> (|-| a).

  (** TH2 *)
  Lemma CH_elim_Cond : forall (p q : list Alg) (b : Boolexp),
    CH p -> CH q -> exists c, (|-| p <| b |> |-| q) <--> (|-| c) /\ CH c.
  Proof.
    intros. eexists;split. apply Cond_over_Choice;auto.
    unfold CH. intros. apply in_map_iff in H1. do 2 destruct H1.
    destruct x0. apply in_prod_iff in H2. simpl in H1. destruct H2.
    rewrite <- H1. unfold CH in H. apply H in H2. do 2 destruct H2.
    unfold CH in H0. apply H0 in H3. do 2 destruct H3.
    pose (Assign_elim_Cond x0 x1 b). destruct e. destruct H6.
    exists x2;split;auto. apply (rwt_trans _ (@{x0} <| b |> @{x1})).
    apply rwt_comb;auto. auto.
  Qed.

  Lemma CH_elim_Seq : forall (p q : list Alg),
    CH p -> CH q -> exists c, ((|-| p) ;; (|-| q)) <--> (|-| c) /\ CH c.
  Proof.
    intros. eexists;split. apply Seq_over_Choice;auto.
    unfold CH. intros. apply in_map_iff in H1. do 2 destruct H1.
    destruct x0. apply in_prod_iff in H2. simpl in H1. destruct H2.
    rewrite <- H1. unfold CH in H. apply H in H2. do 2 destruct H2.
    unfold CH in H0. apply H0 in H3. do 2 destruct H3.
    pose (Assign_elim_Seq x0 x1). destruct e. destruct H6.
    exists x2;split;auto. apply (rwt_trans _ (@{x0} ;; @{x1})).
    apply rwt_comb;auto. auto.
  Qed.

  Lemma CH_app_rev : forall (l1 l2 : list Alg),
    CH l1 -> CH l2 -> CH (l1 ++ l2).
  Proof.
    intros. unfold CH in *. intros. apply in_app_or in H1. destruct H1.
    - apply H in H1. auto.
    - apply H0 in H1. auto.
  Qed.
  Lemma CH_elim_Choice : forall (p q : list Alg),
    CH p -> CH q -> exists c, ((|-| p) /-\ (|-| q)) <--> (|-| c) /\ CH c.
  Proof.
    intros. exists (p++q). split. apply Choice_distr;auto.
    apply CH_app_rev;auto.
  Qed.

  (** Law A.4 *)
  (** Law A.4.1 *)
  Axiom NF_over_Choice : forall (a b : list Alg) (c d : Boolexp),
    CH a -> CH b ->
    (((_|_) <| c |> (|-| a)) /-\ ((_|_) <| d |> (|-| b))) <-->
    ((_|_) <| (fun g => orb (c g) (d g)) |> ((|-|a) /-\ (|-| b))).

  (** Law A.4.2 *)
  Axiom NF_over_Cond : forall (a b : list Alg) (c d e : Boolexp),
    CH a -> CH b ->
    (((_|_) <| c |> (|-|a)) <| d |> ((_|_) <| e |> (|-| b))) <-->
    ((_|_) <| (fun g => if (d g) then (c g) else (e g)) |> ((|-|a) <| d |> (|-| b))).


  (** Law A.4.3-A.4.4 *)
  Definition Assign_over_Boolexp (b : Boolexp) (a : Alg):=
    match a with
    | Lift y => match y with
                | Assn x => b ((extends_mapping x.(ids) x.(values)) GLOBVARS)
                | _ => false
                end
    | _ => false
    end.
  Definition CH_over_Boolexp (a : list Alg) (b : Boolexp) :=
    fold_left orb (map (Assign_over_Boolexp b) a) true.

  (** Law A.4.5 *)
  Axiom NF_over_Seq : forall (a b : list Alg) (c d : Boolexp),
    CH a -> CH b ->
    (((_|_) <| c |> (|-| a)) ;; ((_|_) <| d |> (|-| b))) <-->
    ((_|_) <| (fun g => orb (c g) (CH_over_Boolexp a d)) |> ((|-| a) ;; (|-| b))).

  (** TH.3 *)
  Definition FNF (P : Alg): Prop :=
    exists bexp R, P = (_|_) <| bexp |> (|-| R) /\ CH R.

  Lemma FNF_elim_Cond : forall (P Q : Alg) (b : Boolexp),
    FNF P -> FNF Q -> exists R, (P <| b |> Q) <--> R /\ FNF R.
  Proof.
    intros. unfold FNF in H. do 3 destruct H.
    unfold FNF in H0. do 3 destruct H0. rewrite H. rewrite H0.
    pose (CH_elim_Cond x0 x2 b). apply e in H2 as H3;auto.
    do 2 destruct H3. exists (_|_ <| fun g => if b g then x g
       else x1 g |> |-| x3). split. apply (rwt_trans _ (_|_ <| fun g =>
       if b g then x g else x1 g |> (|-| x0 <| b |> |-| x2))).
    apply NF_over_Cond;auto. apply rwt_comb;auto. apply rwt_refl.
    unfold FNF. do 2 eexists. eauto.
  Qed.

  Lemma FNF_elim_Choice : forall  (P Q : Alg),
    FNF P -> FNF Q -> exists R, (P /-\ Q) <--> R /\ FNF R.
  Proof.
    intros. unfold FNF in H. do 3 destruct H.
    unfold FNF in H0. do 3 destruct H0. rewrite H. rewrite H0.
    pose (CH_elim_Choice x0 x2). apply e in H2 as H3;auto.
    do 2 destruct H3. exists (_|_ <| (fun g => orb (x g) (x1 g)) |> |-| x3).
    split. apply (rwt_trans _ (_|_ <| (fun g => orb (x g) (x1 g)) |>
       (|-| x0 /-\ |-| x2))).
    apply NF_over_Choice;auto. apply rwt_comb;auto. apply rwt_refl.
    unfold FNF. do 2 eexists. eauto.
  Qed.

  Lemma FNF_elim_Seq : forall (P Q : Alg),
    FNF P -> FNF Q -> exists R, (P ;; Q) <--> R /\ FNF R.
  Proof.
    intros. unfold FNF in H. do 3 destruct H.
    unfold FNF in H0. do 3 destruct H0. rewrite H. rewrite H0.
    pose (CH_elim_Seq x0 x2). apply e in H2 as H3;auto.
    do 2 destruct H3. exists (_|_ <| (fun g => orb (x g) (CH_over_Boolexp x0 x1)) |> |-| x3).
    split. apply (rwt_trans _ (_|_ <| (fun g => orb (x g) (CH_over_Boolexp x0 x1)) |>
       (|-| x0 ;; |-| x2))).
    apply NF_over_Seq;auto. apply rwt_comb;auto. apply rwt_refl.
    unfold FNF. do 2 eexists. eauto.
  Qed.

  Theorem FNF_closure : forall (P : Alg),
    exists Q, P <--> Q /\ FNF Q.
  Proof.
    intros. induction P.
    - destruct a.
      + eexists. split. apply (Chaos_to_NF []);auto.
        unfold FNF. repeat eexists; try contradiction.
      + eexists;split. destruct a. apply Assign_to_NF;auto.
        unfold FNF. do 2 eexists. split. reflexivity. unfold CH.
        intros. destruct H; try contradiction.
        destruct (Assign_is_Total a). destruct H0. exists x0.
        rewrite <- H. auto.
    - destruct IHP1. destruct IHP2. destruct H. destruct H0.
      destruct a.
      + destruct (FNF_elim_Seq x x0) ; auto. destruct H3.
        exists x1. split;auto. apply (rwt_trans _ (x;;x0));auto.
        apply rwt_comb;auto.
      + destruct (FNF_elim_Choice x x0) ; auto. destruct H3.
        exists x1. split;auto. apply (rwt_trans _ (x/-\x0));auto.
        apply rwt_comb;auto.
      + destruct (FNF_elim_Cond x x0 b) ; auto. destruct H3.
        exists x1. split;auto. apply (rwt_trans _ (x<| b |>x0));auto.
        apply rwt_comb;auto.
    Unshelve. destruct H;try contradiction.
  Qed.

  Definition eqEval (x y : Assign) :=
  forall a, In a (x.(values) x.(ids)) -> In a (y.(values) y.(ids)).

  Definition eqAssn (x : Alg) (y : Alg) :=
    match x, y with
    | Lift e, Lift f =>
      match e, f with
      | Assn m, Assn n => eqEval (extends_assign m) (extends_assign n)
      | _,_ => False
      end
    | _, _ => False
    end.

  Definition RefineCH (A : list Alg) (B : list Alg) :=
   forall x, In x B -> exists y , In y A /\ eqAssn x y.

  Definition Refine (P Q : Alg) :=
    exists bexp cexp U V,
     (P = (_|_) <| bexp |> (|-| U) /\ CH U)
    /\ (Q = (_|_) <| cexp |> (|-| V) /\ CH V)
    /\ (Constraint -> ((cexp GLOBVARS = false /\ (RefineCH U V))
      \/ (bexp GLOBVARS = true))).
End Fact.


Section Infty.
  Context {UserVar : UserParams}.
  Variable f : Alg -> Alg.

  Definition AlgStr := Stream Alg.
  CoFixpoint Recur (a : Alg) : AlgStr := Cons a (Recur (f a)).

  Definition FNFPres(P Q : Alg) :=
  exists R S, (P <--> R /\ FNF R) /\ (Q <--> S /\ FNF S) /\ Refine R S.

  Definition AlgPresStep (s : AlgStr) :=
    let h := Streams.hd s in
    let m := Streams.hd (Streams.tl s) in
    FNFPres h m.
  Definition AlgPres := Streams.ForAll AlgPresStep.

  Definition SthStep (a : Alg) (s : AlgStr) :=
    let h := Streams.hd s in
    a <--> h.
  Definition SthExists (a : Alg) := Streams.Exists (SthStep a).

  Lemma AlgPresConst : (forall x, FNFPres x (f x))
     -> forall y, AlgPres (Recur y).
  Proof. intro. unfold AlgPres. cofix Pres.
  intros. apply HereAndFurther.
  - unfold AlgPresStep. simpl. apply H.
  - simpl. apply Pres.
  Qed.

  Lemma AlgPresInd : forall y, FNFPres y (f y) ->
    (forall x, FNFPres (f x) (f (f x))) -> AlgPres (Recur y).
  Proof. intros. apply HereAndFurther. unfold AlgPresStep.
  auto. simpl. generalize y. cofix Pres.
  intros. apply HereAndFurther.
  - unfold AlgPresStep. simpl. apply H0.
  - simpl. apply Pres.
  Qed.

End Infty.

Create HintDb palg.

#[export] Hint Unfold FNF CH Total_Assign : palg.

#[export] Hint Resolve rwt_refl rwt_comm: palg.

Ltac pauto := auto with palg.

End ProgramAlgebraAlt.
