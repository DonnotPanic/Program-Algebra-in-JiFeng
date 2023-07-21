Require Import Streams List.
Import ListNotations.
Module ProgramAlgebra.

Class UserParams : Type := {
  Var : Type;
  GLOBVARS : list Var;
  eqb: Var -> Var -> bool;
  Constraints : Prop;
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
  | Assn : Assign -> Atomic
  | Empty : Atomic.

  Inductive Comp : Type :=
  | Seq : Comp
  | NDC : Comp
  | CDC : Boolexp -> Comp.
  Print Typing Flags.
  Inductive Alg : Type :=
  | Lift : Atomic -> Alg
  | Comb : Comp -> Alg -> Alg -> Alg.

  Definition NDCList (l : list Alg) : Alg :=
    match l with
    | [] => Lift Empty
    | h :: tl => fold_left (fun a b => (Comb NDC a b)) tl h
    end.
End alg.

Section rwtrel.
  Context {UserVar : UserParams}.
  Parameter rwtrel : Alg -> Alg -> Prop.
  Axiom rwt_refl : forall (a: Alg), rwtrel a a.
  Axiom rwt_trans : forall (a b c : Alg), rwtrel a b ->
      rwtrel b c -> rwtrel a c.
  Axiom rwt_comm : forall (a b : Alg), rwtrel a b -> rwtrel b a.
  Axiom rwt_comb : forall (a b c d : Alg) (e : Comp), rwtrel a b ->
      rwtrel c d -> rwtrel (Comb e a c) (Comb e b d).
End rwtrel.

Create HintDb palg.

#[export] Hint Resolve rwt_refl rwt_comm: palg.

Ltac pauto := auto with palg.


Notation "var :== exp" := (makeAssign var exp)(at level 51) : alg_scope.
Notation "@{ e }" := (Lift (Assn e)) (at level 10): alg_scope.
Notation "_|_" := (Lift Chaos)(at level 10) : alg_scope.
Notation "a <--> b" := (rwtrel a b) (at level 20, left associativity) : alg_scope.
Notation "p <| b |> q" := (Comb (CDC b) p q) (at level 15): alg_scope.
Notation "p ;; q" := (Comb Seq p q)(at level 14, left associativity): alg_scope.
Notation "p /-\ q" := (Comb NDC p q)(at level 13, left associativity): alg_scope.
Notation "var :== exp" := (makeAssign var exp)(at level 51): alg_scope.
Notation "|-| l" := (NDCList l)(at level 10): alg_scope.
Notation "-o-" := (Lift Empty)(at level 10): alg_scope.

Section Fact.
  Context {UserVar : UserParams}.

  (* LAW *)
  (** Law A.1 *)
  (** Law A.1.1 *)
  Axiom Chaos_zero_Choice_l : forall (p : Alg), ((_|_) /-\ p) <--> _|_.
  Axiom Chaos_zero_Seq_l : forall (p : Alg), ((_|_) ;; p) <--> _|_.
  Axiom Chaos_zero_Seq_r : forall (p : Alg), (p ;; (_|_)) <--> _|_.
  Axiom Empty_id_Seq_l : forall (p : Alg), ((-o-) ;; p) <--> p.
  Axiom Empty_id_Seq_r : forall (p : Alg), (p ;; (-o-)) <--> p.

  (** Law A.1.2 *)
  Axiom Choice_comm : forall (p q : Alg), (p /-\ q) <--> (q /-\ p).
  Theorem Chaos_zero_Choice_r : forall (p : Alg), (p /-\ (_|_)) <--> _|_.
  Proof. intros. apply (rwt_trans _ ((_|_) /-\ p)). apply Choice_comm.
   apply Chaos_zero_Choice_l. Qed.
  Axiom Choice_assoc : forall (p q r : Alg),
   ((p /-\ q) /-\ r) <--> (p /-\ (q /-\ r)).
  Axiom Choice_id : forall (p : Alg), (p /-\ p) <--> p.
  Axiom Choice_Empty_l : forall (p : Alg), ((-o-) /-\ p) <--> p.
  Theorem Choice_Empty_r : forall (p : Alg), (p /-\ (-o-)) <--> p.
  Proof. intros. apply (rwt_trans _ (Lift Empty /-\ p)). apply Choice_comm.
    apply Choice_Empty_l. Qed.

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
   (fun k => extends_mapping_help us (m us) k).
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

  Axiom Empty_to_NF : (-o-) <--> (_|_) <| false_stat |> (|-| []).
  
  (** Law A.2.5 *)
  Axiom Chaos_to_NF : forall p, p <> [] -> (_|_) <--> ((_|_) <| true_stat |> (|-| p)).

  (** TH1 *)

  Definition Total_Assign (a : Assign) := forall x, In x GLOBVARS -> In x a.(ids).
  Theorem Assign_is_Total : forall a : Assign, exists b : Assign, @{a} <--> @{b} /\ Total_Assign b.
  Proof.
    intros. exists (extends_assign a). split.
    - apply Assign_extends.
    - unfold Total_Assign. unfold extends_assign. auto.
  Qed.

  (** Law A.3 *)
  Definition CH (p : list Alg) : Prop :=
    forall (x : Alg), In x p -> exists y, x = @{y} /\ Total_Assign y.

  (** Law A.3.1 *)
  Theorem Choice_distr : forall (a b : list Alg),
    CH a -> CH b -> ((|-| a) /-\ (|-| b)) <--> (|-| (a ++ b)).
  Proof. intros. generalize b.
    apply (rev_ind (fun b0 => |-| a /-\ |-| b0 <--> |-| (a ++ b0))).
    - simpl. rewrite app_nil_r. apply Choice_Empty_r.
    - intros. assert (forall m, |-| (m ++ [x]) <--> |-| m /-\ x).
      { intros. destruct m. simpl. apply rwt_comm. apply Choice_Empty_l.
        unfold NDCList. simpl. rewrite <- fold_left_rev_right.
        rewrite rev_app_distr. simpl. rewrite fold_left_rev_right.
        apply rwt_refl. }
      apply (rwt_trans _ (|-| a /-\ (|-| l /-\ x))). apply rwt_comb;pauto.
      apply (rwt_trans _ (|-| a /-\ |-| l /-\ x)). apply rwt_comm.
      apply Choice_assoc. apply (rwt_trans _ (|-| (a ++ l) /-\ x)).
      apply rwt_comb;pauto. rewrite app_assoc. apply rwt_comm. auto.
  Qed.

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
  Definition Assign_comb_CDC_help (p q : Assign) (b : Boolexp):=
    p.(ids) :== exp_Cond p.(values) q.(values) b.

  Definition Assign_comb_CDC (p q : Alg) (b : Boolexp) :=
    match p, q with
    | Lift x, Lift y => match x, y with
                        | Assn s, Assn t => @{(Assign_comb_CDC_help
                         (extends_assign s) (extends_assign t) b)}
                        | _, _ => -o-
                        end
    | _, _ => -o-
    end.
  Lemma rwt_ext_Forall : forall A (f g : A -> Alg) (l : list A), Forall (fun x => f x <--> g x) l
    -> |-|(map f l) <--> |-|(map g l).
  Proof. intros A f g. apply (rev_ind (fun l => Forall (fun x : A => f x <--> g x) l ->
    |-| (map f l) <--> |-| (map g l))). intros. pauto. intros.
    assert (Forall (fun x : A => f x <--> g x) l). 
    rewrite Forall_forall in *. intros. assert (In x0 (l ++ [x])). apply in_or_app. 
    auto. apply H0 in H2. auto. apply H in H1 as H2.
    rewrite Forall_forall in *. destruct l. simpl. apply H0. 
    apply in_or_app. right. apply in_eq. simpl.
    repeat rewrite <- fold_left_rev_right. repeat rewrite <- map_rev.
    repeat rewrite rev_unit. repeat rewrite map_cons. simpl.
    apply rwt_comb. repeat rewrite map_rev.
    repeat rewrite fold_left_rev_right. auto. pose (H0 x).
    apply r. apply in_or_app. right. apply in_eq.
  Qed.

  Lemma CH_elim_Cond : forall (p q : list Alg) (b : Boolexp),
    CH p -> CH q -> exists c, (|-| p <| b |> |-| q) <--> (|-| c) /\ CH c.
  Proof.
    intros. exists (map (fun g => Assign_comb_CDC (fst g) (snd g) b) (list_prod p q)).
    split. pose (Cond_over_Choice p q b).
    apply r in H as H1. 2: auto. apply (rwt_trans _ _ _ H1).
    apply rwt_ext_Forall. rewrite Forall_forall. intros.
    clear r H1. destruct x. simpl in *. apply in_prod_iff in H2.
    destruct H2. unfold CH in *. apply H in H1. apply H0 in H2.
    do 2 destruct H1. do 2 destruct H2. rewrite H1. rewrite H2.
    simpl. apply (rwt_trans _ (@{extends_assign x} <| b |> @{extends_assign x0})).
    apply rwt_comb; apply Assign_extends. unfold extends_assign.
    unfold Assign_comb_CDC_help. simpl. apply Assign_Cond.
    unfold CH. intros. apply in_map_iff in H1. do 2 destruct H1.
    destruct x0. apply in_prod_iff in H2. simpl in H1. destruct H2.
    rewrite <- H1. unfold CH in H. apply H in H2. do 2 destruct H2.
    unfold CH in H0. apply H0 in H3. do 2 destruct H3.
    eexists. split. rewrite H2. rewrite H3. simpl. unfold extends_assign.
    unfold Assign_comb_CDC_help. simpl. reflexivity. unfold Total_Assign.
    auto.
  Qed.

  Definition Assign_comb_Seq_help (a b : Assign) :=
    a.(ids) :== fun x => b.(values) (a.(values) x).
  Definition Assign_comb_Seq (a b : Alg) :=
    match a, b with
    | Lift x, Lift y => match x, y with
                        | Assn s, Assn t => @{(Assign_comb_Seq_help
                         (extends_assign s) (extends_assign t))}
                        | _, _ => -o-
                        end
    | _, _ => -o-
    end.
  Lemma CH_elim_Seq : forall (p q : list Alg),
    CH p -> CH q -> exists c, ((|-| p) ;; (|-| q)) <--> (|-| c) /\ CH c.
  Proof.
    intros. exists (map (fun g => Assign_comb_Seq (fst g) (snd g)) (list_prod p q)).
    split. pose (Seq_over_Choice p q).
    apply r in H as H1. 2: auto. apply (rwt_trans _ _ _ H1).
    apply rwt_ext_Forall. rewrite Forall_forall. intros.
    clear r H1. destruct x. simpl in *. apply in_prod_iff in H2.
    destruct H2. unfold CH in *. apply H in H1. apply H0 in H2.
    do 2 destruct H1. do 2 destruct H2. rewrite H1. rewrite H2.
    simpl. apply (rwt_trans _ (@{extends_assign x} ;; @{extends_assign x0})).
    apply rwt_comb; apply Assign_extends. unfold extends_assign.
    unfold Assign_comb_Seq_help. simpl. apply Assign_Seq.
    unfold CH. intros. apply in_map_iff in H1. do 2 destruct H1.
    destruct x0. apply in_prod_iff in H2. simpl in H1. destruct H2.
    rewrite <- H1. unfold CH in H. apply H in H2. do 2 destruct H2.
    unfold CH in H0. apply H0 in H3. do 2 destruct H3.
    eexists. split. rewrite H2. rewrite H3. simpl. unfold extends_assign.
    unfold Assign_comb_Seq_help. simpl. reflexivity. unfold Total_Assign.
    auto.
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
                | Assn x => b (extends_mapping x.(ids) x.(values) GLOBVARS)
                | _ => false
                end
    | _ => false
    end.
  Definition CH_over_Boolexp (a : list Alg) (b : Boolexp) :=
    fold_left orb (map (Assign_over_Boolexp b) a) false.

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
      + eexists. split. apply (Chaos_to_NF [@{empty_assn}]);auto.
        discriminate. unfold FNF. repeat eexists; try contradiction.
        destruct H;try contradiction. rewrite <- e. auto.
        unfold Total_Assign. auto.
      + eexists;split. pose (Assign_extends a). unfold extends_assign in r.
        pose (Assign_to_NF GLOBVARS (extends_mapping (ids a) (values a))).
        apply (rwt_trans _ _ _ r). apply r0.
        unfold FNF. do 2 eexists. split. reflexivity. unfold CH.
        intros. destruct H; try contradiction. rewrite <- H.
        eexists;split;auto. unfold Total_Assign. auto.
      + eexists;split. apply Empty_to_NF;auto. unfold FNF.
        repeat eexists;try contradiction.
    - destruct IHP1. destruct IHP2. destruct H. destruct H0.
      destruct c.
      + destruct (FNF_elim_Seq x x0) ; auto. destruct H3.
        exists x1. split;auto. apply (rwt_trans _ (x;;x0));auto.
        apply rwt_comb;auto.
      + destruct (FNF_elim_Choice x x0) ; auto. destruct H3.
        exists x1. split;auto. apply (rwt_trans _ (x/-\x0));auto.
        apply rwt_comb;auto.
      + destruct (FNF_elim_Cond x x0 b) ; auto. destruct H3.
        exists x1. split;auto. apply (rwt_trans _ (x<| b |>x0));auto.
        apply rwt_comb;auto.
    Unshelve. all : destruct H;try contradiction. 
  Qed.

  Definition subEval (x y : Assign) :=
  forall a, In a (x.(values) x.(ids)) -> In a (y.(values) y.(ids)).

  Definition subAssn (x : Alg) (y : Alg) :=
    match x, y with
    | Lift e, Lift f =>
      match e, f with
      | Assn m, Assn n => subEval m n
      | _,_ => False
      end
    | _, _ => False
    end.

  Definition RefineCH (A : list Alg) (B : list Alg) :=
   forall x, In x B -> exists y , In y A /\ subAssn x y.

  Definition Refine (P Q : Alg) :=
    exists bexp cexp U V,
     (P = (_|_) <| bexp |> (|-| U) /\ CH U)
    /\ (Q = (_|_) <| cexp |> (|-| V) /\ CH V)
    /\ (Constraints -> ((cexp GLOBVARS = false /\ (RefineCH U V))
      \/ (bexp GLOBVARS = true))).
End Fact.

#[export] Hint Unfold FNF CH Total_Assign : palg.

Section NormalForm.
  Context {UserVar : UserParams}.
  Fixpoint Alg_to_CH (a : Alg) : list Alg := 
    match a with
    | Lift e => match e with
                | Assn a => [@{a}]
                | _ => []
                end
    | Comb s p q => match s with
                    | NDC => (Alg_to_CH p) ++ (Alg_to_CH q) % list
                    | _ => []
                    end
    end .

  Lemma Alg_to_CH_id : forall l, CH l -> Alg_to_CH (|-| l) = l.
  Proof.
    apply (rev_ind (fun l =>  CH l -> Alg_to_CH (|-| l) = l)).
    intros. auto. intros. assert (CH l). unfold CH in *.
    intros. assert (In x0 (l ++ [x])). apply In_rev. rewrite rev_app_distr.
    simpl. right. rewrite <- In_rev. auto. apply H0 in H2. auto.
    apply H in H1. remember (Alg_to_CH (|-| (l ++ [x]))). rewrite <- H1.
    rewrite Heql0. unfold NDCList. destruct l. simpl. simpl in H0.
    unfold CH in H0. pose (H0 x). destruct e. apply in_eq. destruct H2.
    rewrite H2. auto. simpl. rewrite <- fold_left_rev_right.
    rewrite rev_app_distr. simpl. unfold CH in H0.
    pose (H0 x). destruct e. apply In_rev. rewrite rev_app_distr.
    simpl. left. auto. destruct H2. rewrite H2. simpl.
    rewrite fold_left_rev_right. auto.
  Qed.

  (*Seq*)
  Definition CH_comb_Seq (a b : list Alg) :=
    (map (fun g => Assign_comb_Seq (fst g) (snd g)) (list_prod a b)).

  Definition Normal_comb_Seq (p q : Alg) :=
    match p, q with
    | Comb x _ a, Comb y _ b =>
       match x, y with
       | CDC c, CDC d => (_|_) <| (fun g => orb (c g)
            (CH_over_Boolexp (Alg_to_CH a) d)) |>
         |-| (CH_comb_Seq (Alg_to_CH a) (Alg_to_CH b))
       | _, _ => -o-
       end
    | _, _ => -o-
    end.

  (*CDC*)
  Definition CH_comb_CDC (a b : list Alg) (c : Boolexp):=
    (map (fun g => Assign_comb_CDC (fst g) (snd g) c) (list_prod a b)).

  Definition Normal_comb_CDC (p q : Alg) (bexp : Boolexp) :=
    match p, q with
    | Comb x _ a, Comb y _ b =>
       match x, y with
       | CDC c, CDC d => (_|_) <| (fun g => if (bexp g) then (c g)
             else (d g)) |>
         |-| (CH_comb_CDC (Alg_to_CH a) (Alg_to_CH b) bexp)
       | _, _ => -o-
       end
    | _, _ => -o-
    end.

  (*NDC*)
  Definition Normal_comb_NDC (p q : Alg) :=
    match p, q with
    | Comb x _ a, Comb y _ b =>
       match x, y with
       | CDC c, CDC d => (_|_) <| (fun g => orb (c g) (d g)) |>
         |-| ((Alg_to_CH a) ++ (Alg_to_CH b))
       | _, _ => -o-
       end
    | _, _ => -o-
    end.

  Fixpoint Normal (a : Alg) : Alg :=
    match a with
    | Lift e => 
      match e with
      | Assn a => (_|_) <| false_stat |> |-|[@{extends_assign a}]
      | Empty => (_|_) <| false_stat |> |-|[]
      | Chaos => (_|_) <| true_stat |> |-|[@{empty_assn}]
      end
    | Comb s p q =>
      match s with
      | Seq => Normal_comb_Seq (Normal p) (Normal q)
      | CDC b => Normal_comb_CDC (Normal p) (Normal q) b
      | NDC => Normal_comb_NDC (Normal p) (Normal q)
      end
    end.

  Theorem NormalisNF : forall x, FNF (Normal x).
  Proof.
    intros. induction x;try destruct a;try destruct c.
    - unfold Normal. unfold FNF. do 2 eexists. split;pauto. unfold CH.
      intros. destruct H; try contradiction. rewrite <- H. unfold empty_assn.
      eexists;split;pauto.
    - unfold Normal. unfold FNF. do 2 eexists. split;pauto. unfold CH.
      intros. destruct H;try contradiction. rewrite <- H. destruct a.
      eexists;split;pauto.
    - unfold Normal. unfold FNF. do 2 eexists. split;pauto. unfold CH.
      intros. destruct H.
    - simpl. unfold FNF in *. destruct IHx1. do 2 destruct H.
      destruct IHx2. do 2 destruct H1. rewrite H. rewrite H1.
      simpl. do 2 eexists. split;auto. apply Alg_to_CH_id in H0 as H3.
      apply Alg_to_CH_id in H2 as H4. rewrite H3. rewrite H4.
      unfold CH_comb_Seq. unfold CH in *. intros. apply in_map_iff in H5.
      do 2 destruct H5. destruct x6. apply in_prod_iff in H6.
      destruct H6. apply H0 in H6. apply H2 in H7. do 2 destruct H6.
      do 2 destruct H7. rewrite <- H5. simpl. rewrite H6. rewrite H7.
      simpl. unfold extends_assign. unfold Assign_comb_Seq_help. simpl.
      eexists. split;pauto.
    - simpl. unfold FNF in *. destruct IHx1. do 2 destruct H.
      destruct IHx2. do 2 destruct H1. rewrite H. rewrite H1.
      simpl. do 2 eexists. split;auto. apply Alg_to_CH_id in H0 as H3.
      apply Alg_to_CH_id in H2 as H4. rewrite H3. rewrite H4.
      unfold CH_comb_Seq. unfold CH in *. intros. apply in_app_or in H5.
      destruct H5. apply H0 in H5. auto. apply H2 in H5. auto.
    - simpl. unfold FNF in *. destruct IHx1. do 2 destruct H.
      destruct IHx2. do 2 destruct H1. rewrite H. rewrite H1.
      simpl. do 2 eexists. split;auto. apply Alg_to_CH_id in H0 as H3.
      apply Alg_to_CH_id in H2 as H4. rewrite H3. rewrite H4.
      unfold CH_comb_Seq. unfold CH in *. intros. apply in_map_iff in H5.
      do 2 destruct H5. destruct x6. apply in_prod_iff in H6.
      destruct H6. apply H0 in H6. apply H2 in H7. do 2 destruct H6.
      do 2 destruct H7. rewrite <- H5. simpl. rewrite H6. rewrite H7.
      simpl. unfold extends_assign. unfold Assign_comb_Seq_help. simpl.
      eexists. split;pauto.
  Qed.

  Theorem NormalRWT : forall x, x <--> Normal x.
  Proof.
    intros. induction x;try destruct a;try destruct c.
    - simpl. apply (Chaos_to_NF [@{empty_assn}]). discriminate.
    - simpl. pose (Assign_extends a). apply (rwt_trans _ _ _ r).
      unfold extends_assign. simpl. apply (Assign_to_NF).
    - simpl. apply Empty_to_NF.
    - simpl. pose (rwt_comb _ _ _ _ Seq IHx1 IHx2).
      apply (rwt_trans _ _ _ r). pose NormalisNF.
      pose (f x1). pose (f x2). destruct f0. do 2 destruct H.
      destruct f1. do 2 destruct H1. rewrite H. rewrite H1.
      simpl. pose (NF_over_Seq x0 x4 x x3). apply r0 in H2 as H3;auto.
      clear r r0. apply (rwt_trans _ _ _ H3). rewrite (Alg_to_CH_id x0);auto.
      apply rwt_comb;pauto. rewrite (Alg_to_CH_id x4);auto.
      clear H3 H1 H. pose (Seq_over_Choice x0 x4). apply r in H0 as H3;auto.
      clear r. apply (rwt_trans _ _ _ H3). clear H3. unfold CH_comb_Seq.
      apply rwt_ext_Forall. rewrite Forall_forall. intros.
      destruct x5. apply in_prod_iff in H. destruct H. unfold CH in *.
      simpl in *. apply H0 in H. apply H2 in H1. do 2 destruct H.
      do 2 destruct H1. rewrite H. rewrite H1. unfold Assign_comb_Seq.
      pose (rwt_comb _ _ _ _ Seq (Assign_extends x5) (Assign_extends x6)).
      apply (rwt_trans _ _ _ r). clear r. unfold extends_assign.
      unfold Assign_comb_Seq_help. simpl. apply Assign_Seq.
    - simpl. pose (rwt_comb _ _ _ _ NDC IHx1 IHx2).
      apply (rwt_trans _ _ _ r). pose NormalisNF.
      pose (f x1). pose (f x2). destruct f0. do 2 destruct H.
      destruct f1. do 2 destruct H1. rewrite H. rewrite H1.
      simpl. pose (NF_over_Choice x0 x4 x x3). apply r0 in H2 as H3;auto.
      clear r r0. apply (rwt_trans _ _ _ H3). rewrite (Alg_to_CH_id x0);auto.
      apply rwt_comb;pauto. rewrite (Alg_to_CH_id x4);auto.
      clear H3 H1 H. apply Choice_distr;auto.
    - simpl. pose (rwt_comb _ _ _ _ (CDC b) IHx1 IHx2).
      apply (rwt_trans _ _ _ r). pose NormalisNF.
      pose (f x1). pose (f x2). destruct f0. do 2 destruct H.
      destruct f1. do 2 destruct H1. rewrite H. rewrite H1.
      simpl. pose (NF_over_Cond x0 x4 x b x3). apply r0 in H2 as H3;auto.
      clear r r0. apply (rwt_trans _ _ _ H3). rewrite (Alg_to_CH_id x0);auto.
      apply rwt_comb;pauto. rewrite (Alg_to_CH_id x4);auto.
      clear H3 H1 H. pose (Cond_over_Choice x0 x4 b). apply r in H0 as H3;auto.
      clear r. apply (rwt_trans _ _ _ H3). clear H3. unfold CH_comb_Seq.
      apply rwt_ext_Forall. rewrite Forall_forall. intros.
      destruct x5. apply in_prod_iff in H. destruct H. unfold CH in *.
      simpl in *. apply H0 in H. apply H2 in H1. do 2 destruct H.
      do 2 destruct H1. rewrite H. rewrite H1. unfold Assign_comb_CDC.
      pose (rwt_comb _ _ _ _ (CDC b) (Assign_extends x5) (Assign_extends x6)).
      apply (rwt_trans _ _ _ r). clear r. unfold extends_assign.
      unfold Assign_comb_CDC_help. simpl. apply Assign_Cond.
  Qed.

End NormalForm.

#[export] Hint Resolve NormalisNF NormalRWT: palg.

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
  Proof. intros. unfold AlgPres. intros. generalize y.
    cofix Pres. intros. apply HereAndFurther.
    - unfold AlgPresStep. simpl. apply H.
    - simpl. apply Pres.
  Qed.

  Lemma AlgPresInd : forall y, FNFPres y (f y) ->
    (forall x, FNFPres (f x) (f (f x))) -> AlgPres (Recur y).
  Proof. intros. unfold AlgPres. intros. apply HereAndFurther.
    unfold AlgPresStep. auto. simpl. generalize y. cofix Pres.
    intros. apply HereAndFurther.
    - unfold AlgPresStep. simpl. apply H0.
    - simpl. apply Pres.
  Qed.

End Infty.

End ProgramAlgebra.
