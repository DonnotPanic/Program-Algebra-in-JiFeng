Require Import List.
Import ListNotations.
Require Import Logic.FunctionalExtensionality.

Module ProgramAlgebra.

(* PRIMARY *)
(** it's unnecessary to give the exact definition *)
Class UserParams : Type := {
  Var : Set;
  GLOBVARS : list Var;
  eqb: Var -> Var -> bool;
}.
Section Assign.
Context {UserVar : UserParams}.
Definition Exp := (list Var) -> (list Var).

Record Assign := makeAssign {
  ids : (list Var);
  values : Exp;
}.
Definition refl : Exp := (fun x => x).

Definition empty_assn : Assign :=
  makeAssign GLOBVARS refl.
End Assign.

(** Boolexp is the type of boolean condition *)

Section Bool.
  Context {UserVar : UserParams}.
  Definition Boolexp : Type := (list Var) -> bool.
  Definition true_stat : Boolexp := (fun x => true).
  Definition false_stat : Boolexp := (fun x => false).
End Bool.

(* FINITE ALGEBRA *)
Section ualg.
  Context {UserVar : UserParams}.
  Variable syn : Type.
  Inductive Alg : Type :=
  | Chaos : Alg
  | Assn : Assign -> Alg
  | Cond : Alg -> Boolexp -> Alg -> Alg
  | Seq : Alg -> Alg -> Alg
  | Choice : Alg -> Alg -> Alg
  | Recur : (syn -> Alg) -> Alg.
End ualg.

Section Fact.
Context {UserVar : UserParams}.

Definition Ualg := forall syn, Alg syn.

(** Notation of Alg *)
Notation "var :== exp" := (makeAssign var exp)(at level 51).

Notation "@{ e }" := (fun x => Assn x e)(at level 10).

Notation "_|_" := (fun x => Chaos x)(at level 10).

Definition empty_program : Ualg := @{ empty_assn }.

Fixpoint Choice_of_Alg_List {syn} (l : list (Alg syn))  : Alg syn :=
  match l with
  | [] => (empty_program syn)
  | x :: xs => (Choice syn x (Choice_of_Alg_List xs))
  end.

Notation "|-| l" := (Choice_of_Alg_List l)(at level 20).

(* LAW *)
(** Law A.1 *)
(** Law A.1.1 *)
Axiom Chaos_zero_Choice_l : forall syn (p : Alg syn), (Choice syn (_|_ syn) p) = _|_ syn.
Axiom Chaos_zero_Seq_l : forall syn (p : Alg syn), (Seq syn (_|_ syn) p) = _|_ syn.
Axiom Chaos_zero_Seq_r : forall syn (p : Alg syn), (Seq syn p (_|_ syn)) = _|_ syn.

(** Law A.1.2 *)
Axiom Choice_comm : forall x (p q : Alg x), (Choice x p q) = (Choice x q p).
Theorem Chaos_zero_Choice_r : forall syn (p : Alg syn), (Choice syn p (_|_ syn)) = _|_ syn.
Proof. intros. simpl. rewrite Choice_comm. apply Chaos_zero_Choice_l. Qed.
Axiom Choice_assoc : forall syn (p q r : Alg syn), (Choice syn (Choice syn p q) r) = (Choice syn p (Choice syn q r)).
Axiom Choice_id : forall syn (p : Alg syn), (Choice syn p p) = p.
Axiom Choice_zero_l : forall syn (p : Alg syn),
  Choice syn (empty_program syn) p = p.
Theorem Choice_zero_r : forall syn (p : Alg syn),
  Choice syn p (empty_program syn) = p.
Proof. intros. simpl. rewrite Choice_comm. apply Choice_zero_l. Qed.

(** Law A.1.3 *)
Axiom Cond_rev : forall x (p q : Alg x) (b : Boolexp),
  (Cond x p  b q)  = (Cond x q (fun g => negb (b g)) p).

(** Law A.1.4 *)
Axiom Seq_assoc : forall syn (p q r : Alg syn), 
  (Seq syn (Seq syn p q) r) = (Seq syn p (Seq syn q r)).

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
 v = extends_assign v.

(** Law A.2.2 *)
Axiom Assign_compose : forall syn (v : (list Var)) (g h : Exp),
  Seq syn (@{v :== g} syn) (@{v :== h} syn) = (@{v :== (fun x => h (g x))} syn).

(** Law A.2.3 *)
Definition exp_Cond (g h : Exp) (c : bool) : Exp :=
  match c with
   | true => g
   | false => h
  end.

Axiom Assign_Cond : forall syn (v : (list Var)) (g h : Exp) (b : Boolexp) ,
  Cond syn (@{v :== g} syn) b (@{v :== h} syn) = (@{ v :== (exp_Cond g h (b v))} syn).

(** Law A.2.4 *)
Axiom Assign_to_NF : forall (v : (list Var)) (e : Exp) b syn,
  b GLOBVARS = false ->
  @{v :== e} syn = (Cond syn (_|_ syn) b (|-| [@{extends_assign (v :== e)} syn])).

(** Law A.2.5 *)
Axiom Chaos_to_NF : forall syn b p, b GLOBVARS = true -> (_|_) syn = (Cond syn (_|_ syn) b (|-| p)).

(** TH1 *)

Definition Total_Assign (a : Assign) := forall v:Var, In v GLOBVARS -> In v a.(ids).
Theorem Assign_is_Total : forall a : Assign, exists b : Assign, a=b /\ Total_Assign b.
Proof.
  intros. exists (extends_assign a). split.
  - apply Assign_extends.
  - unfold extends_assign. unfold Total_Assign. auto.
Qed.

Theorem Assign_elim_Seq : forall syn (a b: Assign),
     exists (c: Assign), Seq syn (@{a} syn) (@{b} syn) = (@{c} syn) /\ Total_Assign c.
Proof. intros. rewrite (Assign_extends a). rewrite (Assign_extends b).
    unfold extends_assign. rewrite Assign_compose. eexists;split;eauto.
    unfold Total_Assign. auto. Qed.

Theorem Assign_elim_Cond : forall syn (a b: Assign) (d : Boolexp),
     exists (c: Assign), Cond syn (@{a} syn) d (@{b} syn) = (@{c} syn) /\ Total_Assign c.
Proof. intros. rewrite (Assign_extends a). rewrite (Assign_extends b).
    unfold extends_assign. rewrite Assign_Cond. eexists;split;eauto.
    unfold Total_Assign. auto.  Qed.

(** Law A.3 *)
Definition CH {syn} (p : list (Alg syn)): Prop :=
  forall (x : Alg syn), In x p -> exists y, x = (@{y} syn) /\ Total_Assign y.

(** Law A.3.1 *)
Axiom Choice_distr : forall syn (a b : list (Alg syn)),
  CH a -> CH b -> (Choice syn (|-| a) (|-| b)) = (|-| (a ++ b)).

(** Law A.3.2 *)
Axiom Cond_over_Choice : forall syn (a b : list (Alg syn)) (bexp : Boolexp),
  CH a -> CH b ->
  Cond syn (|-| a) bexp (|-| b) = |-| (map (fun g => Cond syn (fst g) bexp (snd g)) (list_prod a b)).

(** Law A.3.3 *)
Axiom Seq_over_Choice : forall syn (a b : list (Alg syn)),
  CH a -> CH b ->
  Seq syn (|-| a) (|-| b) = |-| (map (fun g => Seq syn (fst g) (snd g)) (list_prod a b)).

(** Law A.3.4 *)
Axiom Choice_to_NF : forall syn (a : list (Alg syn)) b,
  CH a -> b GLOBVARS = false ->
  (|-| a) = Cond syn (_|_ syn) b (|-| a).

(** TH2 *)
Lemma CH_hd :forall syn (l: list (Alg syn)) (a : Alg syn),
  CH (a :: l) -> exists y, a = (@{y} syn) /\ Total_Assign y.
Proof. intros. unfold CH in *. assert (In a (a::l)) by (apply in_eq;auto).
  apply H in H0. auto. Qed.
Lemma CH_cons : forall syn (l: list (Alg syn)) (a : Alg syn),
  CH (a :: l) -> CH l.
Proof. intros. unfold CH in *. intros. apply (in_cons a) in H0 as H1.
  apply H in H1. auto. Qed.

Lemma Choice_list_cons : forall syn (l: list (Alg syn)) (a: Alg syn),
  (|-| (a :: l)) = (Choice syn a (|-| l)).
Proof. intros. unfold Choice_of_Alg_List. auto. Qed.

Lemma Choice_list_eq_app : forall syn (l1 l2 l3 : list (Alg syn)),
  (|-| l1) = (|-| l2) -> (|-| (l3 ++ l1)) = (|-| (l3 ++ l2)).
Proof. intros. induction l3;auto. repeat rewrite <- app_comm_cons.
  repeat rewrite Choice_list_cons. rewrite IHl3. auto. Qed.

Lemma CH_app_rev : forall syn (l1 l2 : list (Alg syn)),
  CH l1 -> CH l2 -> CH (l1 ++ l2).
Proof. intros. unfold CH in *. intros. apply in_app_or in H1. destruct H1.
  - apply H in H1. auto.
  - apply H0 in H1. auto.
Qed.

Lemma CH_elim_Cond : forall syn (p q c : list (Alg syn)) (b : Boolexp),
  CH p -> CH q -> exists c, (Cond syn (|-| p) b (|-| q)) = (|-| c) /\ CH c.
Proof. intros. rewrite Cond_over_Choice;auto. induction p;simpl. induction q;simpl.
  - exists [];auto.
  - apply CH_cons in H0 as H1. apply IHq in H1. auto.
  - apply CH_cons in H as H1. apply IHp in H1. rewrite map_app.
    destruct H1. remember (map (fun y => (a, y)) q).
    remember (map (fun g => Cond syn (fst g) b (snd g)) l). exists (l0 ++ x).
    destruct H1. split.
    + rewrite Heql0. apply Choice_list_eq_app. auto.
    + apply CH_app_rev;auto. apply CH_hd in H as H3. rewrite Heql0. rewrite Heql.
      unfold CH in *. intros. apply in_map_iff in H4. repeat destruct H4.
      destruct H3. apply in_map_iff in H5. destruct H5. destruct H4.
      rewrite <- H4. simpl. apply H0 in H5. destruct H5. destruct H5.
      rewrite H5. destruct H3. rewrite H3. apply Assign_elim_Cond.
Qed.

Lemma CH_elim_Seq : forall syn (p q c : list (Alg syn)),
  CH p -> CH q -> exists c, (Seq syn (|-| p) (|-| q)) = (|-| c) /\ CH c.
Proof. intros. rewrite Seq_over_Choice;auto. induction p;simpl. induction q;simpl.
  - exists [];auto.
  - apply CH_cons in H0 as H1. apply IHq in H1. auto.
  - apply CH_cons in H as H1. apply IHp in H1. rewrite map_app.
    destruct H1. remember (map (fun y => (a, y)) q).
    remember (map (fun g => Seq syn (fst g) (snd g)) l). exists (l0 ++ x).
    destruct H1. split.
    + rewrite Heql0. apply Choice_list_eq_app. auto.
    + apply CH_app_rev;auto. apply CH_hd in H as H3. rewrite Heql0. rewrite Heql.
      unfold CH in *. intros. apply in_map_iff in H4. repeat destruct H4.
      destruct H3. apply in_map_iff in H5. destruct H5. destruct H4.
      rewrite <- H4. simpl. apply H0 in H5. destruct H5. destruct H5.
      rewrite H5. destruct H3. rewrite H3. apply Assign_elim_Seq.
Qed.

Lemma CH_elim_Choice : forall syn (p q c : list (Alg syn)),
  CH p -> CH q -> exists c, (Choice syn (|-| p) (|-| q)) = (|-| c) /\ CH c.
Proof. intros. rewrite Choice_distr;eauto. exists (p ++ q). split;auto.
  apply CH_app_rev;auto. Qed.

(** Law A.4 *)
(** Law A.4.1 *)
Axiom NF_over_Choice : forall syn (a b : list (Alg syn)) (c d : Boolexp),
  CH a -> CH b ->
  (Choice syn (Cond syn (_|_ syn) c (|-| a)) (Cond syn (_|_ syn) d (|-| b))) =
  (Cond syn (_|_ syn) (fun g => orb (c g) (d g)) (Choice syn (|-|a) (|-| b))).

(** Law A.4.2 *)
Axiom NF_over_Cond : forall syn (a b : list (Alg syn)) (c d e : Boolexp),
  CH a -> CH b ->
  (Cond syn (Cond syn (_|_ syn) c (|-|a)) d (Cond syn (_|_ syn) e (|-| b))) =
  (Cond syn (_|_ syn) (fun g => if (d g) then (c g) else (e g)) (Cond syn (|-|a) d (|-| b))).

(** Law A.4.3-A.4.4 *)
Definition Assign_over_Boolexp (b : Boolexp) syn (a : Alg syn):=
  match a with
  | Assn _ x => b ((extends_mapping x.(ids) x.(values)) GLOBVARS)
  | _ => false
  end.
Definition CH_over_Boolexp {syn} (a : list (Alg syn)) (b : Boolexp) :=
  fold_left orb (map (Assign_over_Boolexp b syn) a) true.

(** Law A.4.5 *)
Axiom NF_over_Seq : forall syn (a b : list (Alg syn)) (c d : Boolexp),
  CH a -> CH b ->
  (Seq syn (Cond syn (_|_ syn) c (|-| a)) (Cond syn (_|_ syn) d (|-| b))) =
  (Cond syn (_|_ syn) (fun g => orb (c g) (CH_over_Boolexp a d)) (Seq syn (|-| a) (|-| b))).

(** TH.3 *)
Definition FNF {syn} (P : Alg syn ): Prop :=
  exists bexp Q, P = Cond syn (_|_ syn) bexp Q /\ exists R, Q = (|-| R) /\ CH R.

Lemma FNF_elim_Cond : forall syn (P Q : Alg syn) (b : Boolexp),
  FNF P -> FNF Q -> FNF (Cond syn P b Q).
Proof.
  intros. unfold FNF in H. destruct H. destruct H. destruct H.
  destruct H1. destruct H1.
  unfold FNF in H0. destruct H0. destruct H0. destruct H0.
  destruct H3. destruct H3.
  rewrite H. rewrite H0. rewrite H1. rewrite H3.
  rewrite NF_over_Cond;auto. unfold FNF.
  eexists. eexists. split;eauto.
  apply CH_elim_Cond;auto.
Qed.

Lemma FNF_elim_Choice : forall syn (P Q : Alg syn),
  FNF P -> FNF Q -> FNF (Choice syn P Q).
Proof.
  intros. unfold FNF in H. destruct H. destruct H. destruct H.
  destruct H1. destruct H1.
  unfold FNF in H0. destruct H0. destruct H0. destruct H0.
  destruct H3. destruct H3.
  rewrite H. rewrite H0. rewrite H1. rewrite H3.
  rewrite NF_over_Choice;auto. unfold FNF.
  eexists. eexists. split;eauto.
  apply CH_elim_Choice;auto.
Qed.

Lemma FNF_elim_Seq : forall syn (P Q : Alg syn),
  FNF P -> FNF Q -> FNF (Seq syn P Q).
Proof.
  intros. unfold FNF in H. destruct H. destruct H. destruct H.
  destruct H1. destruct H1.
  unfold FNF in H0. destruct H0. destruct H0. destruct H0.
  destruct H3. destruct H3.
  rewrite H. rewrite H0. rewrite H1. rewrite H3.
  rewrite NF_over_Seq;auto. unfold FNF.
  eexists. eexists. split;eauto.
  apply CH_elim_Seq;auto.
Qed.

(** Law A.5-A.7 *)
Definition clos (c : Type) := (c -> Alg c).
Inductive Closure := 
  | iter : forall c, clos c -> Closure.

Hypothesis lub : Closure -> Ualg.

Definition eqEval (x y : Assign) :=
  forall a, In a (x.(values) x.(ids)) -> In a (y.(values) y.(ids)).

Definition eqAssn {syn syn1} (x : Alg syn) (y : Alg syn1) :=
  match x with
  | Assn _ e => 
    match y with
    | Assn _ f => eqEval (extends_assign e) (extends_assign f)
    | _ => False
    end
  | _ => False
  end.

Definition RefineCH {syn syn1} (A : list (Alg syn))
 (B : list (Alg syn1)) :=
 forall x,
  In x B -> exists y, In y A /\ eqAssn x y.

Definition Refine {syn syn1} (P : Alg syn)
 (Q : Alg syn1) :=
  exists bexp cexp S T U V,
   (P = Cond syn (_|_ syn) bexp S 
    /\ S = (|-| U) /\ CH U)
  /\ (Q = Cond syn1 (_|_ syn1) cexp T
    /\ T = (|-| V) /\ CH V)
  /\ ((cexp GLOBVARS = false /\ (RefineCH U V))
    \/ (bexp GLOBVARS = true)).

Fixpoint EqAlg {syn syn1} (x : Alg syn) (y : Alg syn1) :=
  match x, y with
  | Assn _ e, Assn _ f => eqEval (extends_assign e) (extends_assign f)
  | Chaos _, Chaos _ => True
  | Cond _ P bexp Q, Cond _ R cexp T => bexp GLOBVARS = cexp GLOBVARS /\ EqAlg P R /\ EqAlg Q T
  | Seq _ P Q, Seq _ R T => EqAlg P R /\ EqAlg Q T
  | Choice _ P Q, Choice _ R T => EqAlg P R /\ EqAlg Q T
  | _, _ => False
  end.

Definition RecurFix {syn} (f : clos (Alg syn)) (x : Alg syn) := EqAlg x (f x).

Axiom fix_is_lub : forall s (f : clos (Alg s)) (x : Alg s),
 RecurFix f x -> (f x) = lub (iter (Alg s) f) (Alg s).

Definition FNF_pres {syn : Type} (f : clos (Alg syn)) :=
  forall x, FNF x -> FNF (f x).

Axiom Recur_clos : forall (syn : Type) (F : clos (Alg syn)),
  Recur (Alg syn) F = lub (iter (Alg syn) F) (Alg syn).

Axiom Recur_over_Recur : forall (syn : Type) (f g : clos (Alg syn)) x,
   f x = lub (iter (Alg syn) g) (Alg syn) ->
   exists c, FNF_pres c /\
   lub (iter (Alg syn) f) (Alg syn) = lub (iter (Alg syn) c) (Alg syn).

Axiom Recur_over_Choice : forall (syn : Type) (f : clos (Alg syn)) (p : Alg (Alg syn)),
  FNF_pres f -> FNF p ->
  (Choice (Alg syn) (lub (iter (Alg syn) f) (Alg syn)) p =
  lub (iter (Alg syn) (fun g => (Choice (Alg syn) (f g) p))) (Alg syn)).

Axiom Recur_over_Cond : forall (syn : Type) (f : clos (Alg syn)) (p : Alg (Alg syn)) (b : Boolexp),
  FNF_pres f -> FNF p ->
  (Cond (Alg syn) (lub (iter (Alg syn) f) (Alg syn)) b p =
  lub (iter (Alg syn) (fun g => (Cond (Alg syn) (f g) b p))) (Alg syn)).

Axiom Recur_over_Seq_l : forall (syn : Type) (f : clos (Alg syn)) (p : Alg (Alg syn)),
  FNF_pres f -> FNF p ->
  (Seq (Alg syn) (lub (iter (Alg syn) f) (Alg syn)) p =
  lub (iter (Alg syn) (fun g => (Seq (Alg syn) (f g) p))) (Alg syn)).

Axiom Recur_over_Seq_r : forall (syn : Type) (f : clos (Alg syn)) (p : Alg (Alg syn)),
  FNF_pres f -> FNF p ->
  (Seq (Alg syn) p (lub (iter (Alg syn) f) (Alg syn)) =
  lub (iter (Alg syn) (fun g => (Seq (Alg syn) p (f g)))) (Alg syn)).

Axiom Recur_over_Rec_Choice : forall (syn : Type) (f g : clos (Alg syn)),
  FNF_pres f -> FNF_pres g ->
  Choice (Alg syn) (lub (iter (Alg syn) f) (Alg syn)) (lub (iter (Alg syn) g) (Alg syn)) =
  lub (iter (Alg syn) (fun k => (Choice (Alg syn) (f k) (g k)))) (Alg syn).

Axiom Recur_over_Rec_Cond : forall (syn : Type) (f g : clos (Alg syn)) (b : Boolexp),
  FNF_pres f -> FNF_pres g ->
  Cond (Alg syn) (lub (iter (Alg syn) f) (Alg syn)) b (lub (iter (Alg syn) g) (Alg syn)) =
  lub (iter (Alg syn) (fun k => (Cond (Alg syn) (f k) b (g k)))) (Alg syn).

Axiom Recur_over_Rec_Seq : forall (syn : Type) (f g : clos (Alg syn)),
  FNF_pres f -> FNF_pres g ->
  Seq (Alg syn) (lub (iter (Alg syn) f) (Alg syn)) (lub (iter (Alg syn) g) (Alg syn)) =
  lub (iter (Alg syn) (fun k => (Seq (Alg syn) (f k) (g k)))) (Alg syn).

Definition IFNF {syn} (p : Alg (Alg syn)) :=
  exists x, p = lub (iter (Alg syn) x) (Alg syn) /\ FNF_pres x.

Lemma IFNF_elim_Choice_FNF_l :
  forall x (a b : Alg (Alg x)), IFNF a -> FNF b ->
  IFNF (Choice (Alg x) a b).
Proof. intros. unfold IFNF in *. destruct H. destruct H. eexists.
  split. rewrite H. apply Recur_over_Choice;auto.
  unfold FNF_pres. intros. apply FNF_elim_Choice;auto. Qed.

Lemma IFNF_elim_Choice_FNF_r :
  forall x (a b : Alg (Alg x)), IFNF a -> FNF b ->
  IFNF (Choice (Alg x) b a).
Proof. intros. unfold IFNF in *. destruct H. destruct H. eexists.
  split. rewrite H. rewrite Choice_comm. apply (Recur_over_Choice x);auto.
  unfold FNF_pres. intros. apply FNF_elim_Choice;auto. Qed.

Lemma IFNF_elim_Cond_FNF_l :
  forall x (a b : Alg (Alg x)) c, IFNF a -> FNF b ->
  IFNF (Cond (Alg x) a c b).
Proof. intros. unfold IFNF in *. destruct H. destruct H. eexists.
  split. rewrite H. apply Recur_over_Cond;auto. 
  unfold FNF_pres. intros. apply FNF_elim_Cond;auto. Qed.

Lemma IFNF_elim_Cond_FNF_r :
  forall x (a b : Alg (Alg x)) c, IFNF a -> FNF b ->
  IFNF (Cond (Alg x) b c a).
Proof. intros. unfold IFNF in *. destruct H. destruct H. eexists.
  split. rewrite H. rewrite Cond_rev. apply Recur_over_Cond;auto.
  unfold FNF_pres. intros. apply FNF_elim_Cond;auto. Qed.

Lemma IFNF_elim_Seq_FNF_l :
  forall x (a b : Alg (Alg x)), IFNF a -> FNF b ->
  IFNF (Seq (Alg x) a b).
Proof. intros. unfold IFNF in *. destruct H. destruct H. eexists.
  split. rewrite H. apply Recur_over_Seq_l;auto.
  unfold FNF_pres. intros. apply FNF_elim_Seq;auto. Qed.

Lemma IFNF_elim_Seq_FNF_r :
  forall x (a b : Alg (Alg x)), IFNF a -> FNF b ->
  IFNF (Seq (Alg x) b a).
Proof. intros. unfold IFNF in *. destruct H. destruct H. eexists.
  split. rewrite H. apply Recur_over_Seq_r;auto.
  unfold FNF_pres. intros. apply FNF_elim_Seq;auto. Qed.

Theorem Alg_is_FNF_or_IFNF : forall (a : Ualg) x, FNF (a (Alg x)) \/ IFNF (a (Alg x)).
Proof.
  intros. induction (a (Alg x)).
  - left. rewrite (Chaos_to_NF (Alg x) true_stat [@{empty_assn} (Alg x)]);auto.
    unfold FNF. eexists. eexists. split;eauto. eexists. split;auto.
    unfold empty_program. unfold CH. intros.
    unfold In in H. destruct H;try contradiction. rewrite <- H.
    eexists. split;auto. unfold empty_assn. unfold Total_Assign. auto.
  - left. destruct a0. rewrite (Assign_to_NF _ _ false_stat (Alg x));auto. unfold FNF.
    eexists. eexists. split;eauto.
    eexists. split;auto. unfold CH. intros. unfold In in H.
    destruct H;try contradiction. rewrite <- H. eexists. split;auto.
    unfold Total_Assign. unfold extends_assign. auto.
  - destruct IHa0_1;destruct IHa0_2.
    + left. apply FNF_elim_Cond;auto.
    + right. apply IFNF_elim_Cond_FNF_r;auto.
    + right. apply IFNF_elim_Cond_FNF_l;auto.
    + right. unfold IFNF in *. destruct H. destruct H. destruct H0.
      destruct H0. rewrite H. rewrite H0. eexists. split.
      apply Recur_over_Rec_Cond;auto. unfold FNF_pres.
      intros. apply FNF_elim_Cond;auto.
  - destruct IHa0_1;destruct IHa0_2.
    + left. apply FNF_elim_Seq;auto.
    + right. apply IFNF_elim_Seq_FNF_r;auto.
    + right. apply IFNF_elim_Seq_FNF_l;auto.
    + right. unfold IFNF in *. destruct H. destruct H. destruct H0.
      destruct H0. rewrite H. rewrite H0. eexists. split.
      apply Recur_over_Rec_Seq;auto. unfold FNF_pres.
      intros. apply FNF_elim_Seq;auto.
  - destruct IHa0_1;destruct IHa0_2.
    + left. apply FNF_elim_Choice;auto.
    + right. apply IFNF_elim_Choice_FNF_r;auto.
    + right. apply IFNF_elim_Choice_FNF_l;auto.
    + right. unfold IFNF in *. destruct H. destruct H. destruct H0.
      destruct H0. rewrite H. rewrite H0. eexists. split.
      apply Recur_over_Rec_Choice;auto. unfold FNF_pres.
      intros. apply FNF_elim_Choice;auto.
  - right. unfold IFNF. exists a0. split. apply Recur_clos.
    unfold FNF_pres. intros. remember (H x0). clear Heqo.
    destruct o;auto. unfold IFNF in H1. do 2 destruct H1.
    remember (Recur_over_Recur x a0 x1 x0). clear Heqe.
    apply e in H1 as H3. do 2 (destruct H3). unfold FNF_pres in H3.
    apply H3 in H0. do 2 rewrite <- Recur_clos in H4.
    inversion H4. auto.
Qed.

Axiom Ualg_to_Alg : forall syn (x : Alg syn), exists t: Ualg, t syn = x.

End Fact.
End ProgramAlgebra.


