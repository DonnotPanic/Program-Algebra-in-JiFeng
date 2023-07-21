From PA Require Import ProgramAlgebra.
Import ProgramAlgebra.
Require Import Lia.
Import Nat.
Import List.
Require Import String.
Import ListNotations.

Open Scope alg_scope.

Print Visibility.

Record MyVar := mkVar {
  id: string;
  val : nat;
}.

Definition eqbVar (x y : MyVar) := 
  andb (eqb x.(id) y.(id)) (PeanoNat.Nat.eqb x.(val) y.(val)).

Variable GLOBVARS : list MyVar.

Definition Constarints := exists a b c, (eqbVar a b = false) /\ (eqbVar a c = false)
 /\ (eqbVar b c = false) /\ GLOBVARS = [a;b;c].

Lemma eqbVar_sym : forall x y, eqbVar x y = eqbVar y x.
Proof. intros. unfold eqbVar. destruct x. destruct y. simpl.
  assert ((id0 =? id1) % string = (id1 =? id0) %string) by apply eqb_sym.
  assert ((val0 =? val1) = (val1 =? val0)) by apply PeanoNat.Nat.eqb_sym.
  rewrite H. rewrite H0. auto. Qed.

Lemma eqbVar_refl : forall x, eqbVar x x = true.
Proof. intros. unfold eqbVar. destruct x. simpl.
  assert ((id0 =? id0) % string = true) by apply eqb_refl.
  assert ((val0 =? val0) = true) by apply PeanoNat.Nat.eqb_refl.
  rewrite H. rewrite H0. auto. Qed.

Definition UNDEF := mkVar "Undefined" 0.

Instance myParams : UserParams :=
  Build_UserParams MyVar GLOBVARS eqbVar Constarints.

Fixpoint ascending (l : list Var) : list Var :=
  match l with
  | [] => []
  | h :: tl => (mkVar h.(id) (h.(val) + 1)) :: ascending tl
  end.

Fixpoint descending (l : list Var) : list Var :=
  match l with
  | [] => []
  | h :: tl => (mkVar h.(id) (h.(val) - 1)) :: descending tl
  end.

Definition dscassn := makeAssign GLOBVARS descending.

Definition ascassn := makeAssign GLOBVARS ascending.

Definition hdge2 : Boolexp :=
 fun l =>
  match (hd_error l) with
  | None => false
  | Some x => PeanoNat.Nat.leb 20 x.(val)
  end.

Definition hdle1 : Boolexp :=
 fun l =>
  match (hd_error l) with
  | None => false
  | Some x => PeanoNat.Nat.leb x.(val) 10
  end.

Definition testAlg := ((@{ascassn}) ;;
  ((@{empty_assn}) <| hdge2  |> (@{dscassn}))) <| hdle1 |> (_|_).

Definition testAlg2 := (_|_) <| (fun x => negb (hdle1 x)) |>
  (@{ascassn}) ;; ((|-|[@{ascassn};@{dscassn}])).

Definition tess := (@{ascassn}) ;; ((|-|[@{ascassn};@{dscassn}])).

(* functions in this example are supposed to be already extended *)
Hypothesis no_extends : forall x:Exp, extends_mapping GLOBVARS x = x.

Example testrefine : Refine (Normal testAlg2) (Normal testAlg).
Proof.
  unfold Refine. do 4 eexists. split;split;try split;auto. 
  - unfold CH. simpl. intros. destruct H.
    + rewrite <- H. eexists. split;pauto.
    + destruct H;try contradiction. rewrite <- H. eexists. split;pauto.
  - simpl. assert(forall a b, (_|_) <| b|> a = (_|_) <| b |> |-|[a]) by auto.
    rewrite H. reflexivity.
  - unfold CH. intros. destruct H;try contradiction. eexists. split;try rewrite <- H;pauto.
  - simpl in *. intros. assert Constarints by auto. unfold Constarints in H. do 4 destruct H. destruct H1.
    destruct H2. unfold ascassn. unfold extends_assign. simpl. unfold empty_assn.
    repeat rewrite (no_extends ascending). repeat rewrite (no_extends descending).
    repeat rewrite (no_extends refl_exp). unfold Assign_comb_CDC_help.
    unfold Assign_comb_Seq_help. simpl. assert (GLOBVARS = ProgramAlgebra.GLOBVARS).
    auto. repeat rewrite H4. assert (exp_Cond (extends_mapping ProgramAlgebra.GLOBVARS
     (fun x2 => extends_mapping ProgramAlgebra.GLOBVARS (exp_Cond refl_exp descending hdge2)
     (ascending x2))) refl_exp hdle1 = exp_Cond (fun x => ((exp_Cond refl_exp descending hdge2) 
      (ascending x))) refl_exp hdle1). simpl. rewrite (no_extends (exp_Cond refl_exp descending hdge2)).
    rewrite (no_extends (fun x2 : list MyVar => exp_Cond refl_exp descending hdge2 (ascending x2))).
    auto. simpl in *. remember (hdle1 GLOBVARS). destruct b.
    + left. rewrite H3 in Heqb. unfold hdle1 in Heqb. simpl in *. apply eq_sym in Heqb.
      assert (val x <= 10). apply Compare_dec.leb_complete in Heqb. auto.
      assert (20 <=? val x + 1 = false).
      apply Compare_dec.leb_correct_conv. lia. split.
      unfold CH_over_Boolexp. simpl. unfold false_stat.
      rewrite (no_extends ascending). unfold ascending.
      unfold hdge2. rewrite H3. simpl. (fold (20 <=? (val x + 1))).
      rewrite H7. auto. rewrite H5. clear H5. unfold CH_comb_CDC.
      simpl. unfold RefineCH. intros. destruct H5;try contradiction.
      eexists. split. simpl. right. left. auto.
      unfold Assign_comb_CDC_help. simpl.
      rewrite (no_extends refl_exp). rewrite <- H5.
      rewrite (no_extends (fun x3 : list MyVar => descending (ascending x3))).
      simpl. unfold subEval. rewrite H3. simpl. unfold exp_Cond.
      unfold hdle1. simpl. rewrite Heqb. simpl. unfold hdge2.
      simpl. fold (20 <=? (val x + 1)). rewrite H7. simpl. auto.
    + simpl. right. auto.
  Qed.

