(* See also:                  *)
(* ./faust-coq/lib/tuplealg.v *)

From mathcomp Require Import all_ssreflect all_algebra.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section ZModTuple.

Variable V : zmodType.
Variable k : nat.

Local Open Scope ring_scope.
Import GRing.Theory.

Implicit Types (t : k.-tuple V).

Definition zerot : k.-tuple V := [tuple of nseq k 0%R].
Definition oppt t := map_tuple -%R t.
Definition addt t1 t2 := [tuple of map (prod_curry +%R) (zip t1 t2)].

(* Note, important to use the same level than + *)
Local Notation "t1 '+t' t2" := (addt t1 t2) (at level 50).
Local Notation "'-t' t" := (oppt t) (at level 50).

Lemma tnth_addt t1 t2 idx : tnth (t1 +t t2) idx = tnth t1 idx + tnth t2 idx.
Proof.
by rewrite !tnth_map !(tnth_nth 0) ?nth_zip ?(nth_map 0) ?nth_zip ?size_tuple.
Qed.

Lemma tnth_oppt t idx : tnth (-t t) idx = - tnth t idx.
Proof. by rewrite tnth_map. Qed.

Lemma addtA : associative addt.
Proof.
by move=> ? ? ?; apply/eq_from_tnth=> ?; rewrite !tnth_addt ?addrA.
Qed.

Lemma addtC : commutative addt.
by move=> ? ?; apply/eq_from_tnth=> ?; rewrite !tnth_addt addrC.
Qed.

Lemma tnth_nseq T i (x : T) (idx : 'I_i) : tnth [tuple of nseq i x] idx = x.
Proof. by rewrite (tnth_nth x) nth_nseq if_same. Qed.

Lemma add0t : left_id zerot addt.
Proof.
by move=> ?; apply/eq_from_tnth=> ?; rewrite tnth_addt tnth_nseq add0r.
Qed.

Lemma addNt : left_inverse zerot oppt addt.
Proof.
by move=> s; apply/eq_from_tnth=> idx; rewrite tnth_addt tnth_oppt tnth_nseq addNr.
Qed.

Definition tuple_zmodMixin :=
  @ZmodMixin (k.-tuple V) zerot oppt addt
             addtA addtC add0t addNt.

Canonical tuple_zmodType := Eval hnf in ZmodType (k.-tuple V) tuple_zmodMixin.

End ZModTuple.

Section ZModTupleTheory.

Variable V : zmodType.

Local Open Scope ring_scope.
Import GRing.Theory.

Lemma zerotE : [tuple] = 0%R :> 0.-tuple V.
Proof. exact/val_inj. Qed.

Lemma addt_cons k (t1 t2 : k.+1.-tuple V) :
  t1 + t2 = [tuple of thead t1 + thead t2
         :: [tuple of behead t1] + [tuple of behead t2]].
Proof. by rewrite [t1]tuple_eta [t2]tuple_eta !theadE; apply/val_inj. Qed.

Lemma oppt_cons k (t : k.+1.-tuple V) :
  - t = [tuple of - thead t :: - [tuple of behead t]].
Proof. by rewrite [t]tuple_eta !theadE; apply/val_inj. Qed.

End ZModTupleTheory.

Section LModCol.

Local Open Scope ring_scope.
Import GRing.Theory.

Variable (k : nat) (R : ringType) (L : lmodType R).
Let V := 'cV[L]_k.
Implicit Types (c : R) (t : V).

Definition scalec c t : V := \col_i (c *: t i ord0).

Lemma scalecA c1 c2 t : scalec c1 (scalec c2 t) = scalec (c1*c2) t.
Proof. by apply/matrixP=> i j; rewrite !mxE scalerA. Qed.

Lemma scale1c : @left_id R V 1 scalec.
Proof. by move=> ?; apply/matrixP=> ? ?; rewrite !mxE scale1r !ord1. Qed.

Lemma scalecDr : right_distributive scalec +%R.
Proof. by move=> ? ? ?; apply/matrixP=> ? ?; rewrite !mxE scalerDr. Qed.

Lemma scalecDl v : {morph scalec^~ v : a b / a + b >-> a + b}.
Proof. by move=> ? ?; apply/matrixP=> ? ?; rewrite !mxE scalerDl. Qed.

Definition col_lmodMixin :=
  @LmodMixin R [zmodType of V] scalec scalecA scale1c scalecDr scalecDl.

Print Canonical Projections.

Print polynomial_lmodType.
Print poly_lmodMixin.
Canonical col_lmodType := Eval hnf in LmodType R V col_lmodMixin.

(* this is quite a fringe case; so I dunno if that should be added to
   the library or I just keep this instances local

   also inference is not likely work, so indeed I could use the
   typical pattern and make introduce a new head constant [convertible
   to]

 *)

End LModCol.

Section LModTuple.

Local Open Scope ring_scope.
Import GRing.Theory.

Variable (k : nat) (R : ringType) (L : lmodType R).
Let V := k.-tuple L.
Implicit Types (c : R) (t : V).

Definition scalet c t : V := [tuple of [seq c *: x | x <- t]].

Definition scalet_in t : col_lmodType _ L := \col_i tnth t i.

Lemma scalet_in_inj t1 t2 :
  scalet_in t1 = scalet_in t2 -> t1 = t2.
Proof.
move/matrixP=> s_eq; apply/eq_from_tnth=> idx.
by have := s_eq idx ord0; rewrite !mxE.
Qed.

Check *:%R.
Lemma scaletP c t : scalet_in (scalet c t) = c *: (scalet_in t).
Proof. by apply/matrixP => i j; rewrite !mxE tnth_map. Qed.

Lemma addtP t1 t2 : scalet_in (t1 + t2) = scalet_in t1 + scalet_in t2.
Proof. by apply/matrixP => i j; rewrite !mxE tnth_addt. Qed.

(* Lemma scaletA c1 c2 t : scalet c1 (scalet c2 t) = scalet (c1*c2) t. *)
(* Proof. by apply/eq_from_tnth=> idx; rewrite !tnth_map mulrA. Qed. *)

Lemma scaletA c1 c2 t : scalet c1 (scalet c2 t) = scalet (c1*c2) t.
Proof. by apply/scalet_in_inj; rewrite !scaletP scalerA. Qed.

Lemma scale1t : @left_id R V 1 scalet.
Proof. by move=> ?; apply/scalet_in_inj; rewrite !scaletP scale1r. Qed.

Lemma scaletDr : right_distributive scalet +%R.
Proof.
by move=> ? ? ?; apply/scalet_in_inj; rewrite !(scaletP,addtP) scalerDr.
Qed.

Lemma scaletDl v : {morph scalet^~ v : a b / a + b >-> a + b}.
Proof.
by move=> ? ?; apply/scalet_in_inj; rewrite !(scaletP,addtP) !scalerDl.
Qed.

Definition tuple_lmodMixin :=
  @LmodMixin R [zmodType of V] scalet scaletA scale1t scaletDr scaletDl.

Canonical tuple_lmodType := Eval hnf in LmodType R V tuple_lmodMixin.

End LModTuple.

Section LModTupleTheory.

Local Open Scope ring_scope.
Import GRing.Theory.

Variable (k : nat) (R : ringType) (L : lmodType R).

Lemma scalet_cons (t : k.+1.-tuple L) c :
  c *: t = [tuple of c *: thead t :: c *: [tuple of behead t]].
Proof. by rewrite [t]tuple_eta !theadE; apply/val_inj. Qed.

End LModTupleTheory.
