(* Some investigations in signal processing.
 * (c) Mines ParisTech 2017
 *
 *  Emilio J. Gallego Arias
 *  Sylvain Ribstein
 *
 * Term encoding originally inspired by a development by P-Y Strub.
 *
 * LICENSE: CeCILL-B
 *
 *)

From mathcomp Require Import all_ssreflect all_algebra.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

From W Require Import tuplealg.

Definition admit {T} : T. Admitted.

(******************************************************************************)
(* Auxiliary Lemmas and Definitions                                           *)
(******************************************************************************)
Section HSeq.

Variables (T : Type) (P : T -> Type).

Fixpoint hseq l : Type :=
  if l is x :: l then P x * hseq l else unit.

Variable (t0 : T) (x0 : P t0).

Fixpoint hnth (l : seq T) n : hseq l -> P (nth t0 l n) :=
  match l with
  | [::]        => fun _  => match n with | 0 => x0 | _.+1 => x0 end
  | [:: x & xs] => fun hs => match n with
                             | 0    => hs.1
                             | n.+1 => hnth n hs.2
                             end
  end.

End HSeq.

Section HSeqMap.

Variables (T : Type) (P1 P2 : T -> Type).

Fixpoint hmap (f : forall t, P1 t -> P2 t) (l : seq T) : hseq P1 l -> hseq P2 l :=
  match l with
  | [::]        => fun hs => hs
  | [:: x & xs] => fun hs => (f _ hs.1, hmap f hs.2)
  end.

End HSeqMap.

(******************************************************************************)
(* End Auxiliary Lemmas and Definitions                                       *)
(******************************************************************************)

(* Formalization for the Wagner language, linear fragment *)
Section Wagner.
Variable R : idomainType.

Section Syntax.

(* We represent our linear fragment as functions from
 * R ⊗ ⋯ ⊗ R ⊸ R ⊗ ⋯ ⊗ R
 *)
Inductive ty :=
| tpair of nat
| tfun  of nat & nat.

Section TyInstances.

Implicit Types (t : ty).

Notation tyrep := (nat * nat + nat)%type.

Fixpoint ty_enc t : tyrep :=
  match t with
  | tpair n     => inr n
  | tfun n1 n2  => inl (n1, n2)
  end.

Fixpoint ty_dec (tr : tyrep) :=
  match tr with
  | inl n => tfun n.1 n.2
  | inr n => tpair n
  end.

Lemma ty_encK : cancel ty_enc ty_dec.
Proof. by case. Qed.

Canonical ty_eqType     := Eval hnf in EqType     ty (CanEqMixin     ty_encK).
Canonical ty_choiceType := Eval hnf in ChoiceType ty (CanChoiceMixin ty_encK).

End TyInstances.

(* Lightly-typed syntax, inspired by a development from PY-Strub. *)
Definition t0 := 0.
Inductive expr : seq nat -> ty -> Type :=
(*     idx    time        *)
| var    v Γ of nat                                  : expr Γ (tpair (nth t0 Γ v))
| add    n Γ of expr Γ (tpair n) & expr Γ (tpair n)  : expr Γ (tpair n)
| mul    n Γ of R & expr Γ (tpair n)                 : expr Γ (tpair n)
| pair m n Γ of expr Γ (tpair m) & expr Γ (tpair n)  : expr Γ (tpair (m + n))
| proj   n Γ of 'I_n.+1 & expr Γ (tpair n.+1)        : expr Γ (tpair 1)
| feed   n Γ of expr (n :: Γ) (tpair n)              : expr Γ (tpair n)
| lam  m n Γ of expr (m :: Γ) (tpair n)              : expr Γ (tfun m n)
| app  m n Γ of expr Γ (tfun m n) & expr Γ (tpair m) : expr Γ (tpair n).

End Syntax.

Section WagnerInterp.

(* Interpretations for types, A.K.A closed expressions *)
Implicit Types (t : ty) (tn : nat).

(* We assume a global fixed time, then, traces are defined by their
   size, which basically represents the number of elements of the
   stream that we have manage to produce so far. *)

Coercion lift_t (tn : nat) : ty := tpair tn.
Definition lift_Γ (l : seq nat) : seq ty := map tpair l.

Definition tyI k t : Type :=
  match t with
  | tpair  n => 'cV[R]_n
  | tfun m n => k.+1.-tuple 'cV[R]_m -> 'cV[R]_n
  end.

Definition I0 k t : tyI k t :=
  match t return tyI k t with
  | tpair  n => 0%R
  | tfun m n => fun _ => 0%R
  end.

(* Interpretations for expressions:

 - An environment is just a list representing the history of
   variables, with the most recent element in the head.

 - For simplicity, we don't support yet the case of storing functions
   in the time-based enviromnet.

 - This helps as base values are time invariant and thus we do not
   have to worry about "transporting" values in time.
 *)
Definition hist k tn := k.+1.-tuple (tyI k tn).
Definition env  k l  := hseq (hist k) l.

(* We add the transport fucntions for convenience. *)
(* We can't transport a function to the future yet. *)
Definition Iext k tn : tyI k tn -> tyI k.+1 tn := fun e => e.

(* Similarly we cannot transport it to the past without shifting the
   closure indexes *)
Definition Icon k tn : tyI k.+1 tn -> tyI k tn := fun e => e.

(* Default history *)
Definition hist0 k tn : hist k tn := [tuple of nseq k.+1 (I0 _ tn)].

(* Interpretation yielding a trace up to size n, convenient as to be
   able to reconstruct history more easily. *)
Definition I n : Type := forall k, k < n -> forall {Γ t} (e : expr Γ t), env k Γ -> tyI k t.
Definition IE0 n : I n := fun k _ _ t _ _ => I0 k t.

Definition behead_hist k tn (hs : hist k.+1 tn) : hist k tn :=
  [tuple of behead hs].

Definition extend_hist k tn x (hs : hist k tn) : hist k.+1 tn :=
  [tuple of x :: [seq Iext t | t <- hs]].

Definition behead_env k l (hs : env k.+1 l) : env k l :=
  hmap (@behead_hist _) hs.

(* Given an intepretation up to a trace of size n, we can re-build the
 * history of an expression as a tuple in the current time moment.  *
 *
 * Note however the discussed caveats with our dependent types, in
 * particular, we have to lift things around due to our simple
 * definition of history; we would expect that a function would take
 * elements placed in their proper temporal time stamp.
 *
 *)
Definition accI_rec n Γ tn (I : forall k, k <= n -> env k Γ -> tyI k tn) :=
  fix accI k : k <= n -> env k Γ -> hist k tn :=
  match k with
  | 0    => fun hk Θ => [tuple I _ hk Θ]
  | k.+1 => fun hk Θ =>
            let Ik : tyI  k.+1 tn :=    I k.+1 hk Θ                  in
            let Ip : hist k    tn := accI k (ltnW hk) (behead_env Θ) in
            [tuple of cons Ik Ip]
  end.

Definition accF_rec n Γ tn (I : forall k, k < n -> env k Γ -> tyI k tn) :=
  fix accF k : k <= n -> env k Γ -> hist k tn :=
  match k with
  | 0    => fun hk Θ => [tuple (I0 0 tn)]
  | k.+1 => fun hk Θ =>
              let Ik : tyI  k.+1 tn :=    I k hk        (behead_env Θ) in
              let Ip : hist k    tn := accF k (ltnW hk) (behead_env Θ) in
              [tuple of cons Ik Ip]
  end.

Definition accI := nosimpl accI_rec.
Definition accF := nosimpl accF_rec.

Local Open Scope ring_scope.

(* We are packing a lot of power! *)
Definition exprI n (pI : I n) : I n.+1 :=
  fix eI k hk {Γ t} e {struct e} :=
  match e in expr Γ t return env k Γ -> tyI k t with
  | var v Γ idx      => fun Θ => nth (I0 k _) (hnth (hist0 k _) v Θ) idx
  | add _ _  e1 e2   => fun Θ => eI k hk e1 Θ + eI k hk e2 Θ
  | mul _ _  c  e    => fun Θ => c *: eI k hk e Θ
  | pair _ _ _ e1 e2 => fun Θ => col_mx (eI k hk e1 Θ) (eI k hk e2 Θ)
  | proj m _ i e     => fun Θ => \col__ (eI k hk e Θ) i ord0
  | lam m _ _ e      => fun Θ v => eI k hk e (v, Θ)
  | app _ _ _ ef ea  => fun Θ =>
                        let efI : tyI k (tfun _ _) := eI k hk ef Θ in
                        let eaI : hist k _ :=
                            accI (fun k hk => eI k hk ea) hk Θ in
                        efI eaI
  | feed tn Γ e      => fun Θ =>
                        let prev :=
                            accF (fun k hk => pI k hk _ _ (feed e)) hk Θ in
                        eI k hk e (prev, Θ)
  end.

(* Need to prove |acc_feed n.+1| =  acc_norm n ?? *)

(* We build our step-indexed representation *)
Fixpoint exprIn n {struct n} : I n.+1 :=
  match n return I n.+1 with
  | 0    => fun k hk Γ t e (Θ : env k Γ) =>
            exprI (@IE0 _) hk e Θ
  | n.+1 => fun k hk Γ t e (Θ : env k Γ) =>
            exprI (@exprIn n) hk e Θ
  end.

Definition p1 : expr [::] _ :=
  @lam 1 1 _ (feed (@add 1 [:: 1; 1]%nat (var 0 _ 0) (var 1 _ 0))).

Local Open Scope ring_scope.
Import GRing.Theory.

Lemma exprIn0 : @exprIn 0 = @exprI 0 (@IE0 0).
Proof. by []. Qed.

Lemma exprInS (n : nat) : @exprIn n.+1 = @exprI n.+1 (@exprIn n).
Proof. by []. Qed.

Lemma exprInE :
  let r := @exprIn 2 2%nat erefl _ _ p1 (tt) in
  r [tuple 1; 1; 2%:R] = 4%:R.
Proof. by rewrite /= add0r -!addrA. Qed.

End WagnerInterp.

Section Linearity.

Local Open Scope ring_scope.
Import GRing.Theory.

(* Main logical relation *)
Fixpoint rel_additive k t {struct t} : tyI k t -> tyI k t -> tyI k t -> Prop :=
  match t with
  | tpair m   => fun x1 x2 x3 => x1 = x2 - x3
  | tfun  m n => fun f1 f2 f3 =>
      forall (x1 x2 x3 : k.+1.-tuple (tyI k m)),
        x1 = x2 - x3 -> f1 x1 = f2 x2 - f3 x3
  end.

Fixpoint env_additive k Γ : env k Γ -> env k Γ -> env k Γ -> Prop :=
  match Γ with
    | [::]       => fun _ _ _    => True
    | [:: t & Γ] => fun Θ1 Θ2 Θ3 =>
      Θ1.1 = Θ2.1 - Θ3.1 /\ env_additive Θ1.2 Θ2.2 Θ3.2
  end.

Lemma hist0_additive k : hist0 k t0 = hist0 k t0 - hist0 k t0.
Proof. by rewrite subrr. Qed.

Hint Resolve hist0_additive.

Lemma get_env_additive Γ k idx (Θ1 Θ2 Θ3 : env k Γ) (hΘ : env_additive Θ1 Θ2 Θ3) :
  let: tn := nth t0 Γ idx in
  let: h0 := hist0 k t0   in
  hnth h0 idx Θ1 = hnth h0 idx Θ2 - hnth h0 idx Θ3.
Proof.
by elim: Γ k idx Θ1 Θ2 Θ3 hΘ => [|t Γ ihΓ] k [|idx] //= Θ1 Θ2 Θ3; intuition.
Qed.

Lemma get_hist_additive tn k idx (h1 h2 h3 : hist k tn) (hh : h1 = h2 - h3) :
  let i0 := I0 k tn in
  rel_additive (nth i0 h1 idx) (nth i0 h2 idx) (nth i0 h3 idx).
Proof.
case: (k < idx)%nat / leqP => /= hidx; last first.
  rewrite !(nth_default _) ?subrr ?size_tuple //.
by rewrite hh (nth_map 0) ?nth_zip ?(nth_map 0) ?size_tuple.
Qed.

Lemma additive_cons k tn (v1 v2 v3 : hist k.+1 tn) :
  v1 = v2 - v3 <-> thead v1 = thead v2 - thead v3 /\
                   [tuple of behead v1] = [tuple of behead v2] - [tuple of behead v3].
Proof.
rewrite !addt_cons !oppt_cons /=; split=> [-> | [hh /(congr1 val) /= ht]].
  by rewrite !theadE; split; apply/val_inj.
by apply/val_inj; rewrite [v1]tuple_eta !theadE /= hh ht.
Qed.

Lemma behead_hist_additive k tn (v1 v2 v3 : hist k.+1 tn) :
  v1 = v2 - v3 -> behead_hist v1 = behead_hist v2 - behead_hist v3.
Proof. by case/additive_cons. Qed.

Lemma behead_additive k Γ (Θ1 Θ2 Θ3 : env k.+1 Γ) :
      env_additive Θ1 Θ2 Θ3 ->
      let: Θ1' := behead_env Θ1 in
      let: Θ2' := behead_env Θ2 in
      let: Θ3' := behead_env Θ3 in
      env_additive Θ1' Θ2' Θ3'.
Proof.
elim: Γ Θ1 Θ2 Θ3 => //= tn Γ ihΓ [v1 Θ1] [v2 Θ2] [v3 Θ3] /= [h1 h2].
by split; [apply: behead_hist_additive | apply: ihΓ].
Qed.

(* TODO: - What about the implicits in "I : I n" *)
Definition linP n (I : I n) :=
  forall k (p : (k < n)%nat) Γ (Θ1 Θ2 Θ3 : env k Γ) (tn : nat) (e : expr Γ tn),
    env_additive Θ1 Θ2 Θ3 ->
    I _ p _ _ e Θ1 = I _ p _ _ e Θ2 - I _ p _ _ e Θ3.

(* open type int *)
Definition oI n Γ t := forall k : nat, (k <= n)%N -> env k Γ -> tyI k t.

Definition olinP n Γ (tn : nat) (I : oI n Γ tn) :=
  forall k (hk : (k <= n)%nat) (Θ1 Θ2 Θ3 : env k Γ),
    env_additive Θ1 Θ2 Θ3 ->
    I _ hk Θ1 = I _ hk Θ2 - I _ hk Θ3.

Lemma accI_additive Γ (tn : nat) k n (hk : (k <= n)%N) (g1 g2 g3 : env k Γ)
      (I : oI n Γ tn) (HI : olinP I)
      (hΘ : env_additive g1 g2 g3) :
  accI I hk g1 = accI I hk g2 - accI I hk g3.
Proof.
elim: k hk g1 g2 g3 hΘ => [|k ihk] hk g1 g2 g3 hΘ; apply/val_inj.
  by rewrite /= (HI _ _ _ _ _ hΘ).
have hΘ' := behead_additive hΘ.
by rewrite /= -/accI (ihk _ _ _ _ hΘ') (HI _ _ _ _ _ hΘ).
Qed.

Definition fI n Γ tn := forall k : nat, (k < n)%N -> env k Γ -> tyI k tn.

Definition flinP n Γ (tn : nat) (I : fI n Γ tn) :=
  forall (tn : nat) k (hk : (k < n)%nat) (Θ1 Θ2 Θ3 : env k Γ),
    env_additive Θ1 Θ2 Θ3 ->
    I _ hk Θ1 = I _ hk Θ2 - I _ hk Θ3.

Lemma accF_additive Γ (tn : nat) k n (hk : (k <= n)%N) (g1 g2 g3 : env k Γ)
      (I : fI n Γ tn) (HI : flinP I)
      (hΘ : env_additive g1 g2 g3) :
  accF I hk g1 = accF I hk g2 - accF I hk g3.
Proof.
elim: k hk g1 g2 g3 hΘ => [|k ihk] hk g1 g2 g3 hΘ; apply/val_inj.
  by rewrite subrr.
have hΘ' := behead_additive hΘ.
by rewrite /= -/accF (ihk _ _ _ _ hΘ') (HI _ _ _ _ _ _ hΘ').
Qed.

(* forall k : nat (k < n)%N (Γ : seq nat) (t : ty), expr Γ t -> env k Γ -> tyI k t *)

(* Definition fI n Γ := forall t k : nat, (k < n)%N -> env k Γ -> tyI k t. *)

(* This has to be cleaned up. *)
Definition hlinP n (I : I n) := forall m Γ (e : expr (m :: Γ) m) , flinP
    (fun (k : nat) (hk : (k < n)%N) =>
     I k hk Γ m (feed e)).

Definition hlinP' n (I : I n) := forall (t : nat) Γ (e : expr Γ t) , flinP
    (fun (k : nat) (hk : (k < n)%N) => I k hk Γ t e).

Lemma rel_additive_fund Γ t (e : expr Γ t) n (I : I n) (HI : hlinP' I) :
  forall k (hk : (k < n.+1)%N) (g1 g2 g3 : env k Γ) ,
    env_additive g1 g2 g3      ->
    let: v1 := exprI I hk e g1 in
    let: v2 := exprI I hk e g2 in
    let: v3 := exprI I hk e g3 in
    rel_additive v1 v2 v3.
Proof.
elim: Γ t / e => /=
    [ m Γ idx
    | m Γ e1 ihe1 e2 ihe2
    | m Γ c e ihe
    | m Γ o e1 ihe1 e2 ihe2
    | m Γ o e ihe
    | m Γ e ihe
    | m o Γ e ihe
    | m Γ o e1 ihe1 e2 ihe2
    ] k hk g1 g2 g3 hΘ.
- exact/get_hist_additive/get_env_additive.
- by rewrite opprD addrACA; congr (_ + _); auto.
- by rewrite -scalerN -scalerDr; congr (_ *: _); auto.
- by rewrite opp_col_mx add_col_mx; congr col_mx; auto.
- by rewrite (ihe _ _ _ g2 g3) //; apply/matrixP=> ? ?; rewrite !mxE.
- by apply: ihe; split => //; apply/accF_additive.
- by move=> x1 x2 x3 hva; apply: ihe.
- exact/ihe1/accI_additive.
Qed.

Lemma lin0P : @hlinP' 0 (@IE0 0).
Proof. by []. Qed.

Lemma linPn n : hlinP' (@exprIn n).
Proof.
elim: n => [|n IHn] t Γ e ? k p g1 g2 g3 H.
exact/(rel_additive_fund e lin0P).
exact/(rel_additive_fund e).
Qed.

Lemma rel_additivePn n k (p : (k <= n)%nat) Γ t (e : expr Γ t) g1 g2 g3 :
  env_additive g1 g2 g3    ->
  let: v1 := exprIn p e g1 in
  let: v2 := exprIn p e g2 in
  let: v3 := exprIn p e g3 in
  rel_additive v1 v2 v3.
Proof.
elim: n p => [|n IHn] p /= hea.
exact/(rel_additive_fund _ lin0P).
exact/(rel_additive_fund _ (@linPn _)).
Qed.

Corollary funD n k (p : (k <= n)%nat) a b (f : expr [::] (tfun a b)) :
  additive (exprIn p f tt).
Proof.
move=> /= x2 x3; move E: (x2 - x3) => /= x1.
have He: @env_additive k [::] tt tt tt by [].
exact/(rel_additivePn p f He).
Qed.

(* We can indeed parameterize this constructions in base of the
   relation, we could even do an arity-generic encoding *)
Section Scale.

Variable (c : R).

Fixpoint rel_scale k t {struct t} : tyI k t -> tyI k t -> Prop :=
  match t with
  | tpair m   => fun x1 x2 => x1 = c *: x2
  | tfun  m n => fun f1 f2 =>
      forall (x1 x2 : k.+1.-tuple 'cV[R]_m),
        x1 = c *: x2 -> f1 x1 = c *: f2 x2
  end.

Fixpoint env_scale k Γ : env k Γ -> env k Γ -> Prop :=
  match Γ with
    | [::]       => fun _ _   => True
    | [:: t & Γ] => fun Θ1 Θ2 =>
      Θ1.1 = c *: Θ2.1 /\ env_scale Θ1.2 Θ2.2
  end.

Lemma hist0_scale k : hist0 k t0 = c *: hist0 k t0.
Proof. by rewrite scaler0. Qed.

Hint Resolve hist0_scale.

Lemma get_env_scale Γ k idx (Θ1 Θ2 : env k Γ) (hΘ : env_scale Θ1 Θ2) :
  let: tn := nth t0 Γ idx in
  let: h0 := hist0 k t0   in
  hnth h0 idx Θ1 = c *: (hnth h0 idx Θ2).
Proof.
by elim: Γ k idx Θ1 Θ2 hΘ => [|t Γ ihΓ] k [|idx] //= Θ1 Θ2; intuition.
Qed.

Lemma get_hist_scale tn k idx (h1 h2 : hist k tn) (hh : h1 = c *: h2) :
  let i0 := I0 k tn in
  rel_scale (nth i0 h1 idx) (nth i0 h2 idx).
Proof.
case: (k < idx)%nat / leqP => /= hidx; last first.
  by rewrite !(nth_default _) ?scaler0 ?size_tuple.
by rewrite hh (nth_map 0) ?nth_zip ?(nth_map 0) ?size_tuple.
Qed.

Lemma scale_cons k tn (v1 v2 : hist k.+1 tn) :
  v1 = c *:  v2 <-> thead v1 = c *: thead v2 /\
                   [tuple of behead v1] = c *: [tuple of behead v2].
Proof.
rewrite scalet_cons {1}[v1]tuple_eta; split=> [[? ?]|[-> <-]//].
by split=> //; apply/val_inj.
Qed.

Lemma behead_hist_scale k tn (v1 v2 : hist k.+1 tn) :
  v1 = c *: v2 -> behead_hist v1 = c *: behead_hist v2.
Proof. by case/scale_cons. Qed.

Lemma behead_scale k Γ (Θ1 Θ2 : env k.+1 Γ) :
      env_scale Θ1 Θ2 ->
      let: Θ1' := behead_env Θ1 in
      let: Θ2' := behead_env Θ2 in
      env_scale Θ1' Θ2'.
Proof.
elim: Γ Θ1 Θ2 => //= tn Γ ihΓ [v1 Θ1] [v2 Θ2] /= [h1 h2].
by split; [apply: behead_hist_scale | apply: ihΓ].
Qed.

Definition oscaleP n Γ (tn : nat) (I : oI n Γ tn) :=
  forall k (hk : (k <= n)%nat) g1 g2,
    env_scale g1 g2 ->
    I _ hk g1 = c *: I _ hk g2.

Lemma accI_scale Γ (tn : nat) k n (hk : (k <= n)%N) (g1 g2 : env k Γ)
      (I : oI n Γ tn) (HI : oscaleP I)
      (hΘ : env_scale g1 g2) :
  accI I hk g1 = c *: accI I hk g2.
Proof.
elim: k hk g1 g2 hΘ => [|k ihk] hk g1 g2 hΘ; apply/val_inj.
  by rewrite /= (HI _ _ _ _ hΘ).
have hΘ' := behead_scale hΘ.
by rewrite /= -/accI (ihk _ _ _ hΘ') (HI _ _ _ _ hΘ).
Qed.

Definition fscaleP n Γ (tn : nat) (I : fI n Γ tn) :=
  forall k (hk : (k < n)%nat) g1 g2,
    env_scale g1 g2 ->
    I _ hk g1 = c *: I _ hk g2.

Lemma accF_scale Γ (tn : nat) k n (hk : (k <= n)%N) (g1 g2 : env k Γ)
      (I : fI n Γ tn) (HI : fscaleP I)
      (hΘ : env_scale g1 g2) :
  accF I hk g1 = c *: accF I hk g2.
Proof.
elim: k hk g1 g2 hΘ => [|k ihk] hk g1 g2 hΘ; apply/val_inj.
  by rewrite /= scaler0.
have hΘ' := behead_scale hΘ.
by rewrite /= -/accF (ihk _ _ _ hΘ') (HI _ _ _ _ hΘ').
Qed.

Definition hscaleP' n (I : I n) := forall (t : nat) Γ (e : expr Γ t) , fscaleP
    (fun (k : nat) (hk : (k < n)%N) => I k hk Γ t e).

Lemma rel_scale_fund Γ t (e : expr Γ t) n (I : I n) (HI : hscaleP' I) :
  forall k (hk : (k < n.+1)%N) (g1 g2 : env k Γ) ,
    env_scale g1 g2      ->
    let: v1 := exprI I hk e g1 in
    let: v2 := exprI I hk e g2 in
    rel_scale v1 v2.
Proof.
elim: Γ t / e => /=
    [ m Γ idx
    | m Γ e1 ihe1 e2 ihe2
    | m Γ d e ihe
    | m Γ o e1 ihe1 e2 ihe2
    | m Γ o e ihe
    | m Γ e ihe
    | m o Γ e ihe
    | m Γ o e1 ihe1 e2 ihe2
    ] k hk g1 g2 hΘ.
- exact/get_hist_scale/get_env_scale.
- by rewrite scalerDr; congr (_ + _); auto.
- by rewrite scalerA mulrC -scalerA; congr (_ *: _); auto.
- by rewrite scale_col_mx; congr col_mx; auto.
- by rewrite (ihe _ _ _ g2 _) //; apply/matrixP=> ? ?; rewrite !mxE.
- by apply: ihe; split=> //; apply/accF_scale.
- by move=> x1 x2 hva; apply: ihe; intuition.
- exact/ihe1/accI_scale.
Qed.

Lemma scale0P : @hscaleP' 0 (@IE0 0).
Proof. by []. Qed.

Lemma scalePn n : hscaleP' (@exprIn n).
Proof.
elim: n => [|n IHn] t Γ e k p g1 g2 H.
exact/(rel_scale_fund e scale0P).
exact/(rel_scale_fund e IHn).
Qed.

Lemma rel_scalePn n k (p : (k <= n)%nat) Γ t (e : expr Γ t) g1 g2 :
  env_scale g1 g2          ->
  let: v1 := exprIn p e g1 in
  let: v2 := exprIn p e g2 in
  rel_scale v1 v2.
Proof.
elim: n p => [|n IHn] p /= hea.
exact/(rel_scale_fund _).
exact/(rel_scale_fund _ _ _ hea)/scalePn.
Qed.

End Scale.

Section Linear.

Variable (c : R).

Fixpoint rel_linear k t {struct t} : tyI k t -> tyI k t -> tyI k t -> Prop :=
  match t with
  | tpair m   => fun x1 x2 x3 => x1 = c *: x2 + x3
  | tfun  m n => fun f1 f2 f3 =>
      forall (x1 x2 x3 : k.+1.-tuple (tyI k m)),
        x1 = c *: x2 + x3 -> f1 x1 = c *: f2 x2 + f3 x3
  end.

Fixpoint env_linear k Γ : env k Γ -> env k Γ -> env k Γ -> Prop :=
  match Γ with
    | [::]       => fun _ _ _    => True
    | [:: t & Γ] => fun Θ1 Θ2 Θ3 =>
      Θ1.1 = c *: Θ2.1 + Θ3.1 /\ env_linear Θ1.2 Θ2.2 Θ3.2
  end.

Lemma hist0_linear k : hist0 k t0 = c *: hist0 k t0 + hist0 k t0.
Proof. by rewrite scaler0 add0r. Qed.

Hint Resolve hist0_linear.

Lemma get_env_linear Γ k idx (Θ1 Θ2 Θ3 : env k Γ) (hΘ : env_linear Θ1 Θ2 Θ3) :
  let: tn := nth t0 Γ idx in
  let: h0 := hist0 k t0   in
  hnth h0 idx Θ1 = c *: hnth h0 idx Θ2 + hnth h0 idx Θ3.
Proof.
by elim: Γ k idx Θ1 Θ2 Θ3 hΘ => [|t Γ ihΓ] k [|idx] //= Θ1 Θ2 Θ3; intuition;
   try apply hist0_linear; exact: ihΓ.
Qed.

Lemma get_hist_linear tn k idx (h1 h2 h3 : hist k tn) (hh : h1 = c *: h2 + h3) :
  let i0 := I0 k tn in
  rel_linear (nth i0 h1 idx) (nth i0 h2 idx) (nth i0 h3 idx).
Proof.
case: (k < idx)%nat / leqP => /= hidx; last first.
  rewrite !(nth_default _) ?scaler0 ?add0r ?size_tuple //.
by rewrite hh (nth_map 0) ?nth_zip ?(nth_map 0) ?size_tuple.
Qed.

Lemma linear_cons k tn (v1 v2 v3 : hist k.+1 tn) :
  v1 = c *: v2 + v3 <-> thead v1 = c *: thead v2 + thead v3 /\
       [tuple of behead v1] = c *: [tuple of behead v2] + [tuple of behead v3].
Proof.
rewrite !addt_cons !scalet_cons /=; split=> [-> | [hh /(congr1 val) /= ht]].
  by rewrite !theadE; split; apply/val_inj.
by apply/val_inj; rewrite [v1]tuple_eta !theadE /= hh ht.
Qed.

Lemma behead_hist_linear k tn (v1 v2 v3 : hist k.+1 tn) :
  v1 = c *: v2 + v3 -> behead_hist v1 = c *: behead_hist v2 + behead_hist v3.
Proof. by case/linear_cons. Qed.

Lemma behead_linear k Γ (Θ1 Θ2 Θ3 : env k.+1 Γ) :
      env_linear Θ1 Θ2 Θ3 ->
      let: Θ1' := behead_env Θ1 in
      let: Θ2' := behead_env Θ2 in
      let: Θ3' := behead_env Θ3 in
      env_linear Θ1' Θ2' Θ3'.
Proof.
elim: Γ Θ1 Θ2 Θ3 => //= tn Γ ihΓ [v1 Θ1] [v2 Θ2] [v3 Θ3] /= [h1 h2].
by split; [apply: behead_hist_linear | apply: ihΓ].
Qed.

(* TODO: - What about the implicits in "I : I n" *)
Definition linnP n (I : I n) :=
  forall k (p : (k < n)%nat) Γ (Θ1 Θ2 Θ3 : env k Γ) (tn : nat) (e : expr Γ tn),
    env_linear Θ1 Θ2 Θ3 ->
    I _ p _ _ e Θ1 = c *: I _ p _ _ e Θ2 + I _ p _ _ e Θ3.

(* open type int *)
Definition ooI n Γ t := forall k : nat, (k <= n)%N -> env k Γ -> tyI k t.

Definition olinnP n Γ (tn : nat) (I : oI n Γ tn) :=
  forall k (hk : (k <= n)%nat) (Θ1 Θ2 Θ3 : env k Γ),
    env_linear Θ1 Θ2 Θ3 ->
    I _ hk Θ1 = c *: I _ hk Θ2 + I _ hk Θ3.

Lemma accI_linear Γ (tn : nat) k n (hk : (k <= n)%N) (g1 g2 g3 : env k Γ)
      (I : ooI n Γ tn) (HI : olinnP I)
      (hΘ : env_linear g1 g2 g3) :
  accI I hk g1 = c *: accI I hk g2 + accI I hk g3.
Proof.
elim: k hk g1 g2 g3 hΘ => [|k ihk] hk g1 g2 g3 hΘ; apply/val_inj.
  by rewrite /= (HI _ _ _ _ _ hΘ).
have hΘ' := behead_linear hΘ.
by rewrite /= -/accI (ihk _ _ _ _ hΘ') (HI _ _ _ _ _ hΘ).
Qed.

Definition ffI n Γ tn := forall k : nat, (k < n)%N -> env k Γ -> tyI k tn.

Definition flinnP n Γ (tn : nat) (I : fI n Γ tn) :=
  forall (tn : nat) k (hk : (k < n)%nat) (Θ1 Θ2 Θ3 : env k Γ),
    env_linear Θ1 Θ2 Θ3 ->
    I _ hk Θ1 = c *: I _ hk Θ2 + I _ hk Θ3.

Lemma accF_linear Γ (tn : nat) k n (hk : (k <= n)%N) (g1 g2 g3 : env k Γ)
      (I : ffI n Γ tn) (HI : flinnP I)
      (hΘ : env_linear g1 g2 g3) :
  accF I hk g1 = c *: accF I hk g2 + accF I hk g3.
Proof.
elim: k hk g1 g2 g3 hΘ => [|k ihk] hk g1 g2 g3 hΘ; apply/val_inj.
  by rewrite /= scaler0 add0r.
have hΘ' := behead_linear hΘ.
by rewrite /= -/accF (ihk _ _ _ _ hΘ') (HI _ _ _ _ _ _ hΘ').
Qed.

(* forall k : nat (k < n)%N (Γ : seq nat) (t : ty), expr Γ t -> env k Γ -> tyI k t *)

(* Definition fI n Γ := forall t k : nat, (k < n)%N -> env k Γ -> tyI k t. *)

(* This has to be cleaned up. *)
Definition hlinnP n (I : I n) := forall m Γ (e : expr (m :: Γ) m) , flinnP
    (fun (k : nat) (hk : (k < n)%N) =>
     I k hk Γ m (feed e)).

Definition hlinnP' n (I : I n) := forall (t : nat) Γ (e : expr Γ t) , flinnP
    (fun (k : nat) (hk : (k < n)%N) => I k hk Γ t e).

Lemma rel_linear_fund Γ t (e : expr Γ t) n (I : I n) (HI : hlinnP' I) :
  forall k (hk : (k < n.+1)%N) (g1 g2 g3 : env k Γ) ,
    env_linear g1 g2 g3      ->
    let: v1 := exprI I hk e g1 in
    let: v2 := exprI I hk e g2 in
    let: v3 := exprI I hk e g3 in
    rel_linear v1 v2 v3.
Proof.
elim: Γ t / e => /=
    [ m Γ idx
    | m Γ e1 ihe1 e2 ihe2
    | m Γ d e ihe
    | m Γ o e1 ihe1 e2 ihe2
    | m Γ o e ihe
    | m Γ e ihe
    | m o Γ e ihe
    | m Γ o e1 ihe1 e2 ihe2
    ] k hk g1 g2 g3 hΘ.
- exact/get_hist_linear/get_env_linear.
- by rewrite scalerDr addrACA; congr (_ + _); auto.
- by rewrite scalerA mulrC -scalerA -scalerDr; congr (_ *: _); auto.
- by rewrite scale_col_mx add_col_mx; congr col_mx; auto.
- by rewrite (ihe _ _ _ g2 g3) //; apply/matrixP=> ? ?; rewrite !mxE.
- by apply: ihe; split => //; apply/accF_linear.
- by move=> x1 x2 x3 hva; apply: ihe.
- exact/ihe1/accI_linear.
Qed.

End Linear.

Corollary funS n k (p : (k <= n)%nat) a b (f : expr [::] (tfun a b)) :
  let f := exprIn p f tt in
  scalable f.
Proof.
move=> fi x y.
have He: @env_scale x k [::] tt tt by [].
exact/(rel_scalePn p f He).
Qed.

Corollary funP n k (p : (k <= n)%nat) a b (f : expr [::] (tfun a b)) :
  let f := exprIn p f tt in
  lmorphism f.
Proof. by move=> fi; split; [exact/funD|exact/funS]. Qed.

Canonical fun_linearP n k p a b f := Linear (@funP n k p a b f).

(* Open functions however need to evaluated on a scaled context. *)
Corollary ofunS n k (p : (k <= n)%nat) a b Γ θ (f : expr Γ (tfun a b)) :
  let f θ := exprIn p f θ in
  scalable (f θ).
Proof.
move=> fi x y.
set θ' := hmap (fun _ => [eta *:%R x]) θ; rewrite /= in θ'.
have He: @env_scale x k Γ θ' θ.
  by rewrite /θ'; elim: Γ θ {θ' f fi} => /=.
have /= <- := rel_scalePn p f He (x *: y) y erefl; rewrite /fi {fi}; set fi := exprIn _ _.
Admitted.


End Linearity.
End Wagner.

Print Assumptions funP.
About funP.

Print Assumptions funD.
About funD.
(* Closed under the global context:

   funD : forall (R : idomainType) (n k : nat) (p : k <= n)
     (a b : nat) (f : expr R [::] (tfun a b)), additive (exprIn p f tt)

*)

Print Assumptions funS.
About funS.

Section Tests.

Variable (D : idomainType) (c : D).

Definition id  n : expr D [::] (tfun n n) := lam (var D 0 [:: n] 0).
Definition time n : expr D [::] (tpair n) := feed (mul c (var D 0 [:: n] 0)).

Lemma id_is_id k n (p : k <= n) j (x : 'cV[D]_j) :
  exprIn p (app (id j) (time j)) tt  = exprIn p (time j) tt.
Proof. by elim: n k p => [|n ihn] [|k] p. Qed.

Definition delay1 n G : expr D G (tfun n n) := lam (var D 0 [:: n & G] 1).
Definition delay2 n G : expr D G (tfun n n) := lam (var D 0 [:: n & G] 2).

(* Lemma double_shift k n (p : k <= n) j (x : 'cV[D]_j) G : *)
Lemma double_shift (p : 3 <= 4) j (x : 'cV[D]_j) G :
  exprIn p (lam (app (@delay1 _ _) (var _ 0 _ 1))) =2
  exprIn p (@delay2 1 G).
Proof.
move=> env input /=.
suff [i1 [i2 [i3 hi]]] : { x & { y & { z | input = [tuple x; y; z] } } }.
  by rewrite hi.
case: {p j x env G}input.
case=> [|a1] //; case=> [|a2] //; case=> [|a3]; case => //.
by move=> ?; exists a1, a2, a3; apply/val_inj.
Qed.

End Tests.
