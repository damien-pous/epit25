From epit Require Import utils.
From Coinduction Require Import lattice.
Arguments Datatypes.id {_} _/.
Instance rw_leq {X} {L: CompleteLattice X}: RewriteRelation (@leq X L) := {}.

(** * Abstract theory of coinduction via the final chain and tower induction *)

Module KnasterTarski. 
Section s.
 Context {X} {L: CompleteLattice X}.
 Variable b: mon X.

 Lemma sup_of_pfp_pfp (Y: X -> Prop):
   (forall y, Y y -> y <= b y) -> sup Y <= b (sup Y).
 Proof.
   intro H.
   apply sup_spec. cbn.
   intros y Yy.
   rewrite (H y Yy). 
   apply b.
   by apply leq_xsup. 
 Qed.
 
 Definition gfp := sup (fun x => x <= b x).

 Theorem fixpoint_gfp: b gfp == gfp.
 Proof.
   have post: gfp <= b gfp.
   by apply sup_of_pfp_pfp.
   apply antisym; trivial.
   apply leq_xsup. by apply b.
 Qed.
End s.
End KnasterTarski. 

Section s.

 Context {X} {L: CompleteLattice X}.

 

 
 (** inf-closed predicates *)
 Definition inf_closed (P: X -> Prop) := forall T, T <= P -> P (inf T).

 Lemma inf_closed_cap P Q: inf_closed P -> inf_closed Q -> inf_closed (cap P Q).
 Proof.
   intros HP HQ T. rewrite cap_spec; intros [TP TQ].
   split. now apply HP. now apply HQ.
 Qed.
 Lemma inf_closed_all A (P: A -> X -> Prop): (forall a, inf_closed (P a)) -> inf_closed (fun x => forall a, P a x).
 Proof.
   intros HP T TP a. apply HP. intros ??. now apply TP. 
 Qed.
 Lemma inf_closed_impl (P Q: X -> Prop): Proper (leq ==> leq) P -> inf_closed Q -> inf_closed (fun x => P x -> Q x).
 Proof.
   intros HP HQ T HT H. apply HQ. 
   intros x Hx. apply HT. trivial.
   revert H. apply HP. now apply leq_infx.
 Qed.
 Lemma inf_closed_leq (f: mon X): inf_closed (fun x => f x <= x).
 Proof.
   intros T HT. apply inf_spec. intros x Tx.
   transitivity (f x). now apply f, leq_infx.
   now apply HT. 
 Qed.
 
 Variable b: mon X.

 (** * Final chain as an inductive predicate *)

 (** the set of all (transfinite) iterations of b 
     although this set is (classically) a chain, we never need to know it *)
 Inductive C: X -> Prop :=
 | Cb: forall x, C x -> C (b x)
 | Cinf: forall T, T <= C -> C (inf T).

 (** a type for the elements of the chain *)
 Structure Chain := chain { elem:> X; #[canonical=no] Celem: C elem}.

 (** the chain is closed under [b] *)
 Canonical Structure chain_b (x: Chain) := {| elem := b x; Celem := Cb (Celem x) |}.

 (** ** the greatest fixpoint is the least element of the final chain *)
 Definition gfp := inf C.

 (** the gfp belongs to the chain *)
 Canonical Structure chain_gfp := {| elem := gfp; Celem := Cinf (reflexivity C) |}. 
 Corollary gfp_prop (P: X -> Prop): (forall x: Chain, P x) -> P gfp.
 Proof. now intro. Qed.

 Lemma gfp_pfp: gfp <= b gfp.
 Proof. apply leq_infx, chain_b. Qed.
 
 (** tower induction principle (just a rephrasing of induction on the Chain predicate *)
 Proposition tower (P: X -> Prop):
   inf_closed P ->
   (forall x: Chain, P x -> P (b x)) ->
   (forall x: Chain, P x).
 Proof.
   intros Hinf Hb [x Cx]; cbn.
   induction Cx; auto.
   now apply (Hb (chain Cx)).
 Qed.

 (** elements of the chain are closed under [b] *)
 Lemma b_chain: forall x: Chain, b x <= x.
 Proof.
   apply (tower (inf_closed_leq _)).
   intros; now apply b.
 Qed.
 
 (** [gfp] is below all elements of the chain (by definition) *)
 Lemma gfp_chain (x: Chain): gfp <= x.
 Proof. apply leq_infx, x. Qed.
 
 (** [gfp] is indeed a fixpoint  *)
 Theorem gfp_fp: b gfp == gfp.
 Proof. apply antisym. apply b_chain. apply gfp_pfp. Qed.

 (** and indeed the largest (post)-fixpoint *)
 Theorem leq_gfp x: x <= b x -> x <= gfp.
 Proof.
   intro H. apply gfp_prop.
   apply (tower (inf_closed_leq (const x))); cbn.
   intros y xy. now rewrite H, xy. 
 Qed.

 Definition compat f := f ° b <= b ° f.
 Lemma compat_chain (x: Chain): forall f, compat f -> f x <= x.
 Proof.
   intros f Hf. revert x. apply (tower (inf_closed_leq _)). 
   intros x fx. rewrite (Hf x). now apply b. 
 Qed.

End s.
