From epit Require Import coinduction.

(** abstract theory of greatest fixpoints, in complete lattices *)

(** * 1. Knaster-Tarskki *)


Module KnasterTarski. 
Section s.
 (** we assume a monotone function [b] on a complete lattice [X] *)
 Context {X} {L: CompleteLattice X}.
 Variable b: mon X.

 (** all we need to know about complete lattices is that we have a function
     [sup: (X -> Prop) -> X]
     satisfying
     [sup_spec: forall P z, sup P <= z <-> forall x, P x -> x <= z]
     from which we deduce
     [leq_xsup: forall P x, P x -> x <= sup P]
  *)
 
 (** the greatest fixpoint can be defined as the supremum of all postfixpoints *) 
 Definition gfp := sup (fun x => x <= b x).

 (** it is a postfixpoint (any supremum of postfixpoints is so) *)
 Lemma postfixpoint_gfp: gfp <= b gfp.
 Proof.
   apply sup_spec; cbn.
   intros x Hx.
   rewrite Hx. 
   apply b.
   apply leq_xsup.
   assumption. 
 Qed.
 
 (** it is a fixpoint (and by definition, the largest one) *) 
 Theorem fixpoint_gfp: gfp == b gfp.
 Proof.
   apply antisym.
   - apply postfixpoint_gfp.
   - apply leq_xsup.
     apply b.
     apply postfixpoint_gfp.
     (* the second part if this proof actually is (Co)Lambek's lemma *)
 Qed.
End s.
End KnasterTarski. 


(** * 2. Kleene / final chain *)

Section s.

 Context {X} {L: CompleteLattice X}.
 Variable b: mon X.
 
 (** inf-closed predicates *)
 Definition inf_closed (P: X -> Prop) := forall T, T <= P -> P (inf T).

 (** for every monotone function [f], the predicate [f x <= x] is closed under infima *)
 Lemma inf_closed_leq (f: mon X): inf_closed (fun x => f x <= x).
 Proof.
   intros T HT. apply inf_spec. intros x Tx.
   transitivity (f x). by apply f, leq_infx.
   by apply HT. 
 Qed.

 (** ** the final chain as an inductive predicate
     below, C is the least predicate/set which is closed under b and under infima.
     intuitively, it contains all transfinite iterations of [b]:
     
     ⊤, b⊤, bb⊤, ..., b^i⊤, ...
     b^ω⊤ = \inf_{i∈ω} b^i⊤, bb^ω\top, ..., b^ω+i⊤, ...
     ...

     we do not need ordinals to define it, fortunately,
     and although this set is (classically) a chain, we never need to prove it,
  *)
 Inductive C: X -> Prop :=
 | Cinf: inf_closed C            (* closure under infima *)
 | Cb: forall x, C x -> C (b x).       (* closure under b *)

 (** the greatest fixpoint can be defined as the least element of the final chain *)
 Definition gfp := inf C.

 (** it is a postfixpoint *)
 Lemma postfixpoint_gfp: gfp <= b gfp.
 Proof.
   apply leq_infx.
   apply Cb.
   apply Cinf.
   reflexivity.
 Qed.

 (** [gfp] belongs to the chain (by definition) *)
 Lemma chain_gfp: C gfp.
 Proof. by apply Cinf. Qed.

 (** hence any property holding universally on the chain holds for [gfp] *)
 Corollary gfp_prop (P: X -> Prop): (forall c, C c -> P c) -> P gfp.
 Proof. apply. apply chain_gfp. Qed.

 (** given that the chain is defined as an inductive predicate,
     we an proceed by induction to prove such properties:
     any predicate which is closed under infimas and b must contain the whole chain
     this is called `tower induction' 
     (cf. Steven Schäfer, Gert Smolka:
     Tower Induction and Up-to Techniques for CCS with Fixed Points. RAMiCS 2017: 274-289)
  *)

 (** elements of the chain are prefixpoints (by tower induction) *)
 Lemma prefixpoint_chain: forall c, C c -> b c <= c.
 Proof.
   induction 1 as [D DC IHD|c IHc].
   - by apply inf_closed_leq. 
   - by apply b.
 Qed.

 (** hence [gfp] is a fixpoint  *)
 Theorem fixpoint_gfp: gfp == b gfp.
 Proof.
   apply antisym.
   - apply postfixpoint_gfp.
   - apply prefixpoint_chain, chain_gfp.
 Qed.

 (** and in fact the largest (post)-fixpoint (by tower induction again) *)
 Theorem largest_gfp x: x <= b x -> x <= gfp.
 Proof.
   intro Hx. apply gfp_prop. 
   induction 1 as [D DC IHD|c Cc IHc].
   - apply inf_spec=> d Dd. apply IHD, Dd.
   - rewrite Hx. by apply b.
 Qed.

End s.
