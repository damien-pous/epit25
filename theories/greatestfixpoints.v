From epit Require Import coinduction.

(** Abstract theory of greatest fixpoints, in complete lattices *)

(** * 1. Knaster-Tarskki *)


Module KnasterTarski. 
Section s.
 (** We assume a monotone function [b] on a complete lattice [X] *)
 Context {X} {L: CompleteLattice X}.
 Variable b: mon X.

 (** All we need to know about complete lattices is that we have a function
     [sup: (X -> Prop) -> X]
     satisfying
     [sup_spec: forall P z, sup P <= z <-> forall x, P x -> x <= z]
     from which we deduce
     [leq_xsup: forall P x, P x -> x <= sup P]
  *)
 
 (** The greatest fixpoint can be defined as the supremum of all postfixpoints *) 
 Definition gfp := sup (fun x => x <= b x).

 (** It is a postfixpoint (any supremum of postfixpoints is so) *)
 Lemma postfixpoint_gfp: gfp <= b gfp.
 Proof.
   apply sup_spec; cbn.
   intros x Hx.
   rewrite Hx. 
   apply b.
   apply leq_xsup.
   assumption. 
 Qed.
 
 (** It is a fixpoint (and by definition, the largest one) *) 
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

 (** Dually from before, all we need to know about complete lattices is that we have a function
     [inf: (X -> Prop) -> X]
     satisfying
     [inf_spec: forall P z, z <= inf P <-> forall x, P x -> z <= x]
     from which we deduce
     [leq_infx: forall P x, P x -> inf P <= x]

     (note that we are still looking for greatest fixpoints!)
  *)

 
 (** inf-closed predicates *)
 Definition inf_closed (P: X -> Prop) := forall T, T <= P -> P (inf T).

 (** ** The final chain as an inductive predicate
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
 | Cb: forall x, C x -> C (b x).       (* closure under [b] *)

 (** The greatest fixpoint can be defined as the least element of the final chain *)
 Definition gfp := inf C.

 (** It is a postfixpoint *)
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

 (** Hence any property holding universally on the chain holds for [gfp] *)
 Corollary gfp_prop (P: X -> Prop): (forall c, C c -> P c) -> P gfp.
 Proof. apply. apply chain_gfp. Qed.

 (** Given that the chain is defined as an inductive predicate,
     we can proceed by induction to prove such properties:
     any predicate which is closed under infimas and b must contain the whole chain
     this is called `tower induction' 
     (cf. Steven Schäfer, Gert Smolka:
     Tower Induction and Up-to Techniques for CCS with Fixed Points. RAMiCS 2017)
  *)

 (** Elements of the chain are prefixpoints (by tower induction) *)
 Lemma prefixpoint_chain: forall c, C c -> b c <= c.
 Proof.
   induction 1 as [D DC IHD|c IHc].
   - apply inf_spec=>d Dd. transitivity (b d).
     by apply b, leq_infx. by apply IHD. 
   - by apply b.
 Qed.

 (** Hence [gfp] is a fixpoint  *)
 Theorem fixpoint_gfp: gfp == b gfp.
 Proof.
   apply antisym.
   - apply postfixpoint_gfp.
   - apply prefixpoint_chain, chain_gfp.
 Qed.

 (** And in fact the largest (post)-fixpoint (by tower induction again) *)
 Theorem largest_gfp x: x <= b x -> x <= gfp.
 Proof.
   intro Hx. apply gfp_prop. 
   induction 1 as [D DC IHD|c Cc IHc].
   - apply inf_spec=> d Dd. apply IHD, Dd.
   - rewrite Hx. by apply b.
 Qed.

End s.

(** * Notes

    see "Introduction to lattices and order", by Davey and Priestley, for a very nice book on such topics.

    This way of getting a greatest fixpoint of a monotone map can be generalised to complete partial orders (where only directed infs are available)
    - one path consists in proving that the chain is indeed a chain (i.e., totally ordered), which requires classical logic
    - or to use transfinite recursion to define it and argue that there must be an ordinal from which it is constant (requires ordinals + cardinal analysis)
    - but it suffices to show that it is directed, which Pataraia showed how to do constructively.

    If the montone map is further assumed to be continuous (preserves ω infs), then we can stop the iteration at ω and define the chain by induction on natural numbers:
    [gfp b = \inf_{i∈ω} b^i⊤]
    This last case is a special case of the proof Daniela gave for constructing the final coalgebra

 *)
