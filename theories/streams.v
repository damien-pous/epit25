From epit Require Import coinduction.
Require Import Psatz.           (* for the [nia/lia] tactics about integer arithmetic *)
Unset Primitive Projections.

(** * 0. streams *)

(** Here we only consider streams of natural numbers, for the sake of simplicity *)
CoInductive stream := cons{hd: nat; tl: stream}.
Infix "::" := cons. 

(** Some streams, defined by corecursion *)
CoFixpoint const n := n :: const n. 
CoFixpoint alt n m := n :: alt m n.
CoFixpoint single n := n :: single 0. 

(** Recall the notion of bisimulation from Daniela's course *)
Definition bisimulation (R: relation stream) :=
  forall s t, R s t -> hd s = hd t /\ R (tl s) (tl t).































(** * 1. using Rocq's support for coinductive predicates to define bisimilarity *)

(** One could typically define bisimilarity as the union of all bisimulations,
    or, as in the following line, as a Rocq coinductive predicate *)
CoInductive native_bisim: relation stream :=
| bis: forall s t, hd s = hd t /\ native_bisim (tl s) (tl t) -> native_bisim s t.

(** [native_bisim] is indeed a bisimulation (by its only constructor) *)
Lemma bisimulation_native_bisim: bisimulation native_bisim.
Proof. by intros s t []. Qed.

(** We can prove simple laws by Rocq coinduction *)
Lemma alt_nn_native n: native_bisim (alt n n) (const n).
Proof.
  (** start the proof by coinduction *)
  cofix CH.
  (** use constructor to make sure we are guarded *)
  constructor. cbn.
  split. 
  - reflexivity.                (** compare the heads *)
  - exact CH.                   (** use coinduction hypothesis for the tails *)
Qed.

(** [native_bisim] is the largest bisimulation (by Rocq coinduction again) *)
Lemma native_bisim_largest_bisimulation R: bisimulation R -> R <= native_bisim.
Proof.
  intro HR.
  cofix CH.
  intros x y xy.
  specialize (HR _ _ xy).
  (** three more lines - take inspiration from the previous proof *)
Admitted.



































(** * 2. using the [coinduction] library to define bisimilarity *)


(** Consider instead the following monotone function on relations
    (note that relations, of type [stream -> stream -> Prop], form a complete lattice)  *)
Program Definition b: mon (stream -> stream -> Prop) :=
  {| body R s t := hd s = hd t /\ R (tl s) (tl t) |}.
Next Obligation.
  (** here we prove monotonicity, which is rather trivial *)
  firstorder.
Qed.

(** Its postfixpoints are precisely the bisimulations *)
Remark postfixpoint_bisimulation R: R <= b R <-> bisimulation R.
Proof. reflexivity. Qed.

(** Hence, its greatest fixpoint is bisimilarity---we take this as the definition *)
Notation bisim := (gfp b).
Infix "~" := bisim (at level 70).

(** [bisim] is indeed a bisimulation (being a post-fixpoint of [b], lemma [gfp_pfp]) *)
Lemma bisimulation_bisim: bisimulation bisim.
Proof. exact (gfp_pfp b). Qed.

(** Whence the following basic properties *)
Instance hd_bisim: Proper (bisim ==> eq) hd.
Proof. intros x y H. apply bisimulation_bisim, H. Qed.
Instance tl_bisim: Proper (bisim ==> bisim) tl.
Proof. intros x y H. apply bisimulation_bisim, H. Qed.

(** Also note that the two definition of bisimilarity seen so far coincide *)
Remark sanity_check: bisim == native_bisim.
Proof.
  apply antisym.
  - apply native_bisim_largest_bisimulation, bisimulation_bisim.
  - apply leq_gfp, bisimulation_native_bisim.
Qed.












































(** * 3. Proving bisimilarity laws by tower induction *)

(** Let us prove the same law as before, with our definition of bisimilarity, by tower induction *)
Lemma alt_nn n: alt n n ~ const n.
Proof.
  (** rather than proving the statement, we generalize to all elements on the chain *)
  apply gfp_prop.
  (** so that we can proceed by `tower induction' *)
  apply (tower (P:=fun R => R (alt n n) (const n))).
  - (** we have to show that our property is inf_closed, which is easy (and boring)  *)
    intros D DC R HR. by apply DC. 
  - (** and that it is closed under [b], which is the where we expect to do the real work *)
    (** even though we proceed by induction, [HR] should be thought of as a coinduction hypothesis *)
    intros R HR.

    
Admitted.

(** The [coinduction] library provides the tactic [coinduction],
    which automates the bureaucratic steps (in particular, it proves inf_closure automatically) *)
Lemma alt_nn_bis n: alt n n ~ const n.
Proof.
Admitted.

























(** * pointwise sum and its properties *)

CoFixpoint plus s t := hd s + hd t :: plus (tl s) (tl t).
Infix "+" := plus.

Lemma plusC: forall x y, x + y ~ y + x.
Proof.
  coinduction R HR. intros x y. cbn.
  (* one line each *)
Admitted.

Lemma plusA: forall x y z, x + (y + z) ~ (x + y) + z.
Proof.
Admitted.

Notation zeros := (single 0).  

Lemma plus_0x x: zeros + x ~ x.
Proof.
Admitted.




























Lemma unfold_zeros: zeros ~ 0 :: zeros. 
Proof.
  coinduction R HR. cbn. split.
  - reflexivity.
  -                             (* ?? *)
Abort.




























(** Elements of the final chain are equivalence relations (and in particular bisimilarity itself)
    this property makes it possible to use "up-to equivalence" techniques in the subsequent proofs, implicitly *)
Instance Equivalence_chain_b {R: Chain b}: Equivalence (elem R).
Proof.
  split; revert R.

  Check Reflexive_chain. 
Admitted.

Lemma zeros_const: zeros ~ 0 :: zeros. 
Proof.
  coinduction R HR. cbn. split.
  - reflexivity.
  -                          (* now we do know that [R] is reflexive*)
Admitted.






























(** * shuffle product *)

(** this is the following binary operation on streams [s,t]:
    [(s@t)_k = Σ_{i+j=k} (i k) s_i t_j]
    it can be characterised by the following equations:
    [hd (s@t) = hd s * hd t]
    [tl (s@t) = tl s @ t  +  s @ tl t]
 *)

(** It be defined as easily as one could expect in Coq, 
    because of the guard condition: *)
Fail CoFixpoint shuff s t :=
  hd s * hd t :: shuff (tl s) t + shuff s (tl t).

(** Here we simply assume its existence for the sake of simplicity. *)
Parameter shuf: stream -> stream -> stream.
Infix "@" := shuf (at level 40, left associativity).
Axiom hd_shuf: forall s t, hd (s @ t) = hd s * hd t.
Axiom tl_shuf: forall s t, tl (s @ t) = tl s @ t + s @ tl t.
Ltac cbn_shuf := repeat (rewrite ?hd_shuf ?tl_shuf; simpl hd; simpl tl).

Lemma shuf_0x: forall x, zeros @ x ~ zeros.
Proof.
  coinduction R HR. intros x. split; cbn_shuf.
  - nia.
  - Fail rewrite HR.            (** why? *)
Abort.

































(** addition corresponds to a compatible function and preserves the final chain
    hence bisimilarity is compatible with addition as a special case,
    and we can implicit use an "upto + " technique in the subsequent proofs
 *)
Instance plus_chain: forall {R: Chain b}, Proper (elem R ==> elem R ==> elem R) plus.
Proof.
  (** [Proper_chain] is a generic helper to show by tower induction that
      elements of the chain are preserved by a given function (here, plus) *)
  apply (Proper_chain 2). unfold respectful_iter. 
  intros R HR x y xy u v uv.
Admitted.

Lemma shuf_0x: forall x, zeros @ x ~ zeros.
Proof.
  coinduction R HR. intros x. split; cbn_shuf.
  - nia.
  - (** now we know that [R] is a congruence relation, and we can use rewriting *)
Admitted.
(** such a proof using an up-to congruence technique would typically not be guarded with native coinduction *)





























Notation one := (single 1).

Lemma shuf_1x: forall x, one @ x ~ x.
Proof.
  coinduction R HR. intros x. split; cbn_shuf.
  - nia.
  - 
Admitted.

Lemma shufC: forall x y, x @ y ~ y @ x.
Proof.
  coinduction R HR. intros x y. split; cbn_shuf.
  - nia.
  - 
Admitted.

Lemma shuf_x_plus: forall x y z, x @ (y + z) ~ x@y + x@z.
Proof.
  coinduction R HR. intros x y z. split; cbn_shuf.
  - nia.
  - (** this one is harder, a few lines *)
Admitted.

Lemma shuf_plus_x: forall x y z, (y + z)@x ~ y@x + z@x.
Proof.
  (** hint: look for a proof without coinduction *)
Admitted.

Lemma shufA: forall x y z, x @ (y @ z) ~ (x @ y) @ z.
Proof.
  coinduction R HR. intros x y z. split; cbn_shuf.
  - nia.
  - (** a few lines again *)
Admitted.

(** shuffle product preserves the final chain
    (not used in the sequel, but would be required to perform proofs "up-to shuffle product") *)
Instance shuf_chain: forall {R: Chain b}, Proper (elem R ==> elem R ==> elem R) shuf.
Proof.
  apply (Proper_chain 2). unfold respectful_iter. 
  intros R HR x y xy u v uv. 
  pose proof xy as [xy0 xy'].
  pose proof uv as [uv0 uv'].
  split; cbn_shuf.
  - congruence.
  - by rewrite xy' uv' xy uv.   (** difficult: why does the [rewrite xy uv] works? *)
Qed.






(** * convolution product *)
(** this is the following binary operation on streams [s,t]:
    [(s*t)_k = Σ_{i+j=k} s_i t_j]
    (note that the binomial coefficient has disappeared)

    it can be characterised by the following equations:
    [hd (s*t) = hd s * hd t]
    [tl (s*t) = tl s * t + hd s ** tl t]
    There [**] is pointwise multiplication by a scalar, which is a special case of convolution product:
    [x ** s = single x * s]
    (Remember that [single x] is the stream [x,0,0,...] )
 *)

(** Like before, we cannot define it as one could expect in Coq, 
    because of the guard condition: *)
Fail CoFixpoint mult s t :=
  hd s * hd t :: mult (tl s) t + mult (single (hd s)) (tl t).

(** Here we simply assume its existence for the sake of simplicity. *)
Parameter mult: stream -> stream -> stream.
Infix "*" := mult.
Axiom hd_mult: forall s t, hd (s * t) = (hd s * hd t)%nat.
Axiom tl_mult: forall s t, tl (s * t) = tl s * t + (single (hd s)) * tl t.
Ltac cbn_mult := repeat (rewrite ?hd_mult ?tl_mult; simpl hd; simpl tl).

Lemma mult_0x: forall x, zeros * x ~ zeros.
Proof.
  coinduction R HR. intros x. split; cbn_mult.
  - nia.
  -
Admitted.

Lemma mult_x0: forall x, x * zeros ~ zeros.
Proof.
  coinduction R HR. intros x. split; cbn_mult.
  - nia.
  -
Admitted. 

Lemma mult_1x: forall x, one * x ~ x.
Proof.
  coinduction R HR. intros x. split; cbn_mult.
  - lia.
  -
Admitted. 

Lemma mult_x1: forall x, x * one ~ x.
Proof.
  coinduction R HR. intros x. split; cbn_mult.
  - lia.
  -
Admitted. 

Lemma mult_x_plus: forall x y z, x * (y + z) ~ x*y + x*z.
Proof.
  coinduction R HR. intros x y z. split; cbn_mult.
  - nia. 
  -                             (** a few lines  *)
Admitted. 

Lemma single_plus n m: single (n+m) ~ single n + single m.
Admitted. 

Lemma single_mult n m: single (n*m) ~ single n * single m.
Admitted. 

(** convolution product preserves the final chain
    (required to do proofs up to convolution product below) *)
Instance mult_chain: forall {R: Chain b}, Proper (elem R ==> elem R ==> elem R) mult.
Admitted.                       (** take inspiration from previous similar proofs...  *)

Lemma mult_plus_x: forall x y z, (y + z) * x ~ y*x + z*x.
Admitted. 

Theorem multA: forall x y z, x * (y * z) ~ (x * y) * z.
Admitted. 

(** below: commutativity of convolution product is harder,
    here we propose to follow Jan Rutten's proof *)
     
Lemma multC_n n: forall x, single n * x ~ x * single n.
Admitted. 

(** X is the stream [0::1::zeros] (think of power series...)  *)
Definition X := 0 :: one.

Theorem expand x: x ~ single (hd x) + X * tl x.
Admitted. 

Lemma multC_11 x: tl (X * x) ~ x.
Admitted. 

Lemma multC_X: forall x, X * x ~ x * X. 
Admitted. 

Theorem multC: forall x y, x * y ~ y * x.
Admitted. 




(** * closing the loop: streams form the final coalgebra of the functor [nat × X] *)

From epit Require ex_setoids.

Canonical stream_setoid := Setoid.build stream bisim Equivalence_chain_b.

Program Definition stream_coalg: Coalgebra (ex_setoids.F_times nat) :=
  {| coalg_car := stream_setoid;
     coalg_mor := (efun s => (hd s, tl s)) |}. 
Next Obligation. 
  split. by apply hd_bisim. by apply tl_bisim. 
Qed.

CoFixpoint stream_coiter {X} (f: X -> nat×X) x :=
  cons (f x).1 (stream_coiter f (f x).2).

Lemma stream_coiter_eqv {X: Setoid} (f: X -eqv-> nat×X): 
    Proper (eqv ==> bisim) (stream_coiter f).
Proof.  
  unfold Proper, respectful.
  coinduction R HR.
  intros x y xy. apply f in xy.
  split.
  - apply xy.
  - apply HR, xy.
Qed.

Theorem final_stream_coalg: final stream_coalg.
Proof.
  split.
  - intros [X f]. esplit. exists (stream_coiter f).
    -- apply stream_coiter_eqv.
    -- done. 
  - intros [X h] [f Hf] [g Hg]. cbn in *. 
    coinduction R HR; intro x.
    destruct (Hf x) as [fx1 fx2].
    destruct (Hg x) as [gx1 gx2].
    split.    
    -- by rewrite fx1 gx1. 
    -- by rewrite fx2 gx2.       
    (** such a proof would not be guarded with native coinduction, due
    to the implicit upto technique used in the last line (rewriting to
    work modulo bisimilarity before applying the coinduction
    hypothesis) *)
Qed.


(** * Conclusion

  1. Inductives in Rocq correspond to initial algebras
     nat    = μX.1+X
     list A = μX.1+A×X
     trees  = μX.list X
     ...

  2. CoInductives in Rocq do not exactly correspond to final coalgebras
     (one can prove existence but not unicity of the required coalgebra homomorphisms)
     We can get final coalgebras out of them if we quotient by the appropriate notion of bisimilarity

  3. Bisimilarity can be defined
     - as a native coinductive predicate, but then we suffer with the guard condition in proofs (not illustrated here for lack of time, trust us...)
     - as the greatest fixpoint of a monotone map [b]

  4. The coinduction library defines such a fixpoint as the least element of the chain of [b]
     This gives a powerful `tower induction principle':
     to prove that a property holds for all elements of the chain, prove that it is
     - inf-closed (easy+boring)
     - closed under [b] (where the interesting things happen)

  5. Thus we can systematically state and prove universal properties of the chain rather than just bisimilarity (all elements are equivalence relations, congruences, ...).
     Doing so we get access to powerful up-to techniques (bisimulation up-to equivalence, up-to congruence, ...)

  6. This idea works very smoothly in Rocq, for arbitrary coinductive predicates.

     It remains to deal with coinductive *datatypes*
     For instance, the guard condition makes it difficult to define the shuffle/convolution product.

     It is however not clear how scale the idea of tower induction: while Prop is a complete lattice, Type is not.
     We are working on other approaches, based on coalgebras, containers and polynomial functors.

 *)
