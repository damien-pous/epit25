(** * Rutten's stream calculus *)

From epit Require Import cats.
From epit Require ex_setoids.
Require Import Psatz.
From Coinduction Require Import all. Import CoindNotations.
Unset Primitive Projections. 

(** here we only consider streams of natural numbers, for the sake of simplicity *)
CoInductive stream := cons{hd: nat; tl: stream}.

(** the following monotone function characterises yields bisimilarity as its greatest fixpoint:
    its post-fixpoints are precisely the bisimulations. *)
Program Definition b: mon (stream -> stream -> Prop) :=
  {| body R s t := hd s = hd t /\ R (tl s) (tl t) |}.
Next Obligation. firstorder. Qed.

(** associated relation (bisimularity) *)
Infix "~" := (gfp b) (at level 70).

(** notations  for easing readability in proofs by enhanced coinduction *)
Infix "[~]" := (`_) (at level 70). 
Infix "{~}" := (b `_) (at level 70). 
  
(** elements of the final chain are equivalence relations *)
Instance Equivalence_t {R: Chain b}: Equivalence `R.
Proof.
  constructor; revert R.
  - apply Reflexive_chain. intros R HR x. by split.
  - apply Symmetric_chain. intros R HR x y []. by split; symmetry.
  - apply Transitive_chain. intros R HR x y z [] []. split. congruence. etransitivity; eauto. 
Qed.

Instance hd_bisim: Proper (gfp b ==> eq) hd.
Proof. intros x y H. apply (gfp_pfp b), H. Qed.

Instance tl_bisim: Proper (gfp b ==> gfp b) tl.
Proof. intros x y H. apply (gfp_pfp b), H. Qed.

(** * streams form the final coalgebra of the functor [nat × X] *)

Canonical stream_setoid := Setoid.build stream (gfp b) Equivalence_t.

Program Definition stream_coalg: Coalgebra (ex_setoids.F_times nat) :=
  {| coalg_car := stream_setoid;
     coalg_mor := (efun s => (hd s, tl s)) |}. 
Next Obligation. 
  split. by apply hd_bisim. by apply tl_bisim. 
Qed.

CoFixpoint stream_coiter {X} (f: X -> nat×X) x :=
  cons (f x).1 (stream_coiter f (f x).2).

Lemma stream_coiter_eqv {X: Setoid} (f: X -eqv-> nat×X): 
    Proper (eqv ==> gfp b) (stream_coiter f).
Proof.  
  unfold Proper, respectful. coinduction R HR.
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
Qed.



(** * "constant" streams *)
CoFixpoint c n := cons n (c 0).

(** * pointwise sum and its properties *)
CoFixpoint plus s t := cons (hd s + hd t) (plus (tl s) (tl t)).
Infix "+" := plus.

Lemma plusC: forall x y, x + y ~ y + x.
Proof.
  coinduction R HR. intros x y. split; cbn.
  - lia.
  - apply HR.
Qed.

Lemma plus_0x x: c 0 + x ~ x.
Proof.
  revert x. coinduction R HR. intro x. split; cbn.
  - reflexivity.
  - apply HR.
Qed. 

Lemma plusA: forall x y z, x + (y + z) ~ (x + y) + z.
Proof.
  coinduction R HR. intros x y z. split; cbn.
  - lia.
  - apply HR.
Qed.

(** addition corresponds to a compatible function and preserves the final chain *)
Instance plus_chain: forall {R: Chain b}, Proper (`R ==> `R ==> `R) plus.
Proof.
  apply (Proper_chain 2). 
  intros R HR x y [xy0 xy'] u v [uv0 uv'].
  split; cbn.
  - congruence.
  - by apply HR. 
Qed.


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
  cons (hd s * hd t)%nat (shuff (tl s) t + shuff s (tl t)).

(** Here we simply assume its existence for the sake of simplicity. *)
Parameter shuf: stream -> stream -> stream.
Infix "@" := shuf (at level 40, left associativity).
Axiom hd_shuf: forall s t, hd (s @ t) = (hd s * hd t)%nat.
Axiom tl_shuf: forall s t, tl (s @ t) = tl s @ t + s @ tl t.
Ltac cbn_shuf := repeat (rewrite ?hd_shuf ?tl_shuf; simpl hd; simpl tl).

Lemma shuf_0x: forall x, c 0 @ x ~ c 0.
Proof.
  coinduction R HR. intros x. split; cbn_shuf.
  - nia.
  - rewrite HR. rewrite plus_0x. apply HR. 
Qed.

Lemma shuf_1x: forall x, c 1 @ x ~ x.
Proof.
  coinduction R HR. intros x. split; cbn_shuf.
  - lia.
  - rewrite shuf_0x plus_0x. apply HR.
Qed.

Lemma shufC: forall x y, x @ y ~ y @ x.
Proof.
  coinduction R HR. intros x y. split; cbn_shuf.
  - nia.
  - by rewrite HR plusC HR. 
Qed.

Lemma shuf_x_plus: forall x y z, x @ (y + z) ~ x@y + x@z.
Proof.
  coinduction R HR. intros x y z. split; cbn_shuf.
  - nia. 
  - rewrite 2!HR. rewrite 2!plusA. 
    apply plus_chain. 2: reflexivity.
    rewrite <-2plusA. 
    apply plus_chain. reflexivity. by rewrite plusC.
Qed.

Lemma shuf_plus_x: forall x y z, (y + z)@x ~ y@x + z@x.
Proof.
  intros. rewrite shufC shuf_x_plus.
  apply plus_chain; apply shufC.
Qed.

Lemma shufA: forall x y z, x @ (y @ z) ~ (x @ y) @ z.
Proof.
  coinduction R HR. intros x y z. split; cbn_shuf.
  - nia.
  - rewrite shuf_x_plus shuf_plus_x. rewrite 3!HR.
    by rewrite plusA. 
Qed.

(** shuffle product preserves the final chain *)
Instance shuf_chain: forall {R: Chain b}, Proper (`R ==> `R ==> `R) shuf.
Proof.
  apply (Proper_chain 2). 
  intros R HR x y xy u v uv. 
  pose proof xy as [xy0 xy'].
  pose proof uv as [uv0 uv'].
  split; cbn_shuf.
  - congruence.
  - by rewrite xy' uv' xy uv.
Qed.


(** * convolution product *)
(** this is the following binary operation on streams [s,t]:
    [(s*t)_k = Σ_{i+j=k} s_i t_j]
    (note that the binomial coefficient has disappeared)

    it can be characterised by the following equations:
    [hd (s*t) = hd s * hd t]
    [tl (s*t) = tl s * t + hd s ** tl t]
    There [**] is pointwise multiplication by a scalar, which is a special case of convolution product:
    [x ** s = c x * s]
    (Remember that [c x] is the stream [x,0,0,...] )
 *)

(** Like before, we cannot define it as one could expect in Coq, 
    because of the guard condition: *)
Fail CoFixpoint mult s t :=
  cons (hd s * hd t)%nat (mult (tl s) t + mult (c (hd s)) (tl t)).

(** Here we simply assume its existence for the sake of simplicity. *)
Parameter mult: stream -> stream -> stream.
Infix "*" := mult.
Axiom hd_mult: forall s t, hd (s * t) = (hd s * hd t)%nat.
Axiom tl_mult: forall s t, tl (s * t) = tl s * t + c (hd s) * tl t.
Ltac cbn_mult := repeat (rewrite ?hd_mult ?tl_mult; simpl hd; simpl tl).

Lemma mult_0x: forall x, c 0 * x ~ c 0.
Proof.
  coinduction R HR. intros x. split; cbn_mult.
  - nia.
  - rewrite HR. rewrite plus_0x. apply HR. 
Qed.

Lemma mult_x0: forall x, x  * c 0 ~ c 0.
Proof.
  coinduction R HR. intros x. split; cbn_mult.
  - nia.
  - rewrite HR. rewrite plus_0x. apply HR. 
Qed.

Lemma mult_1x: forall x, c 1 * x ~ x.
Proof.
  coinduction R HR. intros x. split; cbn_mult.
  - lia.
  - rewrite mult_0x plus_0x. apply HR.
Qed.

Lemma mult_x1: forall x, x * c 1 ~ x.
Proof.
  coinduction R HR. intros x. split; cbn_mult.
  - lia.
  - rewrite mult_x0 plusC plus_0x. apply HR.
Qed.

Lemma mult_x_plus: forall x y z, x * (y + z) ~ x*y + x*z.
Proof.
  coinduction R HR. intros x y z. split; cbn_mult.
  - nia. 
  - rewrite 2!HR. rewrite 2!plusA. 
    apply plus_chain. 2: reflexivity.
    rewrite <-2plusA. 
    apply plus_chain. reflexivity. by rewrite plusC.
Qed.

Lemma c_plus n m: c (n+m) ~ c n + c m.
Proof.
  coinduction R HR. clear HR. split; cbn.
  - reflexivity.
  - by rewrite plus_0x.
Qed.

Lemma c_mult n m: c (n*m) ~ c n * c m.
Proof.
  coinduction R HR. clear HR. split; cbn_mult.
  - reflexivity.
  - by rewrite mult_0x mult_x0 plus_0x.
Qed.

(** convolution product preserves the final chain  *)
Instance mult_chain: forall {R: Chain b}, Proper (`R ==> `R ==> `R) mult.
Proof.
  apply (Proper_chain 2). 
  intros R HR x y xy u v uv. 
  pose proof xy as [xy0 xy'].
  pose proof uv as [uv0 uv'].
  split; cbn_mult.
  - congruence.
  - by rewrite xy' uv' xy0 uv.
Qed.

Lemma mult_plus_x: forall x y z, (y + z) * x ~ y*x + z*x.
Proof.
  coinduction R HR. intros x y z. split; cbn_mult.
  - nia. 
  - rewrite c_plus 2!HR 2!plusA.
    apply plus_chain. 2: reflexivity.
    rewrite <-2plusA. 
    apply plus_chain. reflexivity. by rewrite plusC.
Qed.

Lemma multA: forall x y z, x * (y * z) ~ (x * y) * z.
Proof.
  coinduction R HR. intros x y z. split; cbn_mult.
  - nia.
  - rewrite mult_x_plus. rewrite 3!HR.
    rewrite plusA -mult_plus_x.
    by rewrite c_mult.
Qed.

(** below: commutativity of convolution product, following Rutten's
    proof *)
     
Lemma multC_n n: forall x, c n * x ~ x * c n.
Proof.
  coinduction R HR. intro x. split; cbn_mult.
  - nia.
  - by rewrite mult_0x mult_x0 plusC HR.
Qed.

Definition X := cons 0 (c 1).

Theorem expand x: x ~ c (hd x) + X * tl x.
Proof.
  coinduction R HR. clear HR. split; cbn_mult.
  - nia.
  - by rewrite mult_0x mult_1x plus_0x plusC plus_0x.
Qed.

Lemma multC_11 x: tl (X * x) ~ x.
Proof.
  coinduction R HR. clear HR. split; cbn_mult.
  - nia.
  - by rewrite !mult_0x mult_1x 2!plus_0x plusC plus_0x.
Qed.

Lemma multC_X: forall x, X * x ~ x * X. 
Proof.
  coinduction R HR. intro x. split; cbn_mult.      
  - nia. 
  - rewrite mult_0x mult_1x mult_x1.
    rewrite plusC plus_0x.
    rewrite plusC. by rewrite -HR -expand.
Qed.

Lemma multC: forall x y, x * y ~ y * x.
Proof.
  coinduction R HR. intros x y. split.
  - cbn_mult; nia.
  - rewrite {1}(expand x). rewrite mult_plus_x. simpl tl.
    rewrite -multA multC_11.
    rewrite (HR (tl x)).
    rewrite multC_n. rewrite <-(multC_11 (y*tl x)).
    rewrite multA multC_X.
    rewrite {3}(expand x). rewrite mult_x_plus.
    by rewrite multA. 
Qed.
