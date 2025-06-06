From epit Require Import cats.

(** * Case-study in the category of types and functions

  In this file, we ground ourselves in category TYPES of types and functions between them.
  (in set theory, this cateogory is usually called SETS)

  In this setting, we study some concrete inital algebras and final coalgebras.

  We allow ourselves the use of the functional and propositional extensionality axioms:
  [funext : (forall x, f x = g x) -> f = g]
  [propext : (forall P Q: Prop, P <-> Q) -> P = Q]
*)

Canonical TYPES.

(** ** Endofunctors on TYPES *)
Notation Functor := (Functor TYPES TYPES).



(** * 1. Examples of functors *)

(** ** The [A×X] functor *)
Program Definition F_times A: Functor :=
  {| app' X := A × X;
     app X Y f ax := (ax.1,f ax.2) |}.
Next Obligation.
  intros. by apply funext=>[[]].
Qed.

(** ** The option functor (also known as [1+X]) *)
Program Canonical F_option: Functor :=
  {| app' := option; app := Option.map |}.
Next Obligation. Admitted.
Next Obligation. Admitted.

(** ** The list functor (sometimes written [X*])*)
Program Definition F_list: Functor :=
  {| app' := list; 
     app := List.map |}.
Next Obligation. Admitted.
Next Obligation. Admitted.

(** ** The [X^A] functor *)
Program Definition F_exp A: Functor :=
  {| app' X := A -> X;
     app X Y f g := comp f g |}.

(** ** The powerset functor *)
Program Definition F_pow: Functor :=
  {| app' X := (X -> Prop);
     app X Y f S := fun y => exists x, S x /\ y = f x |}.
Next Obligation.
Admitted.
Next Obligation.
Admitted.


(** * 2. Examples of Initial algebras on TYPES *)

(** ** natural unary numbers form the initial algebra of the [option X = 1+X] functor *)

Section initial_option.

(** The definition of natural numbers from the standard library *)
Inductive nat := O | S (n: nat).

(** Consider the following function *)
Definition nat_pack (n: option nat): nat :=
  match n with Some n => S n | None => O end.

(** It is sometimes writen [[O,S]] (copairing of O and S),
    it provides [nat] with an algebra structure: *)
Program Definition nat_alg: Algebra F_option :=
  {| alg_car := nat;
     alg_mor := nat_pack |}.

(** It remains to prove initiality, for which we rely on the following iterator *)
Fixpoint nat_iter {X} (f: option X -> X) (n: nat) :=
  match n with
  | O   => f None
  | S n => f (Some (nat_iter f n))
  end.

Lemma init_nat_alg: initial nat_alg.
Proof.
  esplit. 
  - intros [X f]. exists (nat_iter f). 
    by apply funext; case. 
  - intros [X h] [g Hg]. apply funext=>/=n. 
    induction n as [|n IH]; cbn.
    -- apply (funext' Hg None).
    -- rewrite -IH. apply (funext' Hg (Some _)).
Qed.

End initial_option.

(** since [nat] (with [[O,S]]) is an initial algebra, every other initial algebra is isomorphic to it.
    in particular, this enables an abstract view of [nat]. *)
Module abstract_nat.
  Parameter A: Algebra F_option.
  Parameter I: initial A.
  
  (** We define [nat] as the carrier of the initial algebra *)
  Definition nat := alg_car A.

  (** We get a constructor and a destructor by Lambek's lemma *)
  Definition i: F_option nat ≃ nat := Lambek I.
  Definition c: option nat -> nat  := fwd i.
  Definition d: nat -> option nat  := bwd i.

  (** We derive 0 and successor from the constructor [c] *)
  Definition O: nat := c None.
  Definition S (n: nat): nat := c (Some n).

  (** And a recursion principle *)
  Definition pack_alg {X} (x : X) (s: X -> X): Algebra F_option :=
    @alg TYPES F_option X (fun ox => match ox with | None => x | Some y => s y end).

  Definition abstract_nat_iter {X} (x : X) (s: X -> X): nat -> X :=
    alg_bod (init_mor I (pack_alg x s)).

  Lemma abstract_nat_iterO X (x: X) (s: X -> X):
    abstract_nat_iter x s O = x.
  Proof.
    apply (funext' (algE (I (pack_alg x s))) None).
  Qed.

  Lemma abstract_nat_iterS {X} (x: X) (s: X -> X):
    forall n, abstract_nat_iter x s (S n) = s (abstract_nat_iter x s n).
  Proof.
    intros n.
    apply (funext' (algE (I (pack_alg x s))) (Some n)).
  Qed.

  (** [nat] is still abstract, but we can define addition on it *)
  Definition add (n m: nat): nat := abstract_nat_iter m S n.
  Lemma addO n: add O n = n.
  Proof. apply abstract_nat_iterO. Qed.

  Lemma addS n m: add (S n) m = S (add n m).
  Proof. apply abstract_nat_iterS. Qed.

End abstract_nat.

Section initial_times.

(** ** Exercise
     Define the initial algebra of the [F_times A == λX. AxX] functor
 *)


End initial_times.

Section initial_otimes.

(** ** Exercise
     Define the initial algebra for the functor [λ X. 1 + A × X].
 *)

  (** The [1 + A×X] functor *)
  Definition F_otimes (A : Type): Functor := functor_comp F_option (F_times A).

End initial_otimes.


(** * 3. Polynomial Functors

  We have constructed and proven by hand a couple of initial algebras. We can avoid some tedious work by capturing a large class at once: polynomial functors, corresponding intuitively to functors having the shape of a formal series [λX.Σ_n A_n×X^n].
  Conveniently, these functors admit a simple representation as *containers*.
  In the following section, we construct their initial algebras.
 *)

Section containers.

  (** Containers: a *shape* [A] together with a type family of *positions* [B] *)
  Record container := {
      A: Type;
      B: A -> Type
    }.

  (** Containers represent functors: intuitively, each element of [A] is a different shape,
     and given a shape [a], then the position [B a] indicates how it should be filled with data.
   *)
  Program Definition apply (cont : container) : Functor :=
    {| app' X := { a : A cont & B cont a -> X};
       app X Y f := fun x => existT _ (projT1 x) (f ∘ (projT2 x))
    |}.
  Next Obligation.
    intros ? A.
    apply funext.
    intros [u v].
    cbn; f_equal.
  Qed.

  (** ** A few examples *)
  (** λX . X * X : only one shape, and two pieces of data to store *)
  Example container_pair   : container := {| A := unit ; B := fun _ => bool |}.
  (** option : two shapes, with respectively 0 and 1 piece of data to store *)
  Example container_option : container := {| A := bool ; B := fun b => if b then unit else False |}.
  (** list : a shape per possible length, and the corresponding number of data to store *)
  Example container_list   : container := {| A := Datatypes.nat ; B := fun n => Fin.t n |}.

  (** ** W-types: an explicit construction of the initial algebra of polynomial functors.
      The construction is quite simple: finite trees whose nodes are labelled by a shape,
      and children determined by the corresponding position.
   *)
  Context {cont : container}.
  Notation cA := cont.(A).
  Notation cB := cont.(B).

  Inductive W := node (a : cA) (g : cB a -> W).

  Program Definition W_alg : Algebra (apply cont) :=
    {| alg_car := W;
       alg_mor x := (node (projT1 x) (projT2 x)) |}.

  Fixpoint W_iter {X} (f: apply cont X -> X) (w: W) :=
    match w with
    | node a c => f (existT _ a (fun i => W_iter f (c i)))
    end.
  
  (** And indeed, [W_alg] is initial *)
  Lemma init_W_alg : initial W_alg.
  Proof.
    esplit.
    - intros [X f]. exists (W_iter f). 
      by apply funext=>[]. 
    - cbn.
      intros X [f Hf].
      apply funext=>w.
      induction w as [a c IH]; cbn.
      setoid_rewrite (funext' Hf (existT _ a c)). 
      cbn.
      f_equal. f_equal.
      apply funext. apply IH.
  Qed.

End containers.



(** * 4. Example of final coalgebras in TYPES *)

(** ** `conatural unary numbers' almost form the final coalgebra of the [option] functor *)

CoInductive conat := coO | coS(n: conat).

Definition conat_unpack (n: conat): option conat :=
  match n with coS n => Some n | coO => None end.

Program Definition conat_coalg: Coalgebra F_option :=
  {| coalg_car := conat: ob TYPES;
     coalg_mor := conat_unpack |}.

CoFixpoint conat_coiter {X} (f: X -> option X) (x: X): conat :=
  match f x with
  | None => coO
  | Some y => coS (conat_coiter f y)
  end.

Lemma final_conat_coalg: final conat_coalg.
Proof.
  esplit.
  - intros [X f]. exists (conat_coiter f).
    apply funext=>x/=. by destruct (f x). 
  - intros [X h] [f Hf] [g Hg]. apply funext=>x. cbn in *. 
    (** not provable in Rocq *)
Abort.



(** ** streams are almost a final coalgebra of the [AxX] functor *)

CoInductive stream A := cons { head: A; tail: stream A }.

Program Definition stream_coalg A: Coalgebra (F_times A) :=
  {| coalg_car := stream A;
     coalg_mor s := (head s, tail s) |}.

CoFixpoint stream_coiter {A X} (f: X -> A×X) x :=
  cons (f x).1 (stream_coiter f (f x).2).

Lemma final_stream_coalg A: final (stream_coalg A).
Proof.
  esplit.
  - intros [X f]. exists (stream_coiter f).
    apply funext=>x. cbn. by destruct (f x).
  - intros [X h] [f Hf] [g Hg]; cbn in *. apply funext. intros ?.
    (** not provable in Rocq *)
Abort.
