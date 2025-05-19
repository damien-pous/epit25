From epit Require Import cats.

(** * Case-study in the category of types and functions

  In this file, we ground ourselves in category TYPES.
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
  {| app' X := A × X; app X Y f ax := (ax.1,f ax.2) |}.
Next Obligation.
  intros. by apply funext=>[[]].
Qed.

(** ** The option functor *)
Program Canonical F_option: Functor :=
  {| app' := option; app := Option.map |}.
Next Obligation. (* SOLUTION *) intros. by apply funext=>[[|]]. Qed.
Next Obligation. (* SOLUTION *) intros. by apply funext=>[[|]]. Qed.

(** ** The list functor *)
Program Definition F_list: Functor :=
  {| app' := list; app := List.map |}.
Next Obligation. (* SOLUTION *) intros. apply funext=>l. induction l; cbn; by f_equal. Qed.
Next Obligation. (* SOLUTION *) intros. apply funext=>l. induction l; cbn; by f_equal. Qed.

(** ** The [X^A] functor *)
Program Definition F_exp A: Functor :=
  {| app' X := A -> X; app X Y f g := comp f g |}.

(** ** The powerset functor *)
Program Definition F_pow: Functor :=
  {| app' X := (X -> Prop); app X Y f S := fun y => exists x, S x /\ y = f x |}.
Next Obligation.
  (* SOLUTION *)
  cbn; intros. apply funext=>S;  apply funext=>y.
  apply propext; split=>H; eauto.
  by destruct H as [? [Sy <-]].
Qed.
Next Obligation.
  (* SOLUTION *)
  cbn; intros. apply funext=>S;  apply funext=>y.
  apply propext; split; intros [x [Hx ->]]; eauto.
  destruct Hx as [? [? ->]]; eauto.
Qed.


(** * 2. Examples of Initial algebras on TYPES *)

(** ** natural unary numbers form the initial algebra of the [option] functor *)

Section initial_option.

(** This is the exact definition you can find in the standard library *)
Inductive nat := O | S (n: nat).

Definition nat_pack (n: option nat): nat :=
  match n with Some n => S n | None => O end.

(** The pair (O, S) defines an option-algebra  *)
Program Definition nat_alg: Algebra F_option :=
  {| alg_car := nat;
     alg_mor := nat_pack |}.

(** Remains to prove its initiality. *)
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

(** Having established [init_nat_alg], we can see this result less as a fact about [nat] itself than about [option], proving it admits an initial algebra.
  With this knowledge, we can work over an abstract view of [nat].
*)
Module abstract_nat.
  Parameter A: Algebra F_option.
  Parameter I: initial A.
  (** We define [nat] as the carrier of the initial algebra *)
  Definition nat := alg_car A.

  (** We get a constructor and a destructor by Lambek *)
  Definition i: F_option nat ≃ nat := Lambek I.
  Definition c: option nat -> nat  := fwd i.
  Definition d: nat -> option nat  := bwd i.

  (** We derive 0 and successor from the constructor [c] *)
  Definition O: nat := c None.
  Definition S (n: nat): nat := c (Some n).

  (** And a recursion principle *)
  Definition pack_alg {X} (x : X) (s: X -> X): Algebra F_option :=
    @alg TYPES _ X (fun ox => match ox with | None => x | Some y => s y end).

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

  (* BEGIN SOLUTION *)
  Variant empty := .

  Program Definition empty_alg A: Algebra (F_times A) :=
    {| alg_car := empty;
      alg_mor x := match x.2 with end |}.

  Lemma init_empty_alg A: initial (empty_alg A).
  Proof.
    esplit.
    - intros [X f]. esplit. by case.
      apply funext. by intros [?[]].
    - intros [X h] [g Hg]. apply funext; cbn. by case.
  Qed.
  (* END  SOLUTION *)

End initial_times.

Section initial_otimes.

(** ** Exercise
     Define the initial algebra for the functor [λ X. 1 + A * X].
 *)

  (** The [1 + A×X] functor *)
  Definition F_otimes (A : Type): Functor := functor_comp F_option (F_times A).

  (* BEGIN SOLUTION *)
  (** The pair (nil, cons) defines a list-algebra  *)
  Program Definition list_alg A: Algebra (F_otimes A) :=
    {| alg_car := list A;
      alg_mor := fun x => match x with | None => nil | Some (a,x) => a :: x end |}.

  (** Remains to prove its initiality. *)
  Fixpoint list_iter {A X} (f: option (A × X) -> X) (l: list A) :=
    match l with
    | nil    => f None
    | a :: l => f (Some (a, (list_iter f l)))
    end.

   Lemma init_list_alg A: initial (list_alg A).
   Proof.
     esplit. 
     - intros [X f]. exists (list_iter f). 
       apply funext. by case; [case |].
     - intros [X h] [g Hg]. apply funext=>/=l.
       induction l as [|a l IH]; cbn.
       -- apply (funext' Hg None).
       -- rewrite -IH. apply (funext' Hg (Some (a, _))). 
   Qed.
  (* END SOLUTION *)

End initial_otimes.


(** * 3. Polynomial Functors

  We have constructed and proven by hand a couple of initial algebras. We can avoid some tedious work by capturing a large class at once: polynomial functors, corresponding intuitively to functors having the shape of a formal series [λX.Σ X^n].
  Conveniently, these functors admit a simple representation as *containers*. In the following section,
we construct their initial algebras.
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
  (** λX . X * X : only one shape, and two piece of data to store *)
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

Definition conat_coalg: Coalgebra F_option :=
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
