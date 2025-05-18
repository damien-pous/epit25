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

(** A×X *)
Program Definition F_times A: Functor :=
  {| app' X := A × X; app X Y f ax := (ax.1,f ax.2) |}.
Next Obligation.
  intros. by apply funext=>[[]].
Qed.

(** option *)
Program Canonical F_option: Functor :=
  {| app' := option; app := Option.map |}.
Next Obligation. intros. by apply funext=>[[|]]. Qed.
Next Obligation. intros. by apply funext=>[[|]]. Qed.

(** list *)
Program Definition F_list: Functor :=
  {| app' := list; app := List.map |}.
Next Obligation. intros. apply funext; elim=>/=; congruence. Qed.
Next Obligation. intros. apply funext; elim=>/=; congruence. Qed.

(** X^A *)
Program Definition F_exp A: Functor :=
  {| app' X := A -> X; app X Y f g := comp f g |}.

(** powerset *)
Program Definition F_pow: Functor :=
  {| app' X := (X -> Prop); app X Y f S := fun y => exists x, S x /\ y = f x |}.
Next Obligation.
  cbn; intros. apply funext=>S;  apply funext=>y.
  apply propext; split=>H; eauto.
  by destruct H as [? [Sy <-]].
Qed.
Next Obligation.
  cbn; intros. apply funext=>S;  apply funext=>y.
  apply propext; split; move=>[x [Hx ->]]; eauto.
  destruct Hx as [? [? ->]]; eauto.
Qed.


(** * 2. Examples of Initial algebras on TYPES *)

(** ** natural unary numbers form the initial algebra of the [option] functor *)

Section initial_option.
(* This is the exact definition you can find in the standard library *)
Inductive nat := O | S (n: nat).

Definition nat_pack (n: option nat): nat :=
  match n with Some n => S n | None => O end.

(* The pair (O, S) defines an option-algebra  *)
Program Definition nat_alg: Algebra F_option :=
  {| alg_car := nat;
     alg_mor := nat_pack |}.

(* Remains to prove its initiality. *)
Fixpoint nat_iter {X} (f: option X -> X) (n: nat) :=
  match n with
  | O => f None
  | S n => f (Some (nat_iter f n))
  end.

Lemma init_nat_alg: initial nat_alg.
Proof.
  unshelve eexists. 
  - intro f. exists (nat_iter (alg_mor f)). 
    by apply funext; case. 
  - intros X g. apply funext. simpl. intro n. 
    induction n as [|n IH]; simpl.
    -- apply (funext' (algE g) None).
    -- rewrite -IH. apply (funext' (algE g) (Some _)). 
Qed.

End initial_option.

(* Having established [init_nat_alg], we can see this result less as a fact about [nat] itself than about [option], proving it admits an initial algebra.
  With this knowledge, we can work over an abstract view of [nat].
*)
Module abstract_nat.
  Parameter A: Algebra F_option.
  Parameter I: initial A.
  (* We define [nat] as the carrier of the initial algebra *)
  Definition nat := alg_car A.

  (* We get a constructor and a destructor by Lambek *)
  Definition i: F_option nat ≃ nat := Lambek I.
  Definition c: option nat -> nat  := fwd i.
  Definition d: nat -> option nat  := bwd i.

  (* 0 and successors *)
  Definition O: nat := c None.
  Definition S: nat -> nat := @comp TYPES _ _ _ c Some.

  (* And a recursion principle *)
  Definition pack    {X : Type} (x : X) (s: X -> X) : Algebra F_option := @alg _ F_option X (fun ox => match ox with | None => x | Some y => s y end).
  Definition nat_rec {X : Type} (x : X) (s: X -> X) := rec I (pack x s).
  
  Lemma nat_recO {X : Type} (x : X) (s: X -> X) : nat_rec x s O = x.
  Proof.
    apply (funext' (recE I (pack x s)) None).
  Qed.
      
  Lemma nat_recS {X : Type} (x : X) (s: X -> X): forall n, nat_rec x s (S n) = s (nat_rec x s n).
  Proof.
    intros n.
    apply (funext' (recE I (pack x s)) (Some n)).
  Qed.

  Definition add (n m : nat) : nat := nat_rec m S n.
  Lemma addO n: add O n = n.
  Proof. apply nat_recO. Qed.

  Lemma addS n m: add (S n) m = S (add n m).
  Proof. apply nat_recS. Qed.

End abstract_nat.

Section initial_times.

(** ** the empty set is the initial algebra of the [AxX] functor *)

Variant empty := .

Program Definition empty_alg A: Algebra (F_times A) :=
  {| alg_car := empty;
     alg_mor x := match x.2 with end |}.

Lemma init_empty_alg A: initial (empty_alg A).
Proof.
  unshelve esplit.
  - intro f. unshelve eexists. by case.
    apply funext. by move=>[?[]].
  - simpl. intros X g. apply funext. by case.
Qed.

End initial_times.

(* Exercise? *)
Section initial_otimes.
  (** option (A×X) *)
Definition F_otimes (A : Type): Functor.
unshelve econstructor.
exact (fun X => option (A × X)).
exact (fun X Y f => Option.map (fun ax => (ax.1,f ax.2))).
cbv; intros; apply funext; intros [[] |]; by subst.
cbv; intros; apply funext; intros [[] |]; by subst.
cbv; intros; apply funext; intros [[] |]; by subst.
Defined.

(* Why do I get a weird error with [Program] ? *)
(* because strangely, Program Definition does not propagate the type annotation early enough  *)
(* 
Program Definition F_otimes' A : Functor :=
  {| app' X := option (A × X); 
     app X Y f := Option.map (fun ax => (ax.1,f ax.2)) |}.
Next Obligation.
  intros. apply funext; by intros [[] |].
Qed.
Next Obligation.
  intros.
   apply funext. intros [[] |]; reflexivity.
Fail Qed. *)

(* The pair (nil, cons) defines a list-algebra  *)
Program Definition list_alg A: Algebra (F_otimes A) :=
  {| alg_car := list A;
     alg_mor := fun x => match x with | None => nil | Some (a,x) => a :: x end |}.

(* Remains to prove its initiality. *)
Fixpoint list_iter {A X} (f: option (A × X) -> X) (l: list A) :=
  match l with
  | nil    => f None
  | a :: l => f (Some (a, (list_iter f l)))
  end.

Lemma init_list_alg A: initial (list_alg A).
Proof.
  unshelve eexists. 
  - intro f. exists (list_iter (alg_mor f)). 
    apply funext. by case; [case |].
  - intros X g. apply funext. simpl. intros l.
    induction l as [|a l IH]; simpl.
    -- apply (funext' (algE g) None).
    -- rewrite -IH. apply (funext' (algE g) (Some (a, _))). 
Qed.

End initial_otimes.


(** ** 3. Polynomial Functors

  We have constructed and proven by hand two initial algebras. We can avoid some tedious work by capturing a large class at once: polynomial functors, corresponding intuitively to functors having the shape of a formal series [λX.Σ X^n].
  Conveniently, these functors admit a simple representation as *containers*. In the following section,
we construct their initial algebras.
 *)

Section containers.

  (** Containers: a *shape* [A] together with a type family of *positions* [B] *)
  Record container := {
      A: Type;
      B: A -> Type
    }.

  (* Containers represent functors: intuitively, each element of [A] is a different shape,
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

  (* A few examples *)
  (* λX . X * X : only one shape, and two piece of data to store *)
  Example container_pair   : container := {| A := unit ; B := fun _ => bool |}.
  (* option : two shapes, with respectively 0 and 1 piece of data to store *)
  Example container_option : container := {| A := bool ; B := fun b => if b then unit else False |}.
  (* list : a shape per possible length, and the corresponding number of data to store *)
  Example container_list   : container := {| A := Datatypes.nat ; B := fun n => Fin.t n |}.

  (** W-types: an explicit construction of the initial algebra of polynomial functors.
      The construction is quite simple: finite trees whose nodes are labelled by a shape,
      and children determined by the corresponding position.
   *)
  Context {cont : container}.
  Notation cA := cont.(A).
  Notation cB := cont.(B).

  Inductive W_sort : Type :=
  | sup0 (a : cA) (f : cB a -> W_sort) : W_sort.

  Program Definition w_alg : Algebra (apply cont) :=
    {| alg_car := W_sort;
       alg_mor x := (sup0 (projT1 x) (projT2 x)) |}.

  (* And indeed, [w_alg] is initial *)
  Lemma init_w_alg : initial w_alg.
  Proof.
    unshelve esplit.
    - intros [X f].
      unshelve eexists.
      elim. intros a _ c.
      cbn in *.
      apply f.
      exists a. exact c.
      apply funext.
      intros [].
      cbn; f_equal.
    - simpl.
      intros X f.
      apply funext.
      elim.
      intros a s ih.
      setoid_rewrite (f_equal (fun f => f (existT (fun a : cA => cB a -> W_sort) a s)) (algE f)).
      simpl.
      f_equal.
      f_equal.
      apply funext.
      apply ih.
  Qed.

End containers.



(** * 4. Example of final coalgebras in TYPES *)

(** ** `conatural unary numbers' almost form the final coalgebra of the [option] functor *)

CoInductive conat := coO | coS(n: conat).

Definition conat_pack (n: conat): option conat :=
  match n with coS n => Some n | coO => None end.

Definition conat_coalg: Coalgebra F_option :=
  {| coalg_car := conat: ob TYPES;
     coalg_mor := conat_pack |}.

CoFixpoint conat_coiter {X} (f: X -> option X) (x: X): conat :=
  match f x with
  | None => coO
  | Some y => coS (conat_coiter f y)
  end.
  
Lemma final_conat_coalg: final conat_coalg.
Proof.
  unshelve eexists.
  - intro f. exists (conat_coiter (coalg_mor f)).
    apply funext=>x. simpl.
    (* anomaly with Coq 8.17.1 ... *)
    (* by destruct (coalg_mor f x). *) 
    admit.
  - simpl. intros X f g.
Abort.



(** ** streams are almost a final coalgebra of the [AxX] functor *)

CoInductive stream A := cons { head: A; tail: stream A }.

Program Definition stream_coalg A: Coalgebra (F_times A) :=
  {| coalg_car := stream A;
     coalg_mor s := (head s, tail s) |}.

Lemma final_stream_coalg A: final (stream_coalg A).
Proof.
  unshelve esplit.
  - intro f. unshelve eexists; cbn.
    cofix CH. intro x. destruct (coalg_mor f x) as [a y]. exact (cons a (CH y)).
    apply funext=>x. cbn. by destruct (coalg_mor f x). 
  - intros X f g.
Abort.
