From epit Require Import cats.

(** * case-study in the category of types and functions *)

Canonical TYPES.

(** ** endofunctors on TYPES *)
Notation FUNCTOR := (FUNCTOR TYPES TYPES).


(** A×X *)
Program Definition F_times A: FUNCTOR :=
  {| app' X := A × X; app X Y f ax := (ax.1,f ax.2) |}.
Next Obligation.
  intros. by apply funext=>[[]].
Qed.

(** option *)
Program Canonical F_option: FUNCTOR :=
  {| app' := option; app := Option.map |}.
Next Obligation. intros. by apply funext=>[[|]]. Qed.
Next Obligation. intros. by apply funext=>[[|]]. Qed.

(** list *)
Program Definition F_list: FUNCTOR :=
  {| app' := list; app := List.map |}.
Next Obligation. intros. apply funext; elim=>/=; congruence. Qed.
Next Obligation. intros. apply funext; elim=>/=; congruence. Qed.

(** X^A *)
Program Definition F_exp A: FUNCTOR :=
  {| app' X := A -> X; app X Y f g := comp f g |}.

(** powerset *)
Program Definition F_pow: FUNCTOR :=
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

(** ** natural unary numbers form the initial algebra of the [option] functor *)

Inductive nat := O | S(n: nat).

Definition nat_pack (n: option nat): nat :=
  match n with Some n => S n | None => O end.

Fixpoint nat_iter {X} (f: option X -> X) (n: nat) :=
  match n with
  | O => f None
  | S n => f (Some (nat_iter f n))
  end.

Program Definition nat_alg: ALGEBRA F_option :=
  {| alg_car := nat;
     alg_bod := nat_pack |}.

Lemma init_nat_alg: initial nat_alg.
Proof.
  unshelve eexists. 
  - intro f. exists (nat_iter (alg_bod f)). 
    by apply funext; case. 
  - intros X g. apply funext. simpl. intro n. 
    induction n as [|n IH]; simpl.
    -- apply (funext' (algE g) None).
    -- rewrite -IH. apply (funext' (algE g) (Some _)). 
Qed.

(** ** `conatural unary numbers' almost form the final coalgebra of the [option] functor *)

CoInductive conat := coO | coS(n: conat).

Definition conat_pack (n: conat): option conat :=
  match n with coS n => Some n | coO => None end.

Definition conat_coalg: COALGEBRA F_option :=
  {| coalg_car := conat: ob TYPES;
     coalg_bod := conat_pack |}.

CoFixpoint conat_coiter {X} (f: X -> option X) (x: X): conat :=
  match f x with
  | None => coO
  | Some y => coS (conat_coiter f y)
  end.
  
Lemma final_conat_coalg: final conat_coalg.
Proof.
  unshelve eexists.
  - intro f. exists (conat_coiter (coalg_bod f)).
    apply funext=>x/=. by destruct (coalg_bod f x).
  - simpl. intros X f g.
Abort.


(** ** the empty set is the initial algebra of the [AxX] functor *)

Variant empty := .

Program Definition empty_alg A: ALGEBRA (F_times A) :=
  {| alg_car := empty;
     alg_bod x := match x.2 with end |}.

Lemma init_empty_alg A: initial (empty_alg A).
Proof.
  unshelve esplit.
  - intro f. unshelve eexists. by case.
    apply funext. by move=>[?[]].
  - simpl. intros X g. apply funext. by case.
Qed.


(** ** streams are almost a final coalgebra of the [AxX] functor *)

CoInductive stream A := cons { head: A; tail: stream A }.

Program Definition stream_coalg A: COALGEBRA (F_times A) :=
  {| coalg_car := stream A;
     coalg_bod s := (head s, tail s) |}.

Lemma final_stream_coalg A: final (stream_coalg A).
Proof.
  unshelve esplit.
  - intro f. unshelve eexists; cbn.
    cofix CH. intro x. destruct (coalg_bod f x) as [a y]. exact (cons a (CH y)).
    apply funext=>x; simpl. by destruct (coalg_bod f x).
  - intros X f g.
Abort.

(** ** Polynomial Functors

  We have constructed and proven by hand two initial algebras. We can avoid some tedious work by capturing a large class at once: polynomial functors, corresponding intuitively to functors having the shape of a formal series [λX.Σ X^n].
  Conveniently, these functors admit a simple representation as *containers*. In the following section,
we construct their initial algebras.
 *)

Import SigTNotations.
Section containers.

  (** Containers: a *shape* [A] together with a type family of *positions* [B] *)
  Record container := {
      A: Type;
      B: A -> Type
    }.

  (* Containers represent functors: intuitively, each element of [A] is a different shape,
     and given a shape [a], then the position [B a] indicates how it should be filled with data.
   *)
  Program Definition apply (cont : container) : FUNCTOR :=
    {| app' X := { a : A cont & B cont a -> X};
       app X Y f := fun x => existT _ x.1 (f ∘ x.2)
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

  Program Definition w_alg : ALGEBRA (apply cont) :=
    {| alg_car := W_sort;
       alg_bod x := (sup0 x.1 x.2) |}.

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

