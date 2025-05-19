From epit Require Import cats.

(** * case-study in the category of types and *extenstional* functions *)

(** category of types and extensional functions *)
Program Canonical ETYPES: Category :=
  {|
    ob := Type;
    hom A B := dprod_setoid (fun _: A => eq_setoid B);
    id _ := fun x => x;
    comp _ _ _ f g := fun x => f (g x);
  |}.
Next Obligation.
  intros * f f' ff g g' gg a. by rewrite ff gg.
Qed.

(** ** endofunctors on ETYPES *)
Notation Functor := (Functor ETYPES ETYPES).

(** A×X *)
Program Definition F_times A: Functor :=
  {| app' X := A × X; app X Y f ax := (ax.1,f ax.2) |}.
Next Obligation.
  move=>/=A B C f g E [a b]/=. by rewrite E.
Qed.
Next Obligation.
  by move=>??[].
Qed.

(** option *)
Program Definition F_option: Functor :=
  {| app' := option; app := Option.map |}.
Next Obligation. intros * f g fg [a|]=>//=. f_equal; apply (fg a). Qed.
Next Obligation. by move=>?[]. Qed.
Next Obligation. by move=>*[]. Qed.

(** list *)
Program Definition F_list: Functor :=
  {| app' := list; app := List.map |}.
Next Obligation. move=>* f g /=fg l. induction l as [|a q IH]=>//=. by f_equal. Qed.
Next Obligation. intros. elim=>/=; congruence. Qed.
Next Obligation. intros. elim=>/=; congruence. Qed.

(** X^A *)
Program Definition F_exp A: Functor :=
  {| app' X := (A -> X); app X Y f g := comp f g |}.
Next Obligation.
  move=>/=* f g fg h. apply funext=>a. apply fg. (* still need [funext] *)
Qed.

(** powerset *)
Program Definition F_pow: Functor :=
  {| app' X := (X -> Prop); app X Y f S := fun y => exists x, S x /\ y = f x |}.
Next Obligation.
  move=>/=* f g fg S. apply funext=>b. apply propext. (* still need [funext] and [propext] *)
  by setoid_rewrite fg.
Qed.
Next Obligation.
  move=>/=*. apply funext=>x.
  apply propext; split=>H; eauto.
  by destruct H as [? [Sy <-]].
Qed.
Next Obligation.
  move=>/=*. apply funext=>w.
  apply propext; split; move=>[x [Hx ->]]; eauto.
  destruct Hx as [? [? ->]]; eauto.
Qed.

(** ** natural unary numbers form the initial algebra of the [option] functor *)

Inductive nat := O | S(n: nat).

Program Definition nat_alg: Algebra F_option :=
  {| alg_car := nat;
     alg_mor x := match x with Some x => S x | None => O end |}.

Lemma init_nat_alg: initial nat_alg.
Proof.
  esplit.
  - intro f. esplit.
    elim. exact (alg_mor f None).
    intros _ x. exact (alg_mor f (Some x)).
    by case.
  - cbn. intros X g.
    elim=>/=[|n IH]. apply (algE g None).
    rewrite -IH. apply (algE g (Some _)).
Qed.

(** ** `conatural unary numbers' almost form the final coalgebra of the [option] functor *)

CoInductive conat := coO | coS(n: conat).

Definition conat_coalg: Coalgebra F_option :=
  @coalg _ F_option conat (fun x => match x with coS n => Some n | coO => None end).

Lemma final_conat_coalg: final conat_coalg.
Proof.
  esplit.
  - intro f. esplit; cbn.
    cofix CH. intro x. destruct (coalg_mor f x) as [c|].
    apply coS, CH, c.
    apply coO.
    intro x; cbn. by destruct (coalg_mor f x).
  - intros X f g.
    cbn.
    intro x.                    (* does not help *)
Abort.

