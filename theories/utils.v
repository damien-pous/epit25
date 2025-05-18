From Coq Require Export Basics List Fin.
From Coq Require Export Setoid Morphisms.
From Coq Require Export ssreflect ssrfun ssrbool.

#[global] Set Implicit Arguments.
#[global] Unset Transparent Obligations.
#[global] Obligation Tactic := ((by cbn) || idtac).
#[global] Set Primitive Projections.
#[global] Set Universe Polymorphism.
#[global] Set Warnings "-deprecated-instance-without-locality".

Definition const {X Y} y: X -> Y := fun _ => y.
Arguments const {_ _} _ _/.
Infix "×" := prod (at level 40).

(* From epit Require Import setoids. *)

Axiom funext: forall A B (f g: A -> B), (forall a, f a = g a) -> f = g.
Axiom propext: forall A B: Prop, (A <-> B) -> A = B.

Lemma funext': forall A B (f g: A -> B), f=g -> forall a, f a = g a.
Proof. by move=>????->. Qed.
