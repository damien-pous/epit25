From epit Require Import utils.

(** * setoids *)
Module Setoid.

Structure type := build {
    sort:> Type;
    #[canonical=no] eqv: relation sort;
    #[canonical=no] Equivalence_eqv: Equivalence eqv;
}.
Arguments build: clear implicits.

Structure morphism (X Y: type) := build_morphism {
    body:> X -> Y;
    #[canonical=no] body_eqv: Proper (eqv X ==> eqv Y) body;
}.
Arguments build_morphism {_ _}.

Canonical Structure id {X: type}: morphism X X :=
  build_morphism Datatypes.id _.
Program Canonical Structure comp {X Y Z: type} (f: morphism Y Z) (g: morphism X Y): morphism X Z :=
  build_morphism (comp f g) _.
Next Obligation. move=>X Y Z f g x y xy. apply f, g, xy. Qed.
Program Canonical Structure const {X Y: type} (y: Y): morphism X Y :=
  build_morphism (const y) _.
Next Obligation. move=>X Y y _ _ _/=. apply Equivalence_eqv. Qed.

End Setoid.
Notation Setoid := Setoid.type.
Notation body := Setoid.body.
Notation eqv := (Setoid.eqv _).
#[reversible] Coercion Setoid.sort: Setoid >-> Sortclass.
#[reversible] Coercion Setoid.body: Setoid.morphism >-> Funclass.
Existing Instance Setoid.Equivalence_eqv.
Existing Instance Setoid.body_eqv.
Notation "X '-eqv->' Y" := (Setoid.morphism X%type Y%type) (at level 99, Y at level 200).
Notation "'efun' x .. y => p" := ({| body x := .. {| body y := p |} ..|})
  (at level 200, x binder, right associativity).
Canonical Setoid.id.
Canonical Setoid.comp.
Canonical Setoid.const.
Infix "≡" := eqv (at level 70).
Infix "≡[ X ]" := (@Setoid.eqv X) (at level 70, only parsing).
Lemma eqv_refl {X: Setoid} (x: X): x ≡ x.
Proof. reflexivity. Qed.
Lemma eqv_sym {X: Setoid} (x y: X): x ≡ y -> y ≡ x.
Proof. apply symmetry. Defined.
#[export] Hint Extern 0 (_ ≡ _)=> exact: (eqv_refl _) || apply: eqv_sym; assumption: core.
Lemma eqv_trans {X: Setoid} {x y z: X}: x ≡ y -> y ≡ z -> x ≡ z.
Proof. apply transitivity. Defined.

Definition eq_setoid X := Setoid.build X eq eq_equivalence.
Canonical unit_setoid := eq_setoid unit.
Canonical bool_setoid := eq_setoid bool.

Canonical Prop_setoid := Setoid.build Prop iff _.

Program Canonical prod_setoid (X Y: Setoid) :=
  Setoid.build (X*Y) (fun p q => fst p ≡ fst q /\ snd p ≡ snd q) _.
Next Obligation.
  constructor=>//.
  by move=>??[??]; split; symmetry; assumption.
  by move=>???[??][]; split; etransitivity; eassumption.
Qed.

Definition sum_eqv {X Y: Setoid} (p q: X+Y) :=
  match p,q with inl p,inl q | inr p,inr q => p ≡ q | _,_ => False end.
Program Canonical sum_setoid (X Y: Setoid) := Setoid.build (X+Y) sum_eqv _.
Next Obligation.
  constructor.
  by move=>[?|?]//=.
  by move=>[?|?][?|?]?//=.
  by move=>[?|?][y|y][?|?]??//=; transitivity y.
Qed.

Definition option_eqv {X: Setoid} (p q: option X) :=
  match p,q with Some p,Some q => p≡q | None,None => True | _,_ => False end.
Program Canonical option_setoid (X: Setoid) :=
  Setoid.build (option X) option_eqv _.
Next Obligation.
  constructor.
  by move=>[?|]//=.
  by move=>[?|][?|]//=.
  by move=>[?|][y|][?|]??//=; transitivity y.
Qed.

(** helpers for option setoids *)
Program Definition None' {X: Setoid}: unit -eqv-> option X :=
  efun _ => None.
Program Definition Some' {X: Setoid}: X -eqv-> option X :=
  efun x => Some x.
Next Obligation. intros X ?? E. apply E. Qed.
Program Definition option_pack {X Y: Setoid} (y: Y) (f: X -eqv-> Y): option X -eqv-> Y :=
  efun x => match x with None => y | Some x => f x end.
Next Obligation. intros X Y y f [|] [|] E; cbn in E; try tauto. by apply f. reflexivity. Qed.
Program Definition option_map' {X Y} (f: X -eqv-> Y): option X -eqv-> option Y :=
  efun x => option_map f x.
Next Obligation. intros X Y f [] [] E; cbn; try tauto. by apply f. Qed.

Fixpoint list_eqv {X: Setoid} (h k: list X) :=
  match h,k with cons x h,cons y k => x≡y /\ list_eqv h k | nil,nil => True | _,_ => False end.
Program Canonical list_setoid (X: Setoid) :=
  Setoid.build (list X) list_eqv _.
Next Obligation.
  constructor.
  - by elim=>//.
  - by elim=>[|x h IH][|y k]//=[? ?]; split; auto.
  - elim=>[|x h IH][|y k][|z l]//=[? ?][? ?]; split; try etransitivity; eauto.
Qed.

Program Canonical dprod_setoid A (X: A -> Setoid) :=
  Setoid.build (forall a, X a) (fun f g => forall a, f a ≡ g a) _.
Next Obligation.
  constructor.
  - by move=>??.
  - by move=>????; symmetry.
  - by move=>??????; etransitivity; eauto.
Qed.

Program Definition kern_setoid A (X: Setoid) (f: A -> X) :=
  Setoid.build A (fun a b => f a ≡ f b) _.
Next Obligation.
  constructor.
  - by move=>?.
  - by move=>???.
  - by move=>?????; etransitivity; eauto.
Defined.
Lemma kern_eqv A (X: Setoid) (f: A -> X): Proper (Setoid.eqv (kern_setoid X f) ==> eqv) f.
Proof. now intros. Qed.
Definition kern' A (X: Setoid) (f: A -> X): kern_setoid X f -eqv-> X :=
  @Setoid.build_morphism (kern_setoid X f) X f (kern_eqv X f).


Canonical sig_setoid (X: Setoid) (P: X -> Prop) :=
  kern_setoid X (@proj1_sig X P).
Definition proj1_sig' {X: Setoid} (P: X -> Prop): sig P -eqv-> X := kern' _ _.

Canonical setoid_morphisms_setoid (X Y: Setoid) :=
  kern_setoid _ (@Setoid.body X Y).

Instance comp_eqv_ {X Y Z}: Proper (eqv ==> eqv ==> eqv) (@Setoid.comp X Y Z).
Proof. move=>/=f f' ff' g g' gg' x=>/=. setoid_rewrite ff'. by setoid_rewrite gg'. Qed.

Instance const_eqv {X} {Y: Setoid}: Proper (eqv ==> eqv) (@const X Y).
Proof. move=>/=y y' yy' _/=. apply yy'. Qed.
Instance setoid_const_eqv {X} {Y: Setoid}: Proper (eqv ==> eqv) (@Setoid.const X Y) := const_eqv.

