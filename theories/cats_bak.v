From Coq Require Import Basics List Fin.
From Coq Require Import Setoid Morphisms.
From Coq Require Import ssreflect ssrfun ssrbool.

Set Warnings "-deprecated-instance-without-locality".
Set Warnings "-deprecated-tacopt-without-locality".
Set Implicit Arguments.
Unset Transparent Obligations.
Obligation Tactic := ((by cbn) || idtac).
Set Primitive Projections.
Set Universe Polymorphism.

Axiom funext: forall A B (f g: A -> B), (forall a, f a = g a) -> f = g.
Axiom propext: forall A B: Prop, (A <-> B) -> A = B.

Definition const {X Y} y: X -> Y := fun _ => y.
Arguments const {_ _} _ _/.
Infix "×" := prod (at level 40).

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



(** * categories *)
Structure CATEGORY :=
  {
    ob:> Type;
    hom:> ob -> ob -> Setoid;
#[canonical=no] id: forall {A}, hom A A;
#[canonical=no] comp: forall {A B C}, hom B C -> hom A B -> hom A C;
#[canonical=no] comp_eqv:: forall {A B C}, Proper (eqv ==> eqv ==> eqv) (@comp A B C);
#[canonical=no] idl: forall {A B} f, @comp A A B f id ≡ f;
#[canonical=no] idr: forall {A B} f, @comp B A A id f ≡ f;
#[canonical=no] compA: forall {A B C D} f g h, @comp A B D (@comp B C D h g) f ≡ @comp A C D h (@comp A B C g f)
  }.
Arguments id {_ _}.
Arguments comp {_ _ _ _}.
Notation "g ∘ f" := (comp g f).
Infix "∘[ 𝐂 ] " := (@comp 𝐂 _ _ _) (at level 40, left associativity, only parsing).
Notation "A ~> B" := (hom _ A B) (at level 99, B at level 200, format "A  ~>  B").

(** dual category (SKIP??) *)
Program Definition dual (𝐂: CATEGORY): CATEGORY :=
  {|
    ob := ob 𝐂;
    hom A B := 𝐂 B A;
    id _ := id;
    comp _ _ _ f g := g ∘ f;
    idl := @idr 𝐂;
    idr := @idl 𝐂;
  |}.
Next Obligation.
  repeat intro. by apply: comp_eqv.
Qed.
Next Obligation.
  symmetry. apply compA.
Qed.

(** category of types and functions *)
Program Definition TYPES: CATEGORY :=
  {|
    ob := Type;
    hom A B := eq_setoid (A -> B);
    id _ := fun x => x;
    comp _ _ _ f g := fun x => f (g x);
  |}.

(** single object/morphism category *)
Program Definition UNIT: CATEGORY :=
  {|
    ob := unit;
    hom _ _ := unit;
    id _ := tt;
    comp _ _ _ _ _ := tt;
  |}.
Next Obligation. by destruct f. Qed.
Next Obligation. by destruct f. Qed.


(** * epi/monos (SKIP??) *)
Section epimono.
  Context {𝐂: CATEGORY}.
  Definition epi {A B: 𝐂} (f: A ~> B) := forall C (g h: B ~> C), g ∘ f ≡ h ∘ f -> g ≡ h.
  Definition mono {A B: 𝐂} (f: A ~> B) := forall C (g h: C ~> A), f ∘ g ≡ f ∘ h -> g ≡ h.
End epimono.


(** * isomorphisms *)
Section iso.
  Context {𝐂: CATEGORY}.
  Record iso (A B: 𝐂) :=
    { fwd: A ~> B;
      bwd: B ~> A;
      isoE: fwd ∘ bwd ≡ id;
      isoE': bwd ∘ fwd ≡ id
    }.
  Arguments fwd {_ _}.
  Arguments bwd {_ _}.
  Notation "i ^1" := (fwd i) (at level 20).
  Notation "i ^-1" := (bwd i) (at level 20).
  Infix "≃" := iso (at level 70).

  Definition iso_refl A: A ≃ A.
    exists id id; apply idl.
  Defined.

  Definition iso_sym A B: A ≃ B -> B ≃ A.
    intro i. exists (i^-1) (i^1). apply isoE'. apply isoE.
  Defined.

  Definition iso_trans A B D: A ≃ B -> B ≃ D -> A ≃ D.
    intros i j. exists (j^1 ∘ i^1) (i^-1 ∘ j^-1).
    transitivity (j^1 ∘ (i^1 ∘ i ^-1) ∘ j ^-1). by rewrite !compA. rewrite isoE idl. by apply isoE.
    transitivity (i ^-1 ∘ (j ^-1 ∘ j^1) ∘ i^1). by rewrite !compA. rewrite isoE' idl. by apply isoE'.
  Defined.

  Lemma epi_iso A B (i: A ≃ B): epi (i^1).
  Proof. intros C g h E. by rewrite -(idl _ g) -(isoE i) -compA E compA isoE idl. Qed.
  Lemma mono_iso A B (i: A ≃ B): mono (i^1).
  Proof. intros C g h E. by rewrite -(idr _ g) -(isoE' i) compA E -compA isoE' idr. Qed.

End iso.
Notation "i ^1" := (fwd i) (at level 20).
Notation "i ^-1" := (bwd i) (at level 20).
Infix "≃" := iso (at level 70).


(** * initial and final objects *)
Section universal.
  Context {𝐂: CATEGORY}.
  Record initial (I: 𝐂) := {
      init_mor:> forall X, I ~> X;
      init_unq: forall X (f g: I ~> X), f ≡ g;
    }.
  (* SKIP? *)
  Program Definition Build_initial' I (f: forall X, I ~> X) (Hf: forall X (g: I ~> X), g ≡ f X): initial I :=
    {| init_mor := f |}.
  Next Obligation. intros; transitivity (f X); [|symmetry]; apply Hf. Qed.

  Lemma initial_unique I I': initial I -> initial I' -> I ≃ I'.
  Proof.
    intros i i'.
    exists (i _) (i' _).
    apply (init_unq i').
    apply (init_unq i).
  Qed.

  Record final (Z: 𝐂) := {
      fin_mor:> forall X, X ~> Z;
      fin_unq: forall X (f g: X ~> Z), f ≡ g;
    }.
  Program Definition Build_final' Z (f: forall X, X ~> Z) (Hf: forall X (g: X ~> Z), g ≡ f X): final Z :=
    {| fin_mor := f |}.
  Next Obligation. intros; transitivity (f X); [|symmetry]; apply Hf. Qed.

  Lemma final_unique Z Z': final Z -> final Z' -> Z ≃ Z'.
  Proof.
    intros f f'.
    exists (f' _) (f _).
    apply (fin_unq f').
    apply (fin_unq f).
  Qed.
End universal.


(** * functors *)
Record FUNCTOR (𝐂 𝐃: CATEGORY) :=
  {
    app':> 𝐂 -> 𝐃;
    app: forall {A B}, 𝐂 A B -> 𝐃 (app' A) (app' B);
    app_eqv:: forall {A B}, Proper (eqv ==> eqv) (@app A B);
    app_id: forall {A}, app (id: A ~> A) ≡ id;
    app_comp: forall {U V W} (f: U ~> V) (g: V ~> W), app (g ∘ f) ≡ app g ∘ app f;
  }.

Program Definition functor_id {𝐂}: FUNCTOR 𝐂 𝐂 :=
  {|
    app' A := A;
    app _ _ f := f;
  |}.
Next Obligation.
  by intros ???.
Qed.

Program Definition functor_comp {𝐂 𝐃 𝐄} (G: FUNCTOR 𝐃 𝐄) (F: FUNCTOR 𝐂 𝐃): FUNCTOR 𝐂 𝐄 :=
  {|
    app' A := G (F A);
    app _ _ f := app G (app F f);
  |}.
Next Obligation.
  intros* f g fg. by do 2 apply app_eqv.
Qed.
Next Obligation. cbn; intros. by rewrite 2!app_id. Qed.
Next Obligation. cbn; intros. by rewrite 2!app_comp. Qed.

Program Definition functor_constant {𝐂 𝐃: CATEGORY} (A: 𝐃): FUNCTOR 𝐂 𝐃:=
  {| app' _ := A; app _ _ _ := id |}.
Next Obligation. by cbn; intros. Qed.
Next Obligation. cbn; intros. by rewrite idl. Qed.

Definition app_iso {𝐂 𝐃} (F: FUNCTOR 𝐂 𝐃) A B: A ≃ B -> F A ≃ F B.
Proof.
  intro i. exists (app F (i^1)) (app F (i^-1)).
  by rewrite -app_comp isoE app_id.
  by rewrite -app_comp isoE' app_id.
Qed.

(** * algebras *)
Section algebra.
  Context {𝐂: CATEGORY}.
  Section s.
  Variable F: FUNCTOR 𝐂 𝐂.
  Record ALGEBRA := alg
    {
      alg_car:> 𝐂;
      alg_bod:> F alg_car ~> alg_car
    }.

  Record alg_hom (A B: ALGEBRA) :=
    {
      alg_hom_:> A ~> B;
      algE: alg_hom_ ∘ A ≡ B ∘ app F alg_hom_
    }.
  Arguments alg_hom_ {_ _}.

  Program Definition alg_id (A: ALGEBRA): alg_hom A A := {| alg_hom_ := id |}.
  Next Obligation.
    intro. by rewrite app_id idl idr.
  Qed.

  Program Definition alg_comp (A B C: ALGEBRA)
    (g: alg_hom B C) (f: alg_hom A B): alg_hom A C :=
    {| alg_hom_ := g ∘ f |}.
  Next Obligation.
    intros. by rewrite compA algE -compA algE app_comp compA.
  Qed.

  Canonical alg_hom_setoid (A B: ALGEBRA) :=
    kern_setoid _ (@alg_hom_ A B).

  Program Canonical Structure ALGEBRAS: CATEGORY :=
    {| ob := ALGEBRA ; id := @alg_id ; comp := @alg_comp |}.
  Next Obligation. intros * f f' H g g' G. by apply comp_eqv. Qed.
  Next Obligation. intros. apply idl. Qed.
  Next Obligation. intros. apply idr. Qed.
  Next Obligation. intros. apply compA. Qed.

  Section initial_algebra.
    Context {I: ALGEBRA} (H: initial I).
    Definition Lambek: F I ≃ I.
    Proof.
      set i := alg_bod I.
      set FI := {| alg_car := F I; alg_bod := app F i |}.
      set j := H FI.
      have ij: i ∘ j ≡ id. {
        set i' := Build_alg_hom FI I i (eqv_refl _).
        apply (init_unq H I (i' ∘ H FI) (alg_id _)).
      }
      exists i (j: 𝐂 _ _); trivial.
      by rewrite (algE j) /= -app_comp ij app_id.
    Qed.

    (* SKIP?? *)
    Definition rec (X: ALGEBRA): 𝐂 I X := H X.
    Lemma recE X: rec X ∘ I ≡ X ∘ app F (rec X).
    Proof. apply algE. Qed.
    Lemma rec_comp (X Y: ALGEBRA) (f: X ~> Y): f ∘[𝐂] rec X ≡ rec Y.
    Proof. apply (init_unq H _ (f ∘ H X) (H Y)). Qed.
    Corollary rec_eqv (X: 𝐂) (f g: F X ~> X): f ≡ g -> rec (alg X f) ≡ rec (alg X g).
    Proof.
      intro fg.
      unshelve eset (i := _: alg X f ~> alg X g).
      exists (id: X ~> X)=>/=. abstract (by rewrite idr app_id idl).
      by rewrite -(rec_comp i) idr.
    Qed.
  End initial_algebra.
  End s.

End algebra.
Arguments alg {_ _ _}.


(** * dually, coalgebras *)
Section coalgebra.
  Context {𝐂: CATEGORY}.
  Section s.
  Variable F: FUNCTOR 𝐂 𝐂.
  Record COALGEBRA := coalg
    {
      coalg_car:> 𝐂;
      coalg_bod:> coalg_car ~> F coalg_car
    }.

  Record coalg_hom (A B: COALGEBRA) :=
    {
      coalg_hom_:> A ~> B;
      coalgE: B ∘ coalg_hom_ ≡ app F coalg_hom_ ∘ A
    }.
  Arguments coalg_hom_ {_ _}.

  Program Definition coalg_id (A: COALGEBRA): coalg_hom A A := {| coalg_hom_ := id |}.
  Next Obligation.
    intros. by rewrite app_id idl idr.
  Qed.

  Program Definition coalg_comp (A B C: COALGEBRA)
    (g: coalg_hom B C) (f: coalg_hom A B): coalg_hom A C :=
    {| coalg_hom_ := g ∘ f |}.
  Next Obligation.
    intros. by rewrite -compA coalgE compA coalgE app_comp compA.
  Qed.

  Canonical coalg_hom_setoid (A B: COALGEBRA) :=
    kern_setoid _ (@coalg_hom_ A B).

  Program Canonical Structure COALGEBRAS: CATEGORY :=
    {| ob := COALGEBRA ; id := @coalg_id ; comp := @coalg_comp |}.
  Next Obligation. intros* f f' H g g' G. by apply comp_eqv. Qed.
  Next Obligation. intros. apply idl. Qed.
  Next Obligation. intros. apply idr. Qed.
  Next Obligation. intros. apply compA. Qed.

  Section final_coalgebra.
    Context {Z: COALGEBRA} (H: final Z).
    Definition CoLambek: F Z ≃ Z.
    Proof.
      set z := coalg_bod Z.
      set FZ := {| coalg_car := F Z; coalg_bod := app F z |}.
      set y := H FZ.
      have yz: (y: 𝐂 _ _) ∘ z ≡ id. {
        set z' := Build_coalg_hom Z FZ z (eqv_refl _).
        apply (fin_unq H _ (H FZ ∘ z') (coalg_id _)).
      }
      exists (y: 𝐂 _ _) z; trivial.
      by rewrite (coalgE y) /= -app_comp yz app_id.
    Qed.

    (* SKIP?? *)
    Definition corec (X: COALGEBRA): 𝐂 X Z := H X.
    Lemma corecE X: Z ∘ corec X  ≡ app F (corec X) ∘ X.
    Proof. apply coalgE. Qed.
    Lemma corec_comp (X Y: COALGEBRA) (f: X ~> Y): corec Y ∘ f ≡ corec X.
    Proof. apply (fin_unq H _ (H Y ∘ f) (H X)). Qed.
    Corollary corec_eqv (X: 𝐂) (f g: X ~> F X): f ≡ g -> corec (coalg X f) ≡ corec (coalg X g).
    Proof.
      intro fg.
      unshelve eset (i := _: coalg X f ~> coalg X g).
      exists (id: X ~> X)=>/=. abstract (by rewrite idl app_id idr).
      by rewrite -(corec_comp i) idl.
    Qed.
  End final_coalgebra.
  End s.

End coalgebra.
Arguments coalg {_ _ _}.

(** * case-study in the category of types and functions *)
Module TYPES.

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

Definition nat_alg: ALGEBRA F_option :=
  {| alg_car := nat : ob TYPES;
     alg_bod x := match x with Some x => S x | None => O end |}.

Lemma init_nat_alg: initial nat_alg.
Proof.
  unshelve eapply Build_initial'.
  - intro f. unshelve eexists.
    elim. exact (alg_bod f None).
    intros _ x. exact (alg_bod f (Some x)).
    by apply funext=>[[|]].
  - simpl. intros X g. apply funext.
    elim=>/=[|n IH]. apply (f_equal (fun f => f None) (algE g)).
    rewrite -IH. apply (f_equal (fun f => f (Some _)) (algE g)).
Qed.

(** ** `conatural unary numbers' almost form the final coalgebra of the [option] functor *)

CoInductive conat := coO | coS(n: conat).

Definition conat_coalg: COALGEBRA F_option :=
  {| coalg_car := conat: ob TYPES;
     coalg_bod x := match x with coS n => Some n | coO => None end |}.

Lemma final_conat_coalg: final conat_coalg.
Proof.
  split.
  - intro f. unshelve eexists; cbn.
    cofix CH. intro x. destruct (coalg_bod f x) as [c|].
    apply coS, CH, c.
    apply coO.
    apply funext=>x. by destruct (coalg_bod f x).
  - intros X f g.
    admit.
Abort.


(** ** the empty set is the initial algebra of the [AxX] functor *)

Variant empty := .

Program Definition empty_alg A: ALGEBRA (F_times A) :=
  {| alg_car := empty;
     alg_bod x := match x.2 with end |}.

Lemma init_empty_alg A: initial (empty_alg A).
Proof.
  unshelve eapply Build_initial'.
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
  split.
  - intro f. unshelve eexists; cbn.
    cofix CH. intro x. destruct (coalg_bod f x) as [a y]. exact (cons a (CH y)).
    apply funext=>x; cbn. by destruct (coalg_bod f x).
  - intros X f g.
    admit.
Abort.

(** ** Polynomial Functors

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
  Program Definition apply (cont : container) : FUNCTOR :=
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

  Program Definition w_alg : ALGEBRA (apply cont) :=
    {| alg_car := W_sort;
       alg_bod x := (sup0 (projT1 x) (projT2 x)) |}.

  (* And indeed, [w_alg] is initial *)
  Lemma init_w_alg : initial w_alg.
  Proof.
    unshelve eapply Build_initial'.
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

End TYPES.


(** * case-study in the category of types and *extenstional* functions *)
Module ETYPES.

(** category of types and extensional functions *)
Program Canonical ETYPES: CATEGORY :=
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
Notation FUNCTOR := (FUNCTOR ETYPES ETYPES).

(** A×X *)
Program Definition F_times A: FUNCTOR :=
  {| app' X := A × X; app X Y f ax := (ax.1,f ax.2) |}.
Next Obligation.
  move=>/=A B C f g E [a b]/=. by rewrite E.
Qed.
Next Obligation.
  by move=>??[].
Qed.

(** option *)
Program Definition F_option: FUNCTOR :=
  {| app' := option; app := Option.map |}.
Next Obligation. intros * f g fg [a|]=>//=. f_equal; apply (fg a). Qed.
Next Obligation. by move=>?[]. Qed.
Next Obligation. by move=>*[]. Qed.

(** list *)
Program Definition F_list: FUNCTOR :=
  {| app' := list; app := List.map |}.
Next Obligation. move=>* f g /=fg. elim=> [|a q IH]=>//=. by f_equal. Qed.
Next Obligation. intros. elim=>/=; congruence. Qed.
Next Obligation. intros. elim=>/=; congruence. Qed.

(** X^A *)
Program Definition F_exp A: FUNCTOR :=
  {| app' X := (A -> X); app X Y f g := comp f g |}.
Next Obligation.
  move=>/=* f g fg h. apply funext=>a. apply fg. (* still need [funext] *)
Qed.

(** powerset *)
Program Definition F_pow: FUNCTOR :=
  {| app' X := (X -> Prop); app X Y f S := fun y => exists x, S x /\ y = f x |}.
Next Obligation.
  move=>/=* f g fg S. apply: funext=>b. apply: propext. (* still need [funext] and [propext] *)
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

Program Definition nat_alg: ALGEBRA F_option :=
  {| alg_car := nat;
     alg_bod x := match x with Some x => S x | None => O end |}.

Lemma init_nat_alg: initial nat_alg.
Proof.
  unshelve eapply Build_initial'.
  - intro f. unshelve eexists.
    elim. exact (alg_bod f None).
    intros _ x. exact (alg_bod f (Some x)).
    by case.
  - simpl. intros X g.
    elim=>/=[|n IH]. apply (algE g None).
    rewrite -IH. apply (algE g (Some _)).
Qed.

(** ** `conatural unary numbers' almost form the final coalgebra of the [option] functor *)

CoInductive conat := coO | coS(n: conat).

Definition conat_coalg: COALGEBRA F_option :=
  @coalg _ F_option conat (fun x => match x with coS n => Some n | coO => None end).

Lemma final_conat_coalg: final conat_coalg.
Proof.
  split.
  - intro f. unshelve eexists; cbn.
    cofix CH. intro x. destruct (coalg_bod f x) as [c|].
    apply coS, CH, c.
    apply coO.
    intro x; simpl. by destruct (coalg_bod f x).
  - intros X f g.
    cbn.
    intro x.                    (* does not help *)
Abort.

End ETYPES.


(** * case-study in the category of setoids and setoid morphisms *)

Module SETOIDS.

(** category of setoids and setoid morphisms *)
Program Canonical SETOIDS: CATEGORY :=
  {|
    ob := Setoid;
    hom := setoid_morphisms_setoid;
    id := @Setoid.id;
    comp := @Setoid.comp;
  |}.

(** ** endofunctors on SETOIDS *)
Notation FUNCTOR := (FUNCTOR SETOIDS SETOIDS).

(** A×X *)
Program Definition F_times (A: Setoid): FUNCTOR :=
  {| app' X := (A × X: Setoid);
     app X Y f := efun ax => (ax.1,f ax.2) |}.
Next Obligation.
  move=>/=A X Y f ax ay [aa xy]/=. by rewrite xy.
Qed.
Next Obligation.
  move=>/=A B C f g E [a b]//=.
Qed.

(** option *)
Program Definition F_option: FUNCTOR :=
  {| app' := option_setoid;
     app := @option_map' |}.    (* TODO: inline *)
Next Obligation. by intros * ?? H []; cbn. Qed.
Next Obligation. by move=>?[]. Qed.
Next Obligation. by move=>*[]. Qed.

(** list *)
Program Definition F_list: FUNCTOR :=
  {| app' := list_setoid;
     app X Y f := efun l => List.map f l |}.
Next Obligation.
  intros X Y f.
  elim=>[|a h IH] [|b k]/=; try tauto; intros [].
  split. by apply f. by apply IH.
Qed.
Next Obligation. intros * f g fg. by elim. Qed.
Next Obligation. intros *. by elim. Qed.
Next Obligation. intros *. by elim. Qed.

(** X^A *)
Program Definition F_exp (A: Setoid): FUNCTOR :=
  {| app' := setoid_morphisms_setoid A;
     app X Y f := efun g => Setoid.comp f g |}.
Next Obligation.
  intros*???. by apply comp_eqv_.
Qed.
Next Obligation.
  intros * ?? H??. apply (H _).
Qed.

(** powerset *)
Program Definition F_pow: FUNCTOR :=
  {| app' X := ((X -eqv-> Prop): Setoid);
     app X Y f := efun S y => exists x, S x /\ y ≡ f x |}.
Next Obligation.
  move=>* y y' yy/=. by setoid_rewrite yy.
Qed.
Next Obligation.
  move=>* S T ST y/=.
  split; move=>[x [Sx E]]; exists x; split=>//; by apply ST.
Qed.
Next Obligation.
  move=>* f g /=fg S b.
  by setoid_rewrite fg.
Qed.
Next Obligation.
  move=>/=*. split=>H; eauto.
  by destruct H as [? [Sy ->]].
Qed.
Next Obligation.
  move=>/=*. split; move=>[x [Hx E]]; eauto.
  destruct Hx as [u [Hu F]]. exists u. split=>//.
  by rewrite -F.
Qed.

(** ** natural unary numbers are the initial algebra of the [option] functor *)

Inductive nat := O | S(n: nat).

Program Definition nat_alg: ALGEBRA F_option :=
  {| alg_car := eq_setoid nat;
     alg_bod := efun x => match x with Some x => S x | None => O end |}.
Next Obligation.
  move=>[a|] [b|]//=; congruence.
Qed.

Lemma init_nat_alg: initial nat_alg.
Proof.
  unshelve eapply Build_initial'.
  - intro f. unshelve eexists. unshelve eexists.
    elim. exact (alg_bod f None).
    intros _ x. exact (alg_bod f (Some x)).
    cbn. typeclasses eauto.
    cbn. by case.
  - simpl. intros X g.
    elim=>/=[|n IH]. apply (algE g None).
    setoid_rewrite (algE g (Some _)). simpl.
    apply: Setoid.body_eqv=>/=. exact: IH.
Qed.

(** ** `conatural unary numbers modulo bisimilarity' are the final coalgebra of the [option] functor *)

CoInductive conat := coO | coS(n: conat).

Module conat1.

Definition bisimulation (R: relation conat) :=
  forall n m, R n m -> match n, m with
                 | coO,coO => True
                 | coS n,coS m => R n m
                 | _,_ => False
                 end.
Definition bisim n m := exists R, bisimulation R /\ R n m.
Lemma bisimulation_bisim: bisimulation bisim.
Proof.
  move=>[|n] [|m] [R [BR /BR Rnm]]//=.
  by exists R.
Qed.

Lemma Equivalence_bisim: Equivalence bisim.
Proof.
  split.
  - exists eq; split=>//. move=>[|n] [|m]=>//=; congruence.
  - exists (fun x y => bisim y x); split=>//. move=>[|n] [|m] /bisimulation_bisim=>//.
  - exists (fun x z => exists y, bisim x y /\ bisim y z); split; eauto.
    move=>[|u] [|v] [[|w] [/bisimulation_bisim+ /bisimulation_bisim]]=>//. eauto.
Qed.

Canonical conat_setoid := Setoid.build conat bisim Equivalence_bisim.

Definition conat_coalg: COALGEBRA F_option.
  refine (@coalg _ F_option conat_setoid (efun x => match x with coS n => Some n | coO => None end)).
Proof.
  abstract by move=>[|n] [|m] /bisimulation_bisim nm.
Defined.

Theorem final_conat_coalg: final conat_coalg.
Proof.
  split.
  - intro f.
    set g := cofix CH x :=
        match coalg_bod f x with
        | Some x => coS (CH x)
        | None => coO
        end.
    unshelve eexists. exists g.
    -- intros x y xy.
       set R := fun gx gy => exists x y, gx = g x /\ gy = g y /\ x ≡ y.
       exists R. split. 2: by unfold R; eauto.
       clear=>?? [x [y [-> [-> xy]]]]/=.
       have: coalg_bod f x ≡ coalg_bod f y. by apply: Setoid.body_eqv.
       case: (coalg_bod f x); case: (coalg_bod f y)=>//= i j ij; unfold R; eauto.
    -- intro x; simpl. case (coalg_bod f x)=>//=. reflexivity.
  - intros X f g x.
    set R := fun fx gx => exists x, fx ≡ coalg_hom_ f x /\ gx ≡ coalg_hom_ g x.
    exists R. split. 2: by unfold R; eauto.
    clear; move=>n m [x [nfx mgx]]//=.
    have /= := coalgE f x.
    have /= := coalgE g x.
    apply bisimulation_bisim in nfx.
    apply bisimulation_bisim in mgx.
    destruct (coalg_hom_ f x) eqn:fx;
    destruct (coalg_hom_ g x) eqn:gx;
    destruct (coalg_bod X x) eqn:Xx=>//=.
    -- intros _ _. destruct n; destruct m=>//=.
    -- intros ? ?. destruct n; destruct m=>//=.
       eexists; split.
       rewrite nfx. eassumption.
       rewrite mgx. eassumption.
Qed.

End conat1.

Module conat2.

CoInductive bisim: relation conat :=
| bisO: bisim coO coO
| bisS: Proper (bisim ==> bisim) coS.

Lemma Equivalence_bisim: Equivalence bisim.
Proof.
  split.
  - cofix CH; case; constructor; reflexivity.
  - cofix CH; move=>??[|n m nm]; constructor; by symmetry.
  - cofix CH; move=>???[|n m nm]; inversion_clear 1; constructor; etransitivity; eassumption.
Qed.

Canonical conat_setoid := Setoid.build conat bisim Equivalence_bisim.

Lemma bisimulation (n m: conat):
    n ≡ m <->
      match n, m with
      | coO,coO => True
      | coS n,coS m => n ≡ m
      | _,_ => False
      end.
Proof.
  split.
  - case:n=>[|x];case m=>[|y]; by inversion_clear 1.
  - case:n=>[|x];case m=>[|y]=>//; by constructor.
Defined.

Definition conat_coalg: COALGEBRA F_option.
  refine (@coalg _ F_option conat_setoid (efun x => match x with coS n => Some n | coO => None end)).
Proof.
  by move=>[|n] [|m] // /bisimulation nm; auto; elim nm.
Defined.

Theorem final_conat_coalg: final conat_coalg.
Proof.
  split.
  - intro f.
    set g := cofix CH x :=
        match coalg_bod f x with
        | Some x => coS (CH x)
        | None => coO
        end.
    unshelve eexists. exists g.
    -- cofix CH.
       move=>x y xy.
       apply (Setoid.body_eqv (coalg_bod f)) in xy.
       apply/bisimulation=>/=.
       destruct (coalg_bod f x);
       destruct (coalg_bod f y); move=>//=.
       by apply CH.
    -- intro x; simpl. case (coalg_bod f x)=>//=. reflexivity.
  - intros X f g.
    cofix CH.
    move=>x.
    have /= := coalgE f x.
    have /= := coalgE g x.
    remember (coalg_hom_ f x) as n eqn:nfx.
    remember (coalg_hom_ g x) as m eqn:mgx.
    setoid_rewrite <-nfx.
    setoid_rewrite <-mgx.
    destruct n;
    destruct m;
    destruct (coalg_bod X x)=>//=.
    -- constructor.
    -- move=>mgs nfs; constructor. rewrite mgs nfs. apply (CH _).
Admitted.                       (* not guarded... *)

End conat2.


(** ** the empty set is the initial algebra of the [AxX] functor *)

Variant empty := .

Program Definition empty_alg A: ALGEBRA (F_times A) :=
  {| alg_car := eq_setoid empty;
     alg_bod := efun x => match x.2 with end |}.
Next Obligation.
  by move=>/=A [?[]].
Qed.

Lemma init_empty_alg A: initial (empty_alg A).
Proof.
  unshelve eapply Build_initial'.
  - intro f. unshelve eexists. unshelve eexists.
    by case. by case. by case.
  - by cbn.
Qed.


(** ** streams modulo bisimularity are the final coalgebra of the [AxX] functor *)

CoInductive stream (A: Setoid) := cons { head: A; tail: stream A }.

Module stream2.

CoInductive bisim {A}: relation (stream A) :=
| bis_cons: forall s t, head s ≡ head t -> bisim (tail s) (tail t) -> bisim s t.

Lemma Equivalence_bisim {A}: Equivalence (@bisim A).
Proof.
  split.
  - cofix CH; move=>?; constructor; reflexivity.
  - cofix CH; move=>??[]; constructor; by symmetry.
  - cofix CH; move=>???; do 2 inversion_clear 1; constructor; etransitivity; eassumption.
Qed.

Canonical stream_setoid A := Setoid.build (stream A) bisim Equivalence_bisim.

Lemma bisimulation {A} (n m: stream A):
  n ≡ m <-> head n ≡ head m /\ tail n ≡ tail m.
Proof.
  split.
  - by inversion_clear 1.
  - by case; constructor.
Defined.

Definition stream_coalg A: COALGEBRA (F_times A).
  refine (@coalg _ (F_times A) (stream_setoid A)
            (efun s => (head s, tail s))).
Proof.
  by move=>s t/bisimulation.
Defined.

Lemma final_stream_coalg A: final (stream_coalg A).
Proof.
  split.
  - intro f.
    set g := cofix CH x := let y := coalg_bod f x in cons y.1 (CH y.2).
    unshelve eexists. eexists g.
    -- cofix CH. move=>x y xy.
       apply (Setoid.body_eqv (coalg_bod f)) in xy.
       constructor. apply xy. cbn. apply CH, xy.
    -- move=>x/=; split; reflexivity.
  - intros X f g.
    cofix CH. move=>x.
    have [/=fx1 fx2] := coalgE f x.
    have [/=gx1 gx2] := coalgE g x.
    constructor.
    -- by rewrite fx1 gx1.
    -- setoid_rewrite fx2. setoid_rewrite gx2. apply (CH _).
Admitted.    (* not guarded again, possibly because of the implicit upto in the second supbroof? *)

End stream2.

End SETOIDS.
