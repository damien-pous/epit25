From Stdlib Require Import Basics List.
From Stdlib Require Import Setoid Morphisms.
From Stdlib Require Import ssreflect ssrfun ssrbool.

Set Implicit Arguments.
Unset Transparent Obligations.
Set Primitive Projections.
Set Universe Polymorphism.

Definition const {X Y} y: X -> Y := fun _ => y.
Arguments const {_ _} _ _/.

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
Next Obligation. move=>x y xy. apply f, g, xy. Qed.
Program Canonical Structure const {X Y: type} (y: Y): morphism X Y :=
  build_morphism (const y) _.
Next Obligation. move=>/=_ _ _. apply Equivalence_eqv. Qed.

End Setoid.
Notation Setoid := Setoid.type.
#[reversible] Coercion Setoid.sort: Setoid >-> Sortclass.
#[reversible] Coercion Setoid.body: Setoid.morphism >-> Funclass.
Existing Instance Setoid.Equivalence_eqv.
Existing Instance Setoid.body_eqv.
Notation "X '-eqv->' Y" := (Setoid.morphism X%type Y%type) (at level 99, Y at level 200).
Canonical Setoid.id.
Canonical Setoid.comp.
Canonical Setoid.const.
Definition eqv {X: Setoid} := Setoid.eqv X.
Infix "≡" := eqv (at level 70).
Infix "≡[ X ]" := (@eqv X) (at level 70, only parsing).
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
Canonical False_setoid := eq_setoid False.

Canonical Structure Prop_setoid := Setoid.build Prop iff _.

Program Canonical dprod_setoid A (X: A -> Setoid) :=
  Setoid.build (forall a, X a) (fun f g => forall a, f a ≡ g a) _.
Next Obligation.
  constructor.
  - by move=>??.
  - by move=>????; symmetry.
  - by move=>??????; etransitivity; eauto.
Qed.

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
  {| Setoid.body _ := None |}.
Program Definition Some' {X: Setoid}: X -eqv-> option X :=
  {| Setoid.body := Some |}.
Next Obligation. intros ? ? E. apply E. Qed.
Program Definition option_pack {X Y: Setoid} (y: Y) (f: X -eqv-> Y): option X -eqv-> Y :=
  {| Setoid.body x := match x with None => y | Some x => f x end |}.
Next Obligation. intros [|] [|] E; cbn in E; try tauto. now apply f. reflexivity. Qed.
Program Definition option_map' {X Y} (f: X -eqv-> Y): option X -eqv-> option Y :=
  Setoid.build_morphism (option_map f) _.
Next Obligation. intros [] [] E; cbn; try tauto. now apply f. Qed.

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

Program Definition kern_setoid A (X: Setoid) (f: A -> X) :=
  Setoid.build A (fun a b => f a ≡ f b) _.
Next Obligation.
  constructor.
  - by move=>?.
  - by move=>???.
  - by move=>?????; etransitivity; eauto.
Defined.
Lemma kern_eqv A (X: Setoid) (f: A -> X): Proper (@eqv (kern_setoid X f) ==> eqv) f.
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
Notation "A ~> B" := (hom _ A B) (at level 99, B at level 200, format "A  ~>  B").

(** dual category *)
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
Next Obligation. by case f. Qed.
Next Obligation. by case f. Qed.


(** * epi/monos *)
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
  Lemma init_unq' I (i: initial I) X (g: I ~> X): g ≡ i X.
  Proof. by apply init_unq. Qed.
  Program Definition Build_initial' I (f: forall X, I ~> X) (Hf: forall X (g: I ~> X), g ≡ f X): initial I :=
    {| init_mor := f |}.
  Next Obligation. transitivity (f X); [|symmetry]; apply Hf. Qed.
  
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
  Lemma fin_unq' Z (f: final Z) X (g: X ~> Z): g ≡ f X.
  Proof. by apply fin_unq. Qed.
  Program Definition Build_final' Z (f: forall X, X ~> Z) (Hf: forall X (g: X ~> Z), g ≡ f X): final Z :=
    {| fin_mor := f |}.
  Next Obligation. transitivity (f X); [|symmetry]; apply Hf. Qed.
  
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
  intros f g H. by do 2 apply app_eqv.
Qed.
Next Obligation. by rewrite 2!app_id. Qed.
Next Obligation. by rewrite 2!app_comp. Qed.

Program Definition functor_constant {𝐂 𝐃: CATEGORY} (A: 𝐃): FUNCTOR 𝐂 𝐃:=
  {| app' _ := A; app _ _ _ := id |}.
Next Obligation. by intros ???. Qed.
Next Obligation. by rewrite idl. Qed.

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
    by rewrite app_id idl idr.
  Qed.
  
  Program Definition alg_comp (A B C: ALGEBRA)
    (g: alg_hom B C) (f: alg_hom A B): alg_hom A C :=
    {| alg_hom_ := g ∘ f |}.
  Next Obligation.
    by rewrite compA algE -compA algE app_comp compA.
  Qed.

  Canonical alg_hom_setoid (A B: ALGEBRA) :=
    kern_setoid _ (@alg_hom_ A B).

  Program Canonical Structure ALGEBRAS: CATEGORY :=
    {| ob := ALGEBRA ; id := @alg_id ; comp := @alg_comp |}.
  Next Obligation. intros f f' H g g' G. by apply comp_eqv. Qed.
  Next Obligation. apply idl. Qed.
  Next Obligation. apply idr. Qed.
  Next Obligation. apply compA. Qed.

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

    Definition rec (X: ALGEBRA): 𝐂 I X := H X.
    Lemma recE X: rec X ∘ I ≡ X ∘ app F (rec X).
    Proof. apply algE. Qed.
    Lemma rec_comp (X Y: ALGEBRA) (f: X ~> Y): alg_hom_ f ∘ rec X ≡ rec Y.
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
    by rewrite app_id idl idr.
  Qed.
  
  Program Definition coalg_comp (A B C: COALGEBRA)
    (g: coalg_hom B C) (f: coalg_hom A B): coalg_hom A C :=
    {| coalg_hom_ := g ∘ f |}.
  Next Obligation.
    by rewrite -compA coalgE compA coalgE app_comp compA.
  Qed.

  Canonical coalg_hom_setoid (A B: COALGEBRA) :=
    kern_setoid _ (@coalg_hom_ A B).

  Program Canonical Structure COALGEBRAS: CATEGORY :=
    {| ob := COALGEBRA ; id := @coalg_id ; comp := @coalg_comp |}.
  Next Obligation. intros f f' H g g' G. by apply comp_eqv. Qed.
  Next Obligation. apply idl. Qed.
  Next Obligation. apply idr. Qed.
  Next Obligation. apply compA. Qed.

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

    Definition corec (X: COALGEBRA): 𝐂 X Z := H X.
    Lemma corecE X: Z ∘ corec X  ≡ app F (corec X) ∘ X.
    Proof. apply coalgE. Qed.
    Lemma corec_comp (X Y: COALGEBRA) (f: X ~> Y): corec Y ∘ coalg_hom_ f ≡ corec X.
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


(** ** endofunctors on TYPES *)
Notation TFUNCTOR := (FUNCTOR TYPES TYPES).

(** X^A *)
Program Definition TF_exp A: TFUNCTOR :=
  {| app' X := (A -> X); app X Y f g := comp f g |}.

Axiom fun_ext: forall A B (f g: A -> B), (forall a, f a = g a) -> f = g. (* TOTHINK: or do ETYPES *)
Axiom prop_ext: forall A B: Prop, (A <-> B) -> A = B. 

(** option *)
Program Definition TF_option: TFUNCTOR :=
  {| app' := option; app := Option.map |}.
Next Obligation. by apply fun_ext=>[[|]]. Qed.
Next Obligation. by apply fun_ext=>[[|]]. Qed.

(** list *)
Program Definition TF_list: TFUNCTOR :=
  {| app' := list; app := List.map |}.
Next Obligation. apply fun_ext; elim=>/=; congruence. Qed.
Next Obligation. apply fun_ext; elim=>/=; congruence. Qed.

(** powerset *)
Program Definition TF_pow: TFUNCTOR :=
  {| app' X := (X -> Prop); app X Y f S := fun y => exists x, S x /\ y = f x |}.
Next Obligation.
  apply fun_ext=>S;  apply fun_ext=>y.
  apply prop_ext; split=>H; eauto.
  by destruct H as [? [Sy <-]]. 
Qed.
Next Obligation.
  apply fun_ext=>S;  apply fun_ext=>y.
  apply prop_ext; split; move=>[x [Hx ->]]; eauto.
  destruct Hx as [? [? ->]]; eauto.
Qed.

Inductive nat := O | S(n: nat). 

Definition nat_alg: ALGEBRA TF_option.
  exists nat. case. exact S. exact O.
Defined.

Lemma init_nat_alg: initial nat_alg.
Proof.
  unshelve eapply Build_initial'.
  - intro f. unshelve eexists. 
    elim. exact (alg_bod f None).
    intros _ x. exact (alg_bod f (Some x)).
    by apply fun_ext=>[[|]].
  - simpl. intros X g. apply fun_ext.
    elim=>/=[|n IH]. apply (f_equal (fun f => f None) (algE g)).
    rewrite -IH. apply (f_equal (fun f => f (Some _)) (algE g)). 
Qed.

(* TODO: fails for coinductives (= need even more axioms) *)


(** ** endofunctors on ETYPES *)


(** category of types and extensional functions *)
Program Definition ETYPES: CATEGORY :=
  {|
    ob := Type;
    hom A B := dprod_setoid (fun _: A => eq_setoid B);
    id _ := fun x => x;
    comp _ _ _ f g := fun x => f (g x);
  |}.
Next Obligation.
  intros f f' ff g g' gg a. by rewrite ff gg.
Qed.

Notation EFUNCTOR := (FUNCTOR ETYPES ETYPES).

(** X^A *)
Program Definition EF_exp A: EFUNCTOR :=
  {| app' X := (A -> X); app X Y f g := comp f g |}.
Next Obligation.
  intros f g fg h. apply fun_ext=>a. apply fg. (* still need [fun_ext] *)
Qed.

(** option *)
Program Definition EF_option: EFUNCTOR :=
  {| app' := option; app := Option.map |}.
Next Obligation. intros f g fg [a|]=>//=. f_equal; apply fg. Qed.
Next Obligation. by case a. Qed.
Next Obligation. by case a. Qed.

(** list *)
Program Definition EF_list: EFUNCTOR :=
  {| app' := list; app := List.map |}.
Next Obligation. intros f g fg. elim=> [|a q IH]=>//=. by f_equal. Qed.
Next Obligation. elim a=>/=; congruence. Qed.
Next Obligation. elim a=>/=; congruence. Qed.

(** powerset *)
Program Definition EF_pow: EFUNCTOR :=
  {| app' X := (X -> Prop); app X Y f S := fun y => exists x, S x /\ y = f x |}.
Next Obligation.
  intros f g fg S. apply: fun_ext=>b. apply: prop_ext. (* still need [fun_ext] and [prop_ext] *)
  by setoid_rewrite fg.
Qed.
Next Obligation.
  apply fun_ext=>x. apply prop_ext; split=>H; eauto.
  by destruct H as [? [Sy <-]]. 
Qed.
Next Obligation.
  apply fun_ext=>w.
  apply prop_ext; split; move=>[x [Hx ->]]; eauto.
  destruct Hx as [? [? ->]]; eauto.
Qed.

Definition nat_alg': ALGEBRA EF_option.
  exists nat. case. exact S. exact O.
Defined.

Lemma init_nat_alg': initial nat_alg'.
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

(* TODO: fails for coinductives (= need even more axioms) *)

(** ** endofunctors on SETOIDS *)

(** category of setoids and setoid morphisms *)
Program Definition SETOIDS: CATEGORY :=
  {|
    ob := Setoid;
    hom := setoid_morphisms_setoid;
    id := @Setoid.id;
    comp := @Setoid.comp;
  |}.

Notation SFUNCTOR := (FUNCTOR SETOIDS SETOIDS).

(** X^A *)
Program Canonical Structure SF_power (A: Setoid): SFUNCTOR :=
  {| app' X := setoid_morphisms_setoid A X; app X Y f := _ |}.
Next Obligation.
  exists (fun g => Setoid.comp f g). by apply comp_eqv_. 
Defined.
Next Obligation. intros ?? H??. apply (H _). Qed.

(** option *)
Program Canonical Structure SF_option: SFUNCTOR :=
  {| app' := option_setoid; app := @option_map' |}. 
Next Obligation. by intros ?? H []; cbn. Qed.
Next Obligation. by case a; cbn. Qed.
Next Obligation. by case a; cbn. Qed.

(** list *)
Program Canonical Structure SF_list: SFUNCTOR :=
  {| app' := list_setoid; app X Y f := _ |}.
Next Obligation.
  exists (List.map f).
  intro h; induction h as [|a h IH]; intros [|b k]; cbn; try tauto; intros [].
  split. now apply f. now apply IH. 
Defined.
Next Obligation. intros f g fg l. cbn. induction l; try split; trivial. Qed.
Next Obligation. induction a; split; trivial. Qed.
Next Obligation. induction a; split; trivial. Qed.

(** powerset *)
Program Definition SF_pow: SFUNCTOR :=
  {| app' X := ((X -eqv-> Prop): Setoid); app X Y f := _ |}.
Next Obligation.
  unshelve eexists. intro S.
  exists (fun y => exists x, S x /\ y ≡ f x).
  move=>y y' yy/=. abstract by setoid_rewrite yy. 
  move=>S T ST y/=. abstract (split; move=>[x [Sx E]]; exists x; split=>//; by apply ST).
Defined.
Next Obligation.
  intros f g fg S b; simpl.
  by setoid_rewrite fg.
Qed.
Next Obligation.
  split=>H; eauto.
  by destruct H as [? [Sy ->]].
Qed.
Next Obligation.
  split; move=>[x [Hx E]]; eauto.
  destruct Hx as [u [Hu F]]. exists u. split=>//.
  by rewrite -F.
Qed.

Definition nat_alg'': ALGEBRA SF_option.
  exists (eq_setoid nat). unshelve eexists.
  case. exact S. exact O.
  move=>[a|] [b|]//=; congruence. 
Defined.

Lemma init_nat_alg'': initial nat_alg''.
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


(* TODO: succeeds for coinductives (by defining bisimilarity) *)
