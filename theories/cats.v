From epit Require Export setoids.

(** Bisimulation and coinductive types in the Rocq proof assistant
    Course 1: Formalizing initial algebras and final coalgebras---towards the need for quotients
*)

(** * Preliminaries: Setoids

  Setoids emulate quotients that mathematicians routinely use.
  A setoid is the data of a Type paired with an equivalence relation.
  Morphisms between setoids are maps preserving this equivalence.

  We take the file [setoids.v] as a black box providing support to work with them (albeit feel free to open it!).
  The module provides us with:
  - A structure of [Setoid]
  - Notations for its equivalence: [eqv], written [≡] ("\equiv")
*)

(** * Part 1: Categories

    We start by formalizing the bits of category theory we need to build up to initial algebras and final coalgebras.
    Importantly, notice that objects are a Type, while the homset between two objects are a Setoid.
    Indeed, thinking of standard examples, arrows may be functions (we want to consider them extensionally),
    lambda termes (we want to consider them up-to βε), etc...
    We package in the same structure both the data and the axioms.
*)

(** * Categories *)

Structure CATEGORY :=
  {
    ob :> Type;
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

(* We can already toy with the structure by defining a few categories.
   Note that [Program] allows you to only fill in explicitely the data in teh definition of the structure.
   It will try to solve the properties automatically, and will provide them to you as obligations to solve interactively otherwise.
 *)
Section example_categories.

  (** The category with a single object, and a single morphism. *)
  Program Definition UNIT: CATEGORY :=
    {|
      ob             := unit;
      hom _ _        := unit;
      id _           := tt;
      comp _ _ _ _ _ := tt;
    |}.
  Next Obligation. by destruct f. Qed.
  Next Obligation. by destruct f. Qed.

  (** Important for us: the category of types and functions *)
  Program Definition TYPES: CATEGORY :=
    {|
      ob := Type;
      hom A B := eq_setoid (A -> B);
      id _ := fun x => x;
      comp _ _ _ f g := fun x => f (g x);
    |}.

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

  (* TODO: other examples. Example for the students to define *)

End example_categories.

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
      init_unq': forall X (f: I ~> X), f ≡ init_mor X;
    }.
  Lemma init_unq I (i: initial I) X (f g: I ~> X): f ≡ g.
  Proof. by rewrite (init_unq' i _ f) (init_unq' i _ g). Qed.
          
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
      (* fin_unq': forall X (f: X ~> Z), f ≡ fin_mor X; *)
    }.
  (* Lemma fin_unq Z (z: final Z) X (f g: X ~> Z): f ≡ g. *)
  (* Proof. by rewrite (fin_unq' z _ f) (fin_unq' z _ g). Qed. *)
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
