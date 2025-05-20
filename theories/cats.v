From epit Require Export setoids.

(** * Bisimulation and coinductive types in the Rocq proof assistant
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
  - The notion of map between setoids: [X -eqv-> Y]
*)

(** * Part 1: Categories

    In this first course, we aim specifically at the formalization of initial algebras and final coalgebras. The shortest path therefore takes us through defining:
    - categories and functors
    - isomorphisms
    - inital/final objects
    - (co)algebras

*)

(** * 1. Categories

    We start by formalizing the bits of category theory we need to build up to initial algebras and final coalgebras.
    Importantly, notice that objects are captured as a Type, while the homset between two objects are a Setoid.
    Indeed, thinking of standard examples, arrows may be functions (we want to consider them extensionally),
    lambda termes (we want to consider them up-to βε), etc...
    We package in the same structure both the data and the axioms.
*)

Structure Category :=
  {
    (* the collection of objects *)
    ob :> Type;
    (* for each pair of objects, the collection of morphisms
        (a [Setoid] rather than [Type], because we want to be
         able to specify how to compare morphisms for equality) *)
    hom:> ob -> ob -> Setoid;
    (* for each object [A] the identity morphism on [A] *)
    id: forall {A}, hom A A;
    (* for each triple of objects the composition operation on morphisms *)
    comp: forall {A B C}, hom B C -> hom A B -> hom A C;

    (* composition should preserve morphism equivalence
        intuitively: [forall f f', f≡f' -> forall g g', g≡g' -> g∘f ≡ g'∘f'] *)
    comp_eqv:: forall {A B C}, Proper (eqv ==> eqv ==> eqv) (@comp A B C);

    (* identity is a neutral element on the left  *)
    idl: forall {A B} f, @comp A A B f id ≡ f;
    (* and on the right  *)
    idr: forall {A B} f, @comp B A A id f ≡ f;
    (* composition is associative *)
    compA: forall {A B C D} f g h, @comp A B D (@comp B C D h g) f ≡ @comp A C D h (@comp A B C g f)
  }.

(** thanks to the two coercions [:>] in the first two lines,
    a category [𝐂] can automatically be casted 
    - into a type (its type of objects), so that we can write
    [forall A B C: 𝐂] to quantify over objects, rather than [forall A B C: ob 𝐂]
    - into a function with two arguments (its type of morphisms), so that we can write
    [f: 𝐂 A B] instead of [f: hom 𝐂 A B]
    (below we actually define a notation so that we can also write just [f: A ~> B])
 *)

(** we declare many arguments as implicit 
    for instance, [id] formally has two arguments:
    the category [𝐂] of which it belongs to, and the object [A] which is both its source and target
    those can be inferred automatically most of the time, by the following command we declare them as implicit.
 *)
Arguments id {_ _}.
(** similarly, composition has six arguments (the category, the three objects, the two morphisms)
    we declare the first four as implicit since so that it suffices to provide the two morphisms *)
Arguments comp {_ _ _ _}.

(** standard notations for composition and homsets *)
Notation "g ∘ f" := (comp g f).
Notation "A ~> B" := (hom _ A B) (at level 99, B at level 200, format "A  ~>  B").


(** We can already toy with the structure by defining a few categories.
   Note that [Program] allows you to only fill in explicitely the data in the definition of the structure.
   It will try to solve the properties automatically, and will provide them to you as obligations to solve interactively otherwise.
 *)
Section example_categories.

  (** The category with a single object, and a single morphism. *)
  Program Definition UNIT: Category :=
    {|
      ob             := unit;
      hom _ _        := unit;
      id _           := tt;
      comp _ _ _ _ _ := tt;
    |}.
  Next Obligation. by destruct f. Qed.
  Next Obligation. by destruct f. Qed.

  (** Important for us: the category of types and functions *)
  Program Definition TYPES: Category :=
    {|
      ob := Type;
      hom A B := eq_setoid (A -> B);
      id _ := fun x => x;
      comp _ _ _ f g := fun x => f (g x);
    |}.

  (** ** Exercise
    Define the category REL, whose objects are [Type]s and morphisms are relations.
  *)
    Fail Program Definition REL: Category := {|  |}.

    (* BEGIN SOLUTION *)
    (* {|
      ob := Type;
      hom A B := A -> B -> Prop;
      id _ := @eq _;
      comp _ _ _ R S := fun x y => exists z, S x z /\ R z y;
    |}.
  Next Obligation.
    cbn. repeat intro. split; intros (z & ? & ?); exists z; split; firstorder.
  Qed.
  Next Obligation.
    cbn; firstorder; subst; auto.
  Qed.
  Next Obligation.
    cbn; firstorder; subst; auto.
  Qed.
  Next Obligation.
    cbn; firstorder.
  Qed. *)
  (* END SOLUTION *)

  (** ** Exercise
    Given a Type [A] and a preorder [R] on [A], define the category PRE whose objects are [A]s and morphisms x -> y if and only if x <= y.
    Hints:
    - The standard library provides the [PreOrder] structure.
    - Warning: you may have to define your own setoid.
      If so, you can do so using the following constructor:
        Setoid.build : ∀ (sort : Type) (eqv : relation sort), Equivalence eqv → Setoid
  *)
    Fail Program Definition PRE {A R} (PR : @PreOrder A R) : Category := {| |}.

  (* BEGIN SOLUTION *)
    Definition TT {A} : A -> A -> Prop := fun _ _ => True.
    Instance TTeq {A}: Equivalence (@TT A).
    constructor; cbv; intuition.
    Qed.

    Definition P_setoid (P : Prop) : setoids.Setoid := Setoid.build P TT _.

    Program Definition PRE {A R} (PR : @PreOrder A R) : Category
   :=
    {|
      ob := A ;
      hom x y := P_setoid (R x y) ;
      id := PreOrder_Reflexive ;
      comp x y z H H' := PreOrder_Transitive _ _ _ H' H
    |}.

  (* END SOLUTION *)

  (** ** Exercise
    Define the [dual] category.
  *)
  Fail Program Definition dual (𝐂: Category): Category :=
    {| |}.

  (* BEGIN SOLUTION *)
  Program Definition dual (𝐂: Category): Category :=
    {|
      ob := ob 𝐂;
      hom A B := 𝐂 B A;
      id _ := id;
      comp _ _ _ f g := g ∘ f;

      idl := @idr 𝐂;
      idr := @idl 𝐂;
    |}.
  Next Obligation.
    repeat intro. by apply comp_eqv.
  Qed.
  Next Obligation.
    symmetry. apply compA.
  Qed.
  (* END SOLUTION *)

End example_categories.



(** * 2. Isomorphisms *)

(** ** epi/monos *)
Section epimono.
  Context {𝐂: Category}.
  Definition epi {A B: 𝐂} (f: A ~> B) := forall C (g h: B ~> C), g ∘ f ≡ h ∘ f -> g ≡ h.
  Definition mono {A B: 𝐂} (f: A ~> B) := forall C (g h: C ~> A), f ∘ g ≡ f ∘ h -> g ≡ h.
End epimono.

(** ** isomorphisms *)
Section iso.
  Context {𝐂: Category}.
  Record iso (A B: 𝐂) :=
    {
      (* two morphisms *)
      fwd: A ~> B;
      bwd: B ~> A;
      (* and the proofs that they compose to the identity *)
      isoE : fwd ∘ bwd ≡ id;
      isoE': bwd ∘ fwd ≡ id
    }.
  (** like before, some arguments may remain implicit *)
  Arguments fwd {_ _}.
  Arguments bwd {_ _}.
  (** notations for the forward and backward morphisms *)
  Notation "i ^1"  := (fwd i) (at level 20).
  Notation "i ^-1" := (bwd i) (at level 20).
  Infix "≃" := iso (at level 70).

  (** identity isomorphism *)
  Program Definition iso_refl A: A ≃ A :=
    {| fwd := id; bwd := id |}.
  Next Obligation. intro. apply idl. Qed.
  Next Obligation. intro. apply idl. Qed.

  (** inverting an isomorphism *)
  Program Definition iso_sym A B (i: A ≃ B): B ≃ A :=
    {| fwd := i^-1; bwd := i^1 |}.
  Next Obligation. apply isoE'. Qed.
  Next Obligation. apply isoE. Qed.

  (** composition of isomorphisms *)
  Program Definition iso_trans A B C (i: A ≃ B) (j: B ≃ C): A ≃ C :=
    {| fwd := j^1 ∘ i^1; bwd := i^-1 ∘ j^-1 |}.
  Next Obligation.
    (* SOLUTION *)
    intros. transitivity (j^1 ∘ (i^1 ∘ i ^-1) ∘ j ^-1).
    - by rewrite !compA.
    - rewrite isoE idl. by apply isoE.
  Qed.
  Next Obligation.
    (* SOLUTION *)
    intros. transitivity (i ^-1 ∘ (j ^-1 ∘ j^1) ∘ i^1).
    - by rewrite !compA.
    - rewrite isoE' idl. by apply isoE'.
  Qed.

  Lemma epi_iso A B (i: A ≃ B): epi (i^1).
  (* BEGIN SOLUTION *)
  Proof. intros C g h E. by rewrite -(idl _ g) -(isoE i) -compA E compA isoE idl. Qed.
  (* END SOLUTION *)

  Lemma mono_iso A B (i: A ≃ B): mono (i^1).
  (* BEGIN SOLUTION *)
  Proof. intros C g h E. by rewrite -(idr _ g) -(isoE' i) compA E -compA isoE' idr. Qed.
  (* END SOLUTION *)

End iso.
Notation "i ^1" := (fwd i) (at level 20).
Notation "i ^-1" := (bwd i) (at level 20).
Infix "≃" := iso (at level 70).



(** * 3. Initial and final objects *)

Section universal.

  Context {𝐂: Category}.

  (** an object [I] is initial if for every other object [X],
      there exists a unique morphism [I~>X]  *)
  Record initial (I: 𝐂) := {
      init_mor:> forall X, I ~> X;
      init_mor_unique: forall X (f: I ~> X), f ≡ init_mor X;
    }.
  (** in particular, any two parallel morphisms out of [I] must be equal *)
  Lemma init_unique I (i: initial I) X (f g: I ~> X): f ≡ g.
  Proof.
    by rewrite (init_mor_unique i _ f) (init_mor_unique i _ g).
  Qed.

  (** initial objects are all isomorphic *)
  Lemma initial_iso I I': initial I -> initial I' -> I ≃ I'.
  Proof.
  (* SOLUTION *)
    intros i i'.
    exists (i _) (i' _).
    apply (init_unique i').
    apply (init_unique i).
  Qed.

  (** dually, an object [Z] is final if for every other object [X],
      there exists a unique morphism [X~>Z]
      Given what we do in the sequel, we found it more convenient to directly ask for [fin_unique] in the definition.
   *)
  Record final (Z: 𝐂) := {
      fin_mor:> forall X, X ~> Z;
      fin_unique: forall X (f g: X ~> Z), f ≡ g;
    }.

  Lemma final_unique Z Z': final Z -> final Z' -> Z ≃ Z'.
  Proof.
  (* SOLUTION *)
    intros f f'.
    exists (f' _) (f _).
    apply (fin_unique f').
    apply (fin_unique f).
  Qed.

End universal.

Section example_initial_final.

  (** ** Exercise
    Define the initial and final objects in TYPES
  *)

  (* BEGIN SOLUTION *)
  (*
  Definition initial_types : @initial TYPES False.
  esplit.
  refine (fun _ abs => match abs : False with end).
  intros.
  apply funext; intros [].
  Qed.

  Definition final_types : @final TYPES unit.
  esplit.
  refine (fun _ _ => tt).
  intros.
  apply funext; intros a; destruct (f a); destruct (g a); reflexivity.
  Qed. *)
  (* END SOLUTION *)

End example_initial_final.



(** * 4. Functors *)

Record Functor (𝐂 𝐃: Category) :=
  {
    (* the action of the functor on objects (notation [F A] thanks to the coercion) *)
    app':> 𝐂 -> 𝐃;
    (* the action of the functor on morphisms
        (no coercion, we have to write [app F f] for what is usually written [F f] in maths) *)
    app : forall {A B}, 𝐂 A B -> 𝐃 (app' A) (app' B);

    (* the action of the functor on morphisms should preserve morphism equivalence
        (i.e., [forall f f': A ~> B, f ≡ f' -> app F f ≡ app F f']) *)
    app_eqv:: forall {A B}, Proper (eqv ==> eqv) (@app A B);
    (* functors preserve identity morphisms *)
    app_id: forall {A}, app (id: A ~> A) ≡ id;
    (* functors preserve composition *)
    app_comp: forall {U V W} (f: U ~> V) (g: V ~> W), app (g ∘ f) ≡ app g ∘ app f;
  }.

(** The identity functor *)
Program Definition functor_id {𝐂}: Functor 𝐂 𝐂 :=
  {|
    (* identity on objects *)
    app' A := A;
    (* and on morphisms *)
    app A B (f: A ~> B) := f;
  |}.
Next Obligation. by intros. Qed.

(** Composition of functors *)
Program Definition functor_comp {𝐂 𝐃 𝐄} (G: Functor 𝐃 𝐄) (F: Functor 𝐂 𝐃): Functor 𝐂 𝐄 :=
  {|
    (* we just compose the two components *)
    app' A := G (F A);
    app A B (f: A ~> B) := app G (app F f);
  |}.
Next Obligation.
  intros* f g fg. by apply app_eqv, app_eqv.
Qed.
Next Obligation. cbn; intros. by rewrite 2!app_id. Qed.
Next Obligation. cbn; intros. by rewrite 2!app_comp. Qed.

(** Constant functor *)
Program Definition functor_constant {𝐂 𝐃: Category} (D: 𝐃): Functor 𝐂 𝐃:=
  {|
    (* always the given object on objects *)
    app' _ := D;
    (* always the identity on morphisms *)
    app _ _ _ := id
  |}.
Next Obligation. by cbn; intros. Qed.
Next Obligation. cbn; intros. by rewrite idl. Qed.

(** Functors preserve isomorphisms *)
Lemma app_iso {𝐂 𝐃} (F: Functor 𝐂 𝐃) A B: A ≃ B -> F A ≃ F B.
Proof.
  (** note how we can also provide the two morphisms from within the proof *)
  intro i. esplit.
  exact (app F (i^1)).
  exact (app F (i^-1)).
  (* SOLUTION *)
  by rewrite -app_comp isoE app_id.
  by rewrite -app_comp isoE' app_id.
Qed.



(** * 5. Algebras *)

Section algebra.

  (** We fix in this section a category [𝐂] with an endofunctor [F] *)
  Context {𝐂: Category}.
  Variable F: Functor 𝐂 𝐂.

  (** F-algebras: an object [A] and a morphism [a: F A ~> A]
      (here [A=alg_car] and [a=alg_mor]) *)
  Record Algebra := alg
    {
      alg_car:> 𝐂;
      alg_mor:> F alg_car ~> alg_car
    }.

  (** F-algebra homomorphisms from [(A, a: F A ~> A)] to [(B, b: F B ~> B)]:
      morphisms [f: A ~> B] such that the following square commutes:

       F A ---F f---> F B
        |              |
        a              b
        |              |
        v              v
        A -----f-----> B 

      i.e., f ∘ a ≡ b ∘ F f

      below, [f=alg_bod], [a=alg_mor A], [b=alg_mor B], [A=alg_car A], [B=alg_car B]
      we write [F f] as [app F f]
      and we do not need to write [alg_mor] and [alg_car] because they are coercions
   *)
  Record Alg_hom (A B: Algebra) := alg_hom
    {
      alg_bod:> A ~> B;                     (** alg_car A ~> alg_car B *)
      algE: alg_bod ∘ A ≡ B ∘ app F alg_bod (** alg_bod ∘ alg_mor A ≡ alg_mor B ∘ app F alg_bod *)
    }.
  Arguments alg_bod {_ _}.

  (** The identity algebra homomorphism, from an algebra to itself

       F A ---F id--> F A
        |              |
        a              a
        |              |
        v              v
        A -----id----> A

   *)
  Program Definition alg_id (A: Algebra): Alg_hom A A :=
    {| alg_bod := id |}.
  Next Obligation.
    (* SOLUTION *)
    intro. by rewrite app_id idl idr.
  Qed.

  (** Composing algebra homomorphisms

       F A ---F f---> F B ---F g---> F C
        |              |              |
        a              b              c
        |              |              |
        v              v              v
        A -----f-----> B -----g-----> C 

   *)
  Program Definition alg_comp (A B C: Algebra)
    (g: Alg_hom B C) (f: Alg_hom A B): Alg_hom A C :=
    {| alg_bod := g ∘ f |}.
  Next Obligation.
    (* SOLUTION *)
    intros. by rewrite compA algE -compA algE app_comp compA.
  Qed.

  (** We compare algebra homomorphisms via their underlying morphisms *)
  (** the following line defines [f ≡ g] for [f,g : Alg_hom A B] to be
      [alg_bod f ≡ alg_bod g], i.e., an equivalence of morphisms in [𝐂] *)
  Canonical Alg_hom_setoid (A B: Algebra) :=
    kern_setoid _ (@alg_bod A B).

  (** F-algebras and their homomorphisms form a category *)
  Program Canonical ALGEBRAS: Category :=
    {| ob := Algebra ; id := @alg_id ; comp := @alg_comp |}.
  (* SOLUTION *)
  Next Obligation. intros * f f' H g g' G. by apply comp_eqv. Qed.
  Next Obligation. intros. apply idl. Qed.
  Next Obligation. intros. apply idr. Qed.
  Next Obligation. intros. apply compA. Qed.

  Section initial_algebra.
    (** an initial algebra is "just" an initial object in the above category of algebras *)
    Context {I: Algebra} (H: initial I).

    (** ** Lambek's lemma: initial F-algebras are fixpoints for F,
        i.e., their underlying morphism actually is an isomorphism *)

    (** shorthand for this morphism *)
    Let i: 𝐂 (F I) I := I.

    (** we construct an algebra structure on [F I] *)
    Let FI := alg (F I) (app F i).

    (** by initiality, this yields the backward morphism *)
    Let j: 𝐂 I (F I) := H FI.

    (** it remains to prove that they are inverse of each other *)
    Lemma Lambek1: i ∘ j ≡ id.
    Proof.
      (* SOLUTION *)
      set i' := alg_hom FI I i (eqv_refl _).
      apply (init_unique H I (i' ∘ H FI) (alg_id _)).
    Qed.
    Lemma Lambek2: j ∘ i ≡ id.
    Proof.
      (* SOLUTION *)
      by rewrite (algE j) /= -app_comp Lambek1 app_id.
    Qed.

    (** packing everything together *)
    Definition Lambek: F I ≃ I :=
      {| fwd := i;
         bwd := j;
         isoE := Lambek1;
         isoE' := Lambek2 |}.
  End initial_algebra.

End algebra.
Arguments alg {_ _ _}.


(** * 6. Dually, coalgebras *)
Section coalgebra.

  (** We fix in this section a category [𝐂] with an endofunctor [F]. *)
  Context {𝐂: Category}.
  Variable F: Functor 𝐂 𝐂.

  (** F-coalgebras: an object and a morphism *)
  Record Coalgebra := coalg
    {
      coalg_car:> 𝐂;
      coalg_mor:> coalg_car ~> F coalg_car
    }.

  (** F-coalgebra homomorphisms: morphisms making the obvious square commute *)
  Record Coalg_hom (A B: Coalgebra) := coalg_hom
    {
      coalg_bod:> A ~> B;
      coalgE: B ∘ coalg_bod ≡ app F coalg_bod ∘ A
    }.
  Arguments coalg_bod {_ _}.

  Program Definition coalg_id (A: Coalgebra): Coalg_hom A A :=
    {| coalg_bod := id |}.
  Next Obligation.
    (* SOLUTION *)
    intros. by rewrite app_id idl idr.
  Qed.

  Program Definition coalg_comp (A B C: Coalgebra)
    (g: Coalg_hom B C) (f: Coalg_hom A B): Coalg_hom A C :=
    {| coalg_bod := g ∘ f |}.
  Next Obligation.
    (* SOLUTION *)
    intros. by rewrite -compA coalgE compA coalgE app_comp compA.
  Qed.

  (** We compare coalgebra homomorphisms via their underlying morphisms *)
  Canonical Coalg_hom_setoid (A B: Coalgebra) :=
    kern_setoid _ (@coalg_bod A B).

  (** F-coalgebras form a category *)
  Program Canonical Structure COALGEBRAS: Category :=
    {| ob := Coalgebra ; id := @coalg_id ; comp := @coalg_comp |}.
  (* SOLUTION *)
  Next Obligation. intros* f f' H g g' G. by apply comp_eqv. Qed.
  Next Obligation. intros. apply idl. Qed.
  Next Obligation. intros. apply idr. Qed.
  Next Obligation. intros. apply compA. Qed.

  Section final_coalgebra.
    Context {Z: Coalgebra} (H: final Z).

    (** ** CoLambek's lemma: final F-coalgebras are fixpoints for F,
        i.e., their underlying morphism actually is an isomorphism *)

    Lemma CoLambek: F Z ≃ Z.
    Abort.

    (* BEGIN SOLUTION *)
    (** shorthand for this morphism *)
    Let z: 𝐂 Z (F Z) := Z.

    (** we construct a coalgebra structure on [F Z] *)
    Let FZ := coalg (F Z) (app F z).

    (** by finality, this yields the backward morphism *)
    Let y: 𝐂 (F Z) Z := H FZ.

    (** it remains to prove that they are inverse of each other *)
    Lemma CoLambek1: y ∘ z ≡ id.
    Proof.
      set z' := coalg_hom Z FZ z (eqv_refl _).
      apply (fin_unique H _ (H FZ ∘ z') (coalg_id _)).
    Qed.
    Lemma CoLambek2: z ∘ y ≡ id.
    Proof.
      by rewrite (coalgE y) /= -app_comp CoLambek1 app_id.
    Qed.

    (** packing everything together *)
    Definition CoLambek: F Z ≃ Z :=
      {| fwd := y;
         bwd := z;
         isoE := CoLambek1;
         isoE' := CoLambek2 |}.
    (* END SOLUTION *)
  End final_coalgebra.

End coalgebra.
Arguments coalg {_ _ _}.
