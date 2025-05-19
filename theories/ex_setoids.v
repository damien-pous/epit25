From epit Require Import cats.

(** * case-study in the category of setoids and setoid morphisms *)

(** category of setoids and setoid morphisms *)
Program Canonical SETOIDS: Category :=
  {|
    ob := Setoid;
    hom := setoid_morphisms_setoid;
    id := @Setoid.id;
    comp := @Setoid.comp;
  |}.

(** ** endofunctors on SETOIDS *)
Notation Functor := (Functor SETOIDS SETOIDS).

(** A×X *)
Program Definition F_times (A: Setoid): Functor :=
  {| app' X := (A × X: Setoid);
     app X Y f := efun ax => (ax.1,f ax.2) |}.
Next Obligation.
  intros A X Y f ax ay [aa xy]; cbn. by rewrite xy.
Qed.
Next Obligation.
  by intros A B C f g E [a b]; cbn.
Qed.

(** option *)
Program Definition F_option: Functor :=
  {| app' := option_setoid;
     app := @option_map' |}.    (* TODO: inline *)
Next Obligation. by intros * ?? H []; cbn. Qed.
Next Obligation. by intros ?[]. Qed.
Next Obligation. by intros *[]. Qed.

(** list *)
Program Definition F_list: Functor :=
  {| app' := list_setoid;
     app X Y f := efun l => List.map f l |}.
Next Obligation.
  intros X Y f l.
  induction l as [|a h IH]; intros [|b k]; cbn; try tauto.
  intros [ab hk]. split. by apply f. by apply IH.
Qed.
Next Obligation. intros * f g fg l. by induction l. Qed.
Next Obligation. intros * l. by induction l. Qed.
Next Obligation. intros * l. by induction l. Qed.

(** X^A *)
Program Definition F_exp (A: Setoid): Functor :=
  {| app' := setoid_morphisms_setoid A;
     app X Y f := efun g => Setoid.comp f g |}.
Next Obligation.
  intros*???. by apply comp_eqv_.
Qed.
Next Obligation.
  intros * ?? H??. apply (H _).
Qed.

(** powerset *)
Program Definition F_pow: Functor :=
  {| app' X := ((X -eqv-> Prop): Setoid);
     app X Y f := efun S y => exists x, S x /\ y ≡ f x |}.
Next Obligation.
  intros * y y' yy; cbn. by setoid_rewrite yy.
Qed.
Next Obligation.
  intros * S T ST y; cbn.
  split; intros [x [Sx E]]; exists x; split=>//; by apply ST.
Qed.
Next Obligation.
  intros * f g fg S b; cbn in *.
  by setoid_rewrite fg.
Qed.
Next Obligation.
  cbn; intros *. split=>H; eauto.
  by destruct H as [? [Sy ->]].
Qed.
Next Obligation.
  cbn; intros *. split; move=>[x [Hx E]]; eauto.
  destruct Hx as [u [Hu F]]. exists u. split=>//.
  by rewrite -F.
Qed.

(** ** natural unary numbers are the initial algebra of the [option] functor *)

Inductive nat := O | S(n: nat).

Definition nat_pack (n: option nat): nat :=
  match n with Some n => S n | None => O end.

Fixpoint nat_iter {X} (f: option X -> X) (n: nat) :=
  match n with
  | O => f None
  | S n => f (Some (nat_iter f n))
  end.

Program Definition nat_alg: Algebra F_option :=
  {| alg_car := eq_setoid nat;
     alg_mor := efun x => nat_pack x |}.
Next Obligation.
  intros [a|] [b|]=>//=; congruence.
Qed.

Lemma init_nat_alg: initial nat_alg.
Proof.
  esplit.
  - intro f. esplit. exists (nat_iter (alg_mor f)).
    -- cbn. typeclasses eauto.
    -- cbn. by case.
  - cbn. intros X g n.
    induction n as [|n IH].
    -- apply (algE g None).
    -- setoid_rewrite (algE g (Some _)). cbn.
       apply Setoid.body_eqv. exact IH.
Qed.

(** ** `conatural unary numbers modulo bisimilarity' are the final coalgebra of the [option] functor *)

CoInductive conat := coO | coS(n: conat).

Definition conat_unpack (n: conat): option conat :=
  match n with coS n => Some n | coO => None end.

CoFixpoint conat_coiter {X} (f: X -> option X) (x: X): conat :=
  match f x with
  | None => coO
  | Some y => coS (conat_coiter f y)
  end.

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

Program Definition conat_coalg: Coalgebra F_option :=
  {| coalg_car := conat_setoid;
     coalg_mor := efun n => conat_unpack n |}.
Next Obligation. 
  by move=>[|n] [|m] /bisimulation_bisim nm.
Qed.

Theorem final_conat_coalg: final conat_coalg.
Proof.
  esplit.
  - intros [X f].
    set g := conat_coiter f.
    esplit. exists g. 
    -- intros x y xy.
       set R := fun gx gy => exists x y, gx = g x /\ gy = g y /\ x ≡ y.
       exists R. split. 2: by unfold R; eauto.
       clear=>?? [x [y [-> [-> xy]]]]/=.
       apply f in xy. 
       destruct (f x);
       destruct (f y); unfold R; eauto.
    -- intro x=>/=. case (f x)=>//=. reflexivity.
  - intros [X h] [f Hf] [g Hg] x.
    set R := fun fx gx => exists x, fx ≡ f x /\ gx ≡ g x.
    exists R. split. 2: by unfold R; eauto.
    clear x; intros n m [x [nfx mgx]]=>//=.
    apply bisimulation_bisim in nfx.
    apply bisimulation_bisim in mgx.
    generalize (Hf x).
    generalize (Hg x). cbn. 
    destruct (f x) eqn:fx;
    destruct (g x) eqn:gx;
    destruct (h x) eqn:hx=>//=.
    -- destruct n; destruct m=>//=.
    -- destruct n; destruct m=>//=.
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
  - cofix CH; intros??[|n m nm]; constructor; by symmetry.
  - cofix CH; intros???[|n m nm]; inversion_clear 1; constructor; etransitivity; eassumption.
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
  - destruct n; destruct m; by inversion_clear 1.
  - destruct n; destruct m; try done; by constructor.
Qed.

Program Definition conat_coalg: Coalgebra F_option :=
  {| coalg_car := conat_setoid;
     coalg_mor := efun n => conat_unpack n |}.
Next Obligation. 
  by move=>[|n] [|m] // /bisimulation nm; auto; induction nm.
Qed.

Theorem final_conat_coalg: final conat_coalg.
Proof.
  split.
  - intros [X f].
    set g := conat_coiter f.
    esplit. exists g.
    -- cofix CH.
       intros x y xy.
       apply f in xy.
       apply/bisimulation=>/=.
       destruct (f x);
       destruct (f y)=>//=.
       by apply CH.
    -- intro x=>/=. case (f x)=>//=. reflexivity.
  - intros [X h] [f Hf] [g Hg].
    cofix CH.
    intro x.
    have /= := Hf x.
    have /= := Hg x.
    remember (f x) as n eqn:nfx.
    remember (g x) as m eqn:mgx.
    setoid_rewrite <-nfx.
    setoid_rewrite <-mgx.
    destruct n;
    destruct m;
    destruct (h x)=>//=.
    -- constructor.
    -- intros mgs nfs; constructor. rewrite mgs nfs. apply (CH _).
    (* not guarded... would need to unfold the implicit up-to technnique
       in the unicity part of the proof *)
Fail Qed.
Admitted.                    

End conat2.


(** ** the empty set is the initial algebra of the [AxX] functor *)

Variant empty := .

Program Definition empty_alg A: Algebra (F_times A) :=
  {| alg_car := eq_setoid empty;
     alg_mor := efun x => match x.2 with end |}.
Next Obligation.
  by intros A [?[]].
Qed.

Lemma init_empty_alg A: initial (empty_alg A).
Proof.
  esplit.
  - intro f. esplit. esplit.
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
  - cofix CH; intros ?; constructor; reflexivity.
  - cofix CH; intros ??[]; constructor; by symmetry.
  - cofix CH; intros ???; do 2 inversion_clear 1; constructor; etransitivity; eassumption.
Qed.

Canonical stream_setoid A := Setoid.build (stream A) bisim Equivalence_bisim.

Instance head_eqv A: Proper (bisim ==> eqv) (@head A).
Proof. by intros s t []. Qed.

Instance tail_eqv A: Proper (bisim ==> bisim) (@tail A).
Proof. by intros s t []. Qed.

Lemma bisimulation {A} (n m: stream A):
  n ≡ m <-> head n ≡ head m /\ tail n ≡ tail m.
Proof.
  split.
  - by inversion 1. 
  - by case; constructor.
Qed.

#[local] Obligation Tactic := idtac. 
Program Definition stream_coalg A: Coalgebra (F_times A) :=
  {| coalg_car := stream_setoid A;
     coalg_mor := efun s => (head s, tail s) |}.
Next Obligation.
  by move=>A s t/bisimulation.
Qed.

CoFixpoint stream_coiter {A: Setoid} {X} (f: X -> A×X) x :=
  cons (f x).1 (stream_coiter f (f x).2).

Lemma final_stream_coalg A: final (stream_coalg A).
Proof.
  split.
  - intros [X f].
    set g := stream_coiter f. 
    esplit. eexists g.
    -- cofix CH. intros x y xy.
       apply f in xy. 
       constructor. apply xy. cbn. apply CH, xy.
    -- intros x; cbn; split; reflexivity.
  - intros [X h] [f Hf] [g Hg].
    (** commented out: proof with implicit upto technique, not guarded **)
    (* cofix CH. intro x. *)
    (* destruct (Hf x) as [fx1 fx2]. *)
    (* destruct (Hg x) as [gx1 gx2]. *)
    (* cbn in *. *)
    (* constructor. *)
    (* -- by rewrite fx1 gx1. *)
    (* -- setoid_rewrite fx2. setoid_rewrite gx2. apply (CH _). *)

    (** making the up-to technique explicit, now guarded **)
    suff G: forall x fx gx, fx ≡ f x -> gx ≡ g x -> fx ≡ gx.
    by intro y; apply (G y).
    cofix CH. cbn. intros x fx gx Hfx Hgx.
    destruct (Hf x) as [fx1 fx2]. 
    destruct (Hg x) as [gx1 gx2].
    cbn in *. 
    constructor.
    (** why does rewrite fail?? **)
    -- Fail rewrite Hfx. 
       etransitivity. apply head_eqv. rewrite Hfx. reflexivity.
       setoid_rewrite fx1. symmetry.
       etransitivity. apply head_eqv. rewrite Hgx. reflexivity.
       apply gx1. 
    -- apply CH with (h x).2. 
       etransitivity. apply tail_eqv. rewrite Hfx. reflexivity.
       apply fx2. 
       etransitivity. apply tail_eqv. rewrite Hgx. reflexivity.
       apply gx2.
Qed.

End stream2.
