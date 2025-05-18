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
  move=>/=A X Y f ax ay [aa xy]/=. by rewrite xy.
Qed.
Next Obligation.
  move=>/=A B C f g E [a b]//=.
Qed.

(** option *)
Program Definition F_option: Functor :=
  {| app' := option_setoid;
     app := @option_map' |}.    (* TODO: inline *)
Next Obligation. by intros * ?? H []; cbn. Qed.
Next Obligation. by move=>?[]. Qed.
Next Obligation. by move=>*[]. Qed.

(** list *)
Program Definition F_list: Functor :=
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

Program Definition nat_alg: Algebra F_option :=
  {| alg_car := eq_setoid nat;
     alg_mor := efun x => match x with Some x => S x | None => O end |}.
Next Obligation.
  move=>[a|] [b|]//=; congruence.
Qed.

Lemma init_nat_alg: initial nat_alg.
Proof.
  unshelve esplit.
  - intro f. unshelve eexists. unshelve eexists.
    elim. exact (alg_mor f None).
    intros _ x. exact (alg_mor f (Some x)).
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

Definition conat_coalg: Coalgebra F_option.
  refine (@coalg _ F_option conat_setoid (efun x => match x with coS n => Some n | coO => None end)).
Proof.
  abstract by move=>[|n] [|m] /bisimulation_bisim nm.
Defined.

Theorem final_conat_coalg: final conat_coalg.
Proof.
  unshelve esplit.
  - intro f.
    set g := cofix CH x :=
        match coalg_mor f x with
        | Some x => coS (CH x)
        | None => coO
        end.
    unshelve eexists. exists g.
    -- intros x y xy.
       set R := fun gx gy => exists x y, gx = g x /\ gy = g y /\ x ≡ y.
       exists R. split. 2: by unfold R; eauto.
       clear=>?? [x [y [-> [-> xy]]]]/=.
       have: coalg_mor f x ≡ coalg_mor f y. by apply: Setoid.body_eqv.
       case: (coalg_mor f x); case: (coalg_mor f y)=>//= i j ij; unfold R; eauto.
    -- intro x; simpl. case (coalg_mor f x)=>//=. reflexivity.
  - intros X f g x.
    set R := fun fx gx => exists x, fx ≡ coalg_bod f x /\ gx ≡ coalg_bod g x.
    exists R. split. 2: by unfold R; eauto.
    clear; move=>n m [x [nfx mgx]]//=.
    have /= := coalgE f x.
    have /= := coalgE g x.
    apply bisimulation_bisim in nfx.
    apply bisimulation_bisim in mgx.
    destruct (coalg_bod f x) eqn:fx;
    destruct (coalg_bod g x) eqn:gx;
    destruct (coalg_mor X x) eqn:Xx=>//=.
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

Definition conat_coalg: Coalgebra F_option.
  refine (@coalg _ F_option conat_setoid (efun x => match x with coS n => Some n | coO => None end)).
Proof.
  by move=>[|n] [|m] // /bisimulation nm; auto; elim nm.
Defined.

Theorem final_conat_coalg: final conat_coalg.
Proof.
  split.
  - intro f.
    set g := cofix CH x :=
        match coalg_mor f x with
        | Some x => coS (CH x)
        | None => coO
        end.
    unshelve eexists. exists g.
    -- cofix CH.
       move=>x y xy.
       apply (Setoid.body_eqv (coalg_mor f)) in xy.
       apply/bisimulation=>/=.
       destruct (coalg_mor f x);
       destruct (coalg_mor f y); move=>//=.
       by apply CH.
    -- intro x; simpl. case (coalg_mor f x)=>//=. reflexivity.
  - intros X f g.
    cofix CH.
    move=>x.
    have /= := coalgE f x.
    have /= := coalgE g x.
    remember (coalg_bod f x) as n eqn:nfx.
    remember (coalg_bod g x) as m eqn:mgx.
    setoid_rewrite <-nfx.
    setoid_rewrite <-mgx.
    destruct n;
    destruct m;
    destruct (coalg_mor X x)=>//=.
    -- constructor.
    -- move=>mgs nfs; constructor. rewrite mgs nfs. apply (CH _).
Admitted.                       (* not guarded... *)

End conat2.


(** ** the empty set is the initial algebra of the [AxX] functor *)

Variant empty := .

Program Definition empty_alg A: Algebra (F_times A) :=
  {| alg_car := eq_setoid empty;
     alg_mor := efun x => match x.2 with end |}.
Next Obligation.
  by move=>/=A [?[]].
Qed.

Lemma init_empty_alg A: initial (empty_alg A).
Proof.
  unshelve esplit.
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

Instance head_eqv A: Proper (bisim ==> eqv) (@head A).
Proof. by move=>s t []. Qed.

Instance tail_eqv A: Proper (bisim ==> bisim) (@tail A).
Proof. by move=>s t []. Qed.

Lemma bisimulation {A} (n m: stream A):
  n ≡ m <-> head n ≡ head m /\ tail n ≡ tail m.
Proof.
  split.
  - by inversion 1. 
  - by case; constructor.
Qed.

Definition stream_coalg A: Coalgebra (F_times A).
  refine (@coalg _ (F_times A) (stream_setoid A)
            (efun s => (head s, tail s))).
Proof.
  by move=>s t/bisimulation.
Defined.

CoFixpoint stream_corec {A: Setoid} {X} (f: X -> A×X) x :=
  let '(a,y) := f x in cons a (stream_corec f y).

Lemma final_stream_coalg A: final (stream_coalg A).
Proof.
  split.
  - intro f.
    set g := cofix CH x := let y := coalg_mor f x in cons y.1 (CH y.2).
    unshelve eexists. eexists g.
    -- cofix CH. move=>x y xy.
       apply (Setoid.body_eqv (coalg_mor f)) in xy.
       constructor. apply xy. cbn. apply CH, xy.
    -- move=>x/=; split; reflexivity.
  - intros X f g.
    (** proof with implicit upto technique, not guarded **)
    (* cofix CH. move=>x. *)
    (* destruct (coalgE f x) as [fx1 fx2].  *)
    (* destruct (coalgE g x) as [gx1 gx2]. *)
    (* simpl in *.  *)
    (* constructor. *)
    (* -- by rewrite fx1 gx1. *)
    (* -- setoid_rewrite fx2. setoid_rewrite gx2. apply (CH _). *)
       
    (** making the up-to technique explicit, now guarded **)
    suff G: forall x fx gx, fx ≡ coalg_bod f x -> gx ≡ coalg_bod g x -> fx ≡ gx.
    by move=>y; apply: G.
    cofix CH. move=>x fx gx /=Hfx Hgx.
    destruct (coalgE f x) as [fx1 fx2]. 
    destruct (coalgE g x) as [gx1 gx2].
    simpl in *. 
    constructor.
    (** why does rewrite fail?? **)
    -- Fail rewrite Hfx. 
       etransitivity. apply head_eqv. rewrite Hfx. reflexivity.
       setoid_rewrite fx1. symmetry.
       etransitivity. apply head_eqv. rewrite Hgx. reflexivity.
       apply gx1. 
    -- apply: CH.
       etransitivity. apply tail_eqv. rewrite Hfx. reflexivity.
       apply fx2. 
       etransitivity. apply tail_eqv. rewrite Hgx. reflexivity.
       apply gx2.
Qed.

End stream2.
