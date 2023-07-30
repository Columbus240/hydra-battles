(** A formalization of denumerable sets. *)
(** by Florian Hatat, ENS-Lyon *)


From Coq Require Import Ensembles  Arith ArithRing (* Even Div2 *)
     Wellfounded Relations  Wf_nat  Finite_sets
     Logic.Epsilon  Sets.Image Lia.

From hydras Require Import MoreEpsilonIota PartialFun  GRelations
     Prelude.More_Arith.

Import Nat.

Set Implicit Arguments.

Arguments rel_injection {A B}.
Arguments rel_surjection {A B}.

From ZornsLemma Require Import CountableTypes Families.

Lemma image_as_Im {A B : Type} (U : Ensemble A) (f : A -> B) :
  image U f = Im U f.
Proof.
  apply Extensionality_Ensembles; split; intros y Hy.
  - destruct Hy as [x [Hx Hy]].
    subst. exists x; auto.
  - inversion Hy; subst; clear Hy.
    exists x; auto.
Qed.

Definition fun_restr {U V : Type} (f : U -> V)
  {A : Ensemble U} {B : Ensemble V}
  (Hf : fun_codomain A B f) :
  { x : U | In A x } -> { y : V | In B y } :=
  fun p : { x : U | In A x } =>
    exist (fun y : V => In B y)
      (f (proj1_sig p))
      (Hf (proj1_sig p) (proj2_sig p)).

(** A is countable if there exists an injection from [A] to
  [Full_set nat]. *)
Notation countable := ZornsLemma.CountableTypes.Countable.

Section Countable.

  Section Definitions.
    Variable U : Type.
    Variable A : Ensemble U.
    Let Dnat : Ensemble nat := @Full_set nat.

    (** Predicate for relations which number the elements of A.

  These relations map each element of A to at least one integer, but they
  are not required to be functional (injectivity is only needed to ensure that
  A is countable). *)

    Definition rel_numbers (R: GRelation U nat) := rel_injection A Dnat R.

    (** Predicate for relations which enumerate A. *)
    Definition rel_enumerates (R : GRelation nat U) := rel_surjection Dnat A R.

    Theorem countable_surj :
      countable A <-> exists R, rel_enumerates R.
    Proof.
    Admitted.

  End Definitions.

  Variable U : Type.

  (** [Union _ A B] is countable if [A] and [B] are countable. *)

  Section Countable_union.
    (* used in Schutte_basics.v *)
    Definition countable_union (E : Ensemble U) (F : Ensemble U) :
      countable E -> countable F -> countable (Union E F) :=
      countable_union2.
  End Countable_union.

  Section Countable_inclusion.

    Variables E F : Ensemble U.

    Definition countable_inclusion :
      countable E -> @Included _ F E -> countable F :=
      countable_downward_closed F E.

  End Countable_inclusion.

  (* Union of all sets B with B in A. *)
  Section Infinite_union.

    Variable A : Ensemble (Ensemble U).

    Definition Infinite_union (x : U) : Prop :=
      In (FamilyUnion A) x.

    Definition countable_union_qcq :
      countable A ->
      (forall b : Ensemble U, In A b -> countable b) ->
      countable (FamilyUnion A) :=
      countable_family_union A.
  End Infinite_union.

  Section Countable_empty.

    Lemma countable_empty :
      countable (@Empty_set U).
    Proof.
      exists (fun _ => 0%nat).
      intros p.
      destruct (proj2_sig p).
    Qed.

  End Countable_empty.

  Section Countable_singleton.

    Variable x : U.

    Lemma countable_singleton :
      countable (@Singleton _ x).
    Proof.
      exists (fun _ => 0%nat).
      intros [y0 H0] [y1 H1] _.
      apply ProofIrrelevance.ProofIrrelevanceTheory.subset_eq_compat.
      inversion H0; subst; clear H0.
      inversion H1; subst; clear H1.
      reflexivity.
    Qed.

  End Countable_singleton.

  Section Countable_seq_range.

    Definition seq_range (f : nat -> U) : Ensemble U :=
      image (@Full_set nat) f.

    Lemma seq_range_countable :
      forall f, countable (seq_range f).
    Proof.
      intros f.
      unfold seq_range.
      rewrite image_as_Im.
      apply countable_img.
      apply countable_type_ensemble.
      apply nat_countable.
    Qed.

  End Countable_seq_range.

  Section Countable_bijection.

    Variable V : Type.

    Variable A : Ensemble U.
    Variable B : Ensemble V.
    Variable g : U -> V.

    Hypothesis g_bij : fun_bijection A B g.

    (* convert a [fun_bijection] to a [bijection] in the sense of the
       [ZornsLemma] library. *)

    (* define [fun_bijection] as proposition instead of as inductive type? *)
    Lemma fun_bijection_codomain :
      fun_codomain A B g.
    Proof.
      destruct g_bij; assumption.
    Defined.

    Lemma fun_bijection_is_ZL_bijection :
      FunctionProperties.bijective
        (fun_restr fun_bijection_codomain).
    Proof.
      destruct g_bij.
      split.
      - intros [x0 Hx0] [x1 Hx1] Hx.
        apply ProofIrrelevance.ProofIrrelevanceTheory.subset_eq_compat.
        inversion Hx; subst; clear Hx.
        apply H1; auto.
      - intros [y Hy].
        specialize (H0 y Hy) as [x [Hx0 Hx1]].
        subst. exists (exist _ x Hx0).
        apply ProofIrrelevance.ProofIrrelevanceTheory.subset_eq_compat.
        reflexivity.
    Qed.

    Lemma countable_bij_fun :
      countable A -> countable B.
    Proof.
      intros H.
      apply surj_countable
        with (f := fun_restr fun_bijection_codomain);
        auto.
      apply fun_bijection_is_ZL_bijection.
    Qed.

    Lemma countable_bij_funR :
      countable B -> countable A.
    Proof.
      intros H.
      apply inj_countable
        with (f := fun_restr fun_bijection_codomain);
        auto.
      apply fun_bijection_is_ZL_bijection.
    Qed.

  End Countable_bijection.

  Section Countable_finite.

    Variable A : Ensemble U.
    Hypothesis A_finite : @Finite _ A.

    Definition countable_finite : countable A :=
      Finite_impl_Countable A A_finite.

  End Countable_finite.

End Countable.

Lemma countable_image : forall (U V:Type)(DA : Ensemble U)(f:U->V),
    countable DA -> countable (image DA f).
Proof.
  intros.
  rewrite image_as_Im.
  apply countable_img.
  assumption.
Qed.
