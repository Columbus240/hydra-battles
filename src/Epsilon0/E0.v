(*  Pierre Casteran 
    LaBRI, University of Bordeaux 


   Class of ordinals less than epsilon0 


   [E0] is a class type for ordinal terms proved to be in normal form.
*)

Require Import Arith Max Bool Lia  Compare_dec  Relations Ensembles
        Wellfounded  Operators_Properties
        Prelude.More_Arith  Prelude.Restriction
        not_decreasing  ArithRing   DecPreOrder Logic.Eqdep_dec.


Require  Export T1 Hessenberg.
Set Implicit Arguments.

Declare Scope E0_scope.

Delimit Scope E0_scope with e0.
Open Scope E0_scope.


(** * Definitions *)

Class E0 : Type := mkord {cnf : T1; cnf_ok : nf cnf}.

Arguments cnf : clear implicits.

Hint Resolve cnf_ok : E0.



Definition Lt (alpha beta : E0) := T1.LT (@cnf alpha) (@cnf beta).
Definition Le (alpha beta : E0) := T1.LE (@cnf alpha) (@cnf beta).

Infix "<" := Lt : E0_scope.
Infix "<=" := Le : E0_scope.

Instance Zero : E0.
Proof.
  refine (@mkord T1.zero _);  now compute. 
Defined.


Definition Is_Limit (alpha : E0) : bool :=
  is_limit (@cnf alpha).

Definition Is_Succ (alpha : E0) : bool :=
  is_succ (@cnf alpha).

Instance _Omega : E0.
Proof.
  exists omega%t1; auto with T1.
Defined. 


Notation "'omega'"  := _Omega : E0_scope.



Instance Succ (alpha : E0) : E0.
Proof.
  refine (@mkord (T1.succ (@cnf alpha)) _); 
  apply succ_nf,  cnf_ok.
Defined.

Instance ord1 : E0.
Proof. 
  refine (@mkord (T1.succ zero) _);now compute. 
Defined.

Search (nf (_ + _)%t1).

Instance plus (alpha beta : E0) : E0.
Proof.
  refine (@mkord (T1.plus (@cnf alpha) (@cnf beta))_ );
    apply plus_nf; apply cnf_ok.
Defined.

Infix "+" := plus : E0_scope.

Check omega + omega.

Instance Phi0 (alpha: E0) : E0.
Proof.
  refine (@mkord (phi0 (cnf alpha)) _).
  apply nf_phi0; apply cnf_ok.
Defined.

Instance Omega_term (alpha: E0) (n: nat) : E0.
Proof.
  refine (@mkord (ocons (cnf alpha) n zero) _).
  apply nf_phi0; apply cnf_ok.
Defined.

Instance Ocons (alpha : E0) (n: nat) (beta: E0) : E0
  := (Omega_term alpha n + beta)%e0.                                                          

Instance FinS (i:nat) : E0.
Proof.
  refine (@mkord (FS i)%t1 _);apply T1.nf_FS.
Defined.



Instance Fin (i:nat) : E0.
Proof.
  destruct i.
  - exact Zero.
  - exact (FinS i).
Defined.

Coercion Fin : nat >-> E0.


Instance Mult (alpha beta : E0) : E0.
Proof.
  refine (@mkord (cnf alpha * cnf beta)%t1 _).
  apply nf_mult; apply cnf_ok.
Defined.


Infix "*" := Mult : E0_scope.

Instance Mult_i  (alpha: E0) (n: nat) : E0.
Proof.
  refine (@mkord (cnf alpha * n)%t1  _).
  apply nf_mult_fin.  apply cnf_ok.
Defined.

(** ** Lemmas *)

(* begin hide *)

Lemma cnf_rw (alpha:T1)(H :nf alpha) : cnf (mkord H) = alpha.
Proof. reflexivity. Defined.

(* end hide *)


(** *** On equality on type [E0] *)

Lemma nf_proof_unicity :
  forall (alpha:T1) (H H': nf alpha), H = H'.
Proof.
  intros;  red in H, H';  apply eq_proofs_unicity_on.
  destruct y. 
  - rewrite H; auto. 
  - rewrite H; right; discriminate. 
Qed.


Lemma E0_eq_intro : forall alpha beta : E0,
    cnf alpha = cnf beta -> alpha = beta.
Proof.
  destruct alpha, beta;simpl;intros; subst;f_equal; auto.
  apply nf_proof_unicity.
Qed.


Lemma E0_eq_iff alpha beta : alpha = beta <-> cnf alpha = cnf beta.
Proof.
 split.
 -  intro; now f_equal.  
 - intro; now apply E0_eq_intro.
Qed.


Hint Resolve E0_eq_intro : E0.

Ltac orefl := (apply E0_eq_intro; try reflexivity).

Ltac ochange alpha beta := (replace alpha with beta; [| orefl]).

Lemma E0_eq_dec : forall alpha beta: E0,
    {alpha = beta}+{alpha <> beta}.
Proof.
  destruct alpha, beta.
  destruct (T1_eq_dec cnf0 cnf1) as [e | n].
  - subst; left; auto with E0.
  - right; intro H; destruct n; now injection H.
Defined.

(** ** Adaptation to [E0] of lemmas about [T1]  *)

Lemma alpha_plus_zero alpha : alpha + Zero = alpha.
Proof.
  apply E0_eq_intro; simpl; now rewrite plus_a_zero.
Qed.

Hint Rewrite alpha_plus_zero : E0_rw.

Lemma cnf_Phi0 (alpha : E0) :
  cnf (Phi0 alpha) = phi0 (cnf alpha).
Proof.
 unfold Phi0. now rewrite cnf_rw.
Defined.

Lemma cnf_Succ (alpha : E0) :
  cnf (Succ alpha) = succ (cnf alpha).
Proof.
 unfold Succ. now rewrite cnf_rw.
Defined.

Lemma cnf_Omega_term (alpha: E0) (n: nat) :
  cnf (Omega_term alpha n) = omega_term (cnf alpha) n.
Proof.
  reflexivity.
Defined.

Lemma Is_Limit_Omega_term alpha i : alpha <> Zero ->
                                    Is_Limit (Omega_term alpha i).
Proof.
  intro H; unfold Is_Limit.
  destruct alpha; simpl; destruct cnf0.
   - destruct H; auto with E0.
   -  auto.
Qed.

Lemma Is_Limit_Phi0 alpha  : alpha <> Zero ->
                             Is_Limit (Phi0 alpha).
Proof.
  unfold Phi0; apply Is_Limit_Omega_term.
Qed.

Hint Resolve Is_Limit_Phi0 : E0.




Definition Zero_Succ_Limit_dec (alpha : E0) :
  {alpha = Zero} + {Is_Limit alpha = true} +
  {beta : E0  | alpha = Succ beta}.
  destruct alpha as [t Ht];  destruct (zero_succ_limit_dec  Ht).  
  -  destruct s. 
     + left; left. 
       unfold Zero; subst t; f_equal.
       apply nf_proof_unicity.
     + left;right; unfold Is_Limit; now simpl. 
  -  destruct s as [beta [H0 H1]]; right;  eexists (@mkord beta H0).
     subst t; unfold Succ; f_equal; apply nf_proof_unicity.
Defined.

Definition Pred (alpha: E0) : E0 :=
  match Zero_Succ_Limit_dec alpha with
      inl _ => Zero
    | inr (exist _ beta _) => beta
  end.


Tactic Notation "mko" constr(alpha) := refine (@mkord alpha eq_refl).

Instance Two : E0 :=  ltac:(mko (fin 2)).

Instance Omega_2 : E0 :=ltac:(mko (omega * omega)%t1).

Lemma Lt_wf : well_founded Lt.
Proof.
 split; intros [t Ht] H; apply (Acc_inverse_image _ _ LT (@cnf) 
  {| cnf := t; cnf_ok := Ht |} );
  now   apply T1.nf_Acc. 
Defined.


Hint Resolve Lt_wf : E0.

Lemma Lt_le : forall alpha beta,  beta < alpha -> Succ beta <= alpha.
Proof.
  destruct alpha, beta;simpl in *;  unfold le, Lt;simpl.
  intro. split; auto.
  - apply T1.succ_nf; auto.
  -  split; auto.
     + apply T1.lt_succ_le;auto.
       destruct H; tauto.
Qed.



Lemma Pred_of_Succ:  forall alpha, Pred (Succ alpha) = alpha.
Proof.
  unfold Pred; intro alpha; destruct (Zero_Succ_Limit_dec (Succ alpha)).
  destruct s.
  - unfold Succ, Zero in e; injection  e .
    intro H; now   destruct (T1.succ_not_zero (cnf alpha)).
  -  unfold is_limit, Succ in e; simpl in e;
       destruct (@T1.is_limit_succ (cnf alpha)); auto.
        destruct alpha; simpl; auto. 
  -  destruct s.
    { unfold Succ in e.
      injection e.
      destruct alpha, x;simpl; intros; apply T1.succ_injective in H; auto.
      -  subst; replace cnf_ok1 with cnf_ok0; trivial.
         eapply nf_proof_unicity.
    }
Qed.

Hint Rewrite Pred_of_Succ: E0_rw.

Lemma  Pred_Lt alpha : alpha <> Zero  ->  Is_Limit alpha = false ->
                       Pred alpha < alpha.
Proof.
  unfold Is_Limit, Pred, Lt; destruct alpha; intros. simpl.
  destruct (T1.zero_succ_limit_dec cnf_ok0 ).
  destruct s.
  - subst. unfold Zero in H. destruct H. f_equal;apply nf_proof_unicity.
  - simpl in H0; rewrite i in H0; discriminate.
  - destruct s. destruct a. simpl. subst cnf0.
    apply LT_succ;auto.
Qed.

Hint Resolve Pred_Lt : E0.



Lemma Succ_is_succ : forall alpha, Is_Succ (Succ alpha).
destruct alpha; unfold Is_Succ, Succ; cbn; apply T1.succ_is_succ.
Qed.

Hint Resolve Succ_is_succ : E0.

Ltac ord_eq alpha beta := assert (alpha = beta);
      [apply E0_eq_intro ; try reflexivity|].




Lemma FinS_eq i : FinS i = Fin (S i).
Proof. reflexivity. Qed.

Lemma mult_fin_rw alpha (i:nat) : (alpha *  i)%e0 = Mult_i alpha i.
Proof.
 orefl;cbn; f_equal; now destruct i.
 Qed.





Lemma FinS_Succ_eq : forall i, FinS i = Succ (Fin i).
Proof.
  intro i; compute. orefl; now destruct i.
Qed.

Hint Rewrite FinS_Succ_eq : E0_rw.

Lemma Limit_not_Zero alpha : Is_Limit alpha -> alpha <> Zero.
Proof.
  destruct alpha; unfold Is_Limit, Zero; cbn; intros H H0.
  injection H0;  intro ; subst cnf0; eapply T1.is_limit_not_zero; eauto.
Qed.


Lemma Succ_not_Zero alpha:  Is_Succ alpha -> alpha <> Zero.
Proof.
  destruct alpha;unfold Is_Succ, Zero; cbn.
  intros H H0.
  injection H0; intro;subst; discriminate H.
Qed.

Lemma Lt_Succ : forall alpha, Lt alpha (Succ alpha).
Proof.
  destruct  alpha; unfold lt, Succ. simpl; apply LT_succ;auto.
Qed.


Lemma Succ_not_Is_Limit alpha : Is_Succ alpha -> ~ Is_Limit alpha .
Proof. 
  red; destruct alpha; unfold Is_Succ, Is_Limit; cbn.
  intros H H0. rewrite (succ_not_limit _ H) in H0. discriminate.  
Qed.

Hint Resolve Limit_not_Zero Succ_not_Zero Lt_Succ Succ_not_Is_Limit : E0.

Lemma lt_Succ_inv : forall alpha beta, beta < alpha <->
                                       Succ beta <= alpha.
Proof.
  destruct alpha, beta; unfold lt, le, Succ; cbn; split.
  -  intro; now  apply LT_succ_LE.
  - intro; now apply LT_succ_LE_R.  
Qed.


Lemma le_lt_eq_dec : forall alpha beta, alpha <= beta ->
                                        {alpha < beta} + {alpha = beta}.
Proof.
  destruct alpha, beta.
  unfold Lt, Le; cbn.
  intro H; destruct (LE_LT_eq_dec  H).
  - now left.
  - right; subst; f_equal; apply nf_proof_unicity.
Qed.





(** *** rewriting lemmas *)

Lemma Succ_rw : forall alpha, cnf (Succ alpha) = T1.succ (cnf alpha).
Proof.
  now destruct alpha.
Qed.

Lemma Plus_rw : forall alpha beta, cnf (alpha + beta) =
                                   (cnf alpha + cnf beta)%t1.
Proof.
  now destruct alpha, beta.
Qed.

Lemma phi0_rw : forall alpha, cnf (Phi0 alpha) = phi0 (cnf alpha).
Proof.
  now destruct alpha.
Qed.


Lemma Lt_trans alpha beta gamma :
  alpha < beta -> beta < gamma -> alpha < gamma.
Proof.
  destruct alpha, beta, gamma; simpl. unfold lt.
  simpl.
 intros; eauto with T1.
 eapply T1.LT_trans; eauto.
Qed.


Lemma Omega_term_plus alpha beta i :
  alpha <> Zero -> (beta < Phi0 alpha)%e0 ->
  cnf (Omega_term alpha i + beta)%e0 = ocons (cnf alpha) i (cnf beta).
Proof.
  destruct alpha as [alpha Halpha]; destruct beta as [beta Hbeta].
  intros.
  unfold lt in H0. simpl in H0.
  unfold  Omega_term. unfold cnf.
  unfold plus.
  unfold cnf at 1 2.
  fold (omega_term alpha i ).
  rewrite omega_term_plus_rw.
  reflexivity.
  rewrite nf_LT_iff; tauto.
Qed.


Lemma cnf_Ocons (alpha beta: E0) n : alpha <>Zero -> beta < Phi0 alpha ->
                                          cnf (Ocons alpha n beta) =
                                          ocons (cnf alpha) n (cnf beta).
Proof.
  intros. unfold Ocons. rewrite Omega_term_plus; auto.
Defined.


Lemma Is_Limit_plus alpha beta i:
  (beta < Phi0 alpha)%e0 -> Is_Limit beta ->
  Is_Limit (Omega_term alpha i + beta)%e0.
Proof.
  intros.
  assert (alpha <> Zero). { intro; subst. 
                            apply (Limit_not_Zero H0).
                            destruct beta.
                            red in H. simpl in H.
                            apply LT_one in H. subst.
                            now apply E0_eq_intro.
                          }
                          unfold Is_Limit.
  rewrite   Omega_term_plus; auto.

  simpl. 
  case_eq (cnf alpha).
  intro. 
  destruct H1.
  apply E0_eq_intro.
  apply H2.
  intros.
  unfold Is_Limit in H0;
    destruct (cnf beta).   
  auto.   
  auto.
Qed.


Lemma Succ_cons alpha gamma i : alpha <> Zero -> gamma < Phi0 alpha ->
                                cnf (Succ (Omega_term alpha i + gamma)%e0) =
                                cnf (Omega_term alpha i + Succ gamma)%e0.
Proof.
  intros.
  rewrite Omega_term_plus; auto.
  rewrite Succ_rw.
  rewrite Omega_term_plus; auto.
  rewrite succ_cons, Succ_rw; auto.
  intro H1; apply H, E0_eq_intro.   assumption. 
  destruct H0.
  destruct H1.
  rewrite phi0_rw in H1.
  apply nf_intro; auto.
  now apply lt_phi0_phi0R. 
  red.  
  apply succ_lt_limit.
  rewrite phi0_rw.
  apply nf_phi0. apply cnf_ok.
  rewrite phi0_rw.
  simpl.
  case_eq (cnf alpha).
  intro.
  destruct H.
  apply E0_eq_intro. assumption.
  intros; trivial. 
  now red.   
  assumption.
Qed.


Instance Oplus (alpha beta : E0) : E0.
Proof.
  refine (@mkord (oplus (cnf alpha) (cnf beta) )_).
  apply oplus_nf; apply cnf_ok.
Defined.

Infix "O+" := Oplus (at level 50, left associativity): E0_scope.

Lemma Oplus_assoc (alpha beta gamma : E0) :
   (alpha O+ (beta O+ gamma) =  alpha O+ beta O+ gamma)%e0.
Proof.
  destruct alpha, beta, gamma. unfold Oplus.  cbn.
  apply E0_eq_intro. cbn. now   rewrite oplus_assoc.
Qed.



Lemma oPlus_rw (alpha beta : E0) :
  cnf (alpha O+ beta)%e0 = (cnf alpha o+ cnf beta)%t1.
Proof.
  now destruct alpha, beta.
Qed.

