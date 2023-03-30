(******************************************************************************)
From Coq Require Import Wf_nat Arith Lists.List Peano_dec. 

Require Import ListExt. (* todo: use stdlib? *)
Require Export fol.

Section Fol_Properties.

Variable L : Language.

Notation Formula := (Formula L) (only parsing).
Notation Formulas := (Formulas L) (only parsing).
Notation System := (System L) (only parsing).
Notation Term := (Term L) (only parsing).
Notation Terms := (Terms L) (only parsing).
  
Let lt_depth := lt_depth L.

Section Free_Variables.

Fixpoint freeVarTerm (s : fol.Term L) : list nat :=
  match s with
  | var v => v :: nil
  | apply f ts => freeVarTerms (arityF L f) ts
  end
with freeVarTerms (n : nat) (ss : fol.Terms L n) {struct ss} : list nat :=
       match ss with
       | Tnil => nil (A:=nat)
       | Tcons m t ts => freeVarTerm t ++ freeVarTerms m ts
       end.

Lemma freeVarTermApply :
  forall (f : Functions L) (ts : fol.Terms L _),
    freeVarTerm (apply f ts) = freeVarTerms _ ts.
Proof. reflexivity. Qed.

Fixpoint freeVarFormula (A : fol.Formula L) : list nat :=
  match A with
  | equal t s => freeVarTerm t ++ freeVarTerm s
  | atomic r ts => freeVarTerms _ ts
  | impH A B => freeVarFormula A ++ freeVarFormula B
  | notH A => freeVarFormula A
  | forallH v A => List.remove  eq_nat_dec v (freeVarFormula A)
  end.

Definition ClosedSystem (T : fol.System L) :=
  forall (v : nat) (f : fol.Formula L),
    mem _ T f -> ~ In v (freeVarFormula f).

Fixpoint closeList (l: list nat)(a : fol.Formula L) :=
 match l with
   nil => a
|  cons v l =>  (forallH v (closeList l a))
end.

(* Todo : use stdlib's nodup *)

Definition close (x : fol.Formula L) : fol.Formula L :=
  closeList (List.nodup eq_nat_dec (freeVarFormula x)) x.

Lemma freeVarClosedList1 :
  forall (l : list nat) (v : nat) (x : fol.Formula L),
    In v l -> ~ In v (freeVarFormula (closeList l x)).
Proof.
  intro l; induction l as [| a l Hrecl].
  - intros v x H; elim H.
  - intros v x H; induction H as [H| H].
    + simpl in |- *; rewrite H.
      unfold not in |- *; intros H0;
        elim (in_remove_neq _ _ _ _ _ H0); reflexivity.
    + simpl in |- *.  intro H0. 
      assert (H1: In v (freeVarFormula (closeList l x))).
      { eapply in_remove.   apply H0. }
      apply (Hrecl _ _ H H1).
Qed.

Lemma freeVarClosedList2 :
  forall (l : list nat) (v : nat) (x : fol.Formula L),
    In v (freeVarFormula (closeList l x)) ->
    In v (freeVarFormula x).
Proof.
  intro l; induction l as [| a l Hrecl].
  - simpl; intros v x H; apply H.
  - simpl; intros v x H; apply Hrecl; eapply in_remove;  apply H.
Qed.

Lemma freeVarClosed :
  forall (x : fol.Formula L) (v : nat), ~ In v (freeVarFormula (close x)).
Proof.
  intros x v; unfold close;
  destruct (In_dec eq_nat_dec v (List.nodup eq_nat_dec (freeVarFormula x)))
    as [i | n]. 
  - apply freeVarClosedList1; assumption.
  - intro H; elim n. rewrite nodup_In.  
    eapply freeVarClosedList2; apply H.
Qed.

Fixpoint freeVarListFormula (l : fol.Formulas L) : list nat :=
  match l with
  | nil => nil (A:=nat)
  | f :: l => freeVarFormula f ++ freeVarListFormula l
  end.

Lemma freeVarListFormulaApp :
  forall a b : fol.Formulas L,
    freeVarListFormula (a ++ b) =
      freeVarListFormula a ++ freeVarListFormula b.
Proof.
  intros a b; induction a as [| a a0 Hreca].
  - reflexivity.
  - simpl in |- *; rewrite Hreca; now rewrite List.app_assoc. 
Qed.

Lemma In_freeVarListFormula :
  forall (v : nat) (f : fol.Formula L) (F : fol.Formulas L),
    In v (freeVarFormula f) -> In f F -> In v (freeVarListFormula F).
Proof.
  intros v f F H H0; induction F as [| a F HrecF].
  - elim H0.
  - destruct H0 as [H0| H0]; simpl in |- *.
    + apply in_or_app; left; now rewrite H0.
    + apply in_or_app; auto.
Qed.

Lemma In_freeVarListFormulaE :
  forall (v : nat) (F : fol.Formulas L),
    In v (freeVarListFormula F) ->
    exists f : fol.Formula L, In v (freeVarFormula f) /\ In f F.
Proof.
  intros v F H; induction F as [| a F HrecF].
  - destruct H.
  - destruct (in_app_or _ _ _ H) as [H0 | H0].
    + exists a; simpl in |- *; auto.
    + destruct (HrecF H0) as [x Hx]; exists x; cbn; tauto.
Qed.

Definition In_freeVarSys (v : nat) (T : fol.System L) :=
  exists f : fol.Formula L, List.In v (freeVarFormula f) /\ mem _ T f.

Lemma notInFreeVarSys :
  forall x, ~ In_freeVarSys x (Ensembles.Empty_set (fol.Formula L)).
Proof.
  intros x; unfold In_freeVarSys in |- *.
  intros [? [? H0]]; destruct H0. 
Qed.

End Free_Variables.

Section Substitution.

Fixpoint substituteTerm (s : fol.Term L) (x : nat) 
  (t : fol.Term L) {struct s} : fol.Term L :=
  match s with
  | var v =>
      match eq_nat_dec x v with
      | left _ => t
      | right _ => var v
      end
  | apply f ts => apply f (substituteTerms _ ts x t)
  end
with substituteTerms (n : nat) (ss : fol.Terms L n) 
       (x : nat) (t : fol.Term L) {struct ss} : fol.Terms L n :=
       match ss in (fol.Terms _ n0) return (fol.Terms L n0) with
       | Tnil => Tnil
       | Tcons m s ts =>
           Tcons  (substituteTerm s x t) 
             (substituteTerms m ts x t)
       end.

Lemma subTermVar1 :
  forall (v : nat) (s : fol.Term L), substituteTerm (var v) v s = s.
Proof.
  intros v s;  unfold substituteTerm in |- *.
  destruct  (eq_nat_dec v v) as [e | b].
  - reflexivity.
  - now destruct b.
Qed.

Lemma subTermVar2 :
  forall (v x : nat) (s : fol.Term L),
    v <> x -> substituteTerm (var x) v s = var x.
Proof.
  intros v x s H; unfold substituteTerm in |- *.
  destruct (eq_nat_dec v x).
  - contradiction. 
  - reflexivity.
Qed.

Lemma subTermFunction :
  forall (f : Functions L) (ts : fol.Terms L (arityF L f)) 
         (v : nat) (s : fol.Term L),
    substituteTerm (apply f ts) v s = apply f (substituteTerms _ ts v s).
Proof. reflexivity. Qed.

Definition newVar (l : list nat) : nat := fold_right Nat.max 0 (map S l).

Lemma newVar2 : forall (l : list nat) (n : nat), In n l -> n < newVar l.
Proof.
  induction l as [| a l Hrecl].
  - destruct 1.
  - destruct 1 as [H| H].
    + rewrite H; unfold newVar in |- *; simpl in |- *.
      induction (fold_right Nat.max 0 (map S l)).
      * apply Nat.lt_succ_diag_r .
      * apply Nat.lt_succ_r;  apply Nat.le_max_l.
    + unfold newVar in Hrecl |- *; simpl. 
      assert
        (H0: fold_right Nat.max 0 (map S l) = 0 \/
               (exists n : nat, fold_right Nat.max 0 (map S l) = S n)).
      { induction (fold_right Nat.max 0 (map S l)) as [| n0 IHn0].
        - auto.
        - right; now exists n0.
      }
      destruct H0 as [H0| [x0 H0]].
      * rewrite H0; rewrite H0 in Hrecl.
        elim (Nat.nlt_0_r n (Hrecl _ H)).
      * rewrite H0; rewrite H0 in Hrecl.
        -- apply Nat.lt_le_trans with (S x0).
           ++ now apply Hrecl.
           ++ apply le_n_S, Nat.le_max_r.
Qed.

Lemma newVar1 : forall l : list nat, ~ In (newVar l) l.
Proof.
  intros l ?; elim (Nat.lt_irrefl (newVar l)); now apply newVar2.
Qed.

Definition substituteFormulaImp (f : fol.Formula L)
  (frec : nat * fol.Term L -> {y : fol.Formula L | depth L y = depth L f})
  (g : fol.Formula L)
  (grec : nat * fol.Term L -> {y : fol.Formula L | depth L y = depth L g})
  (p : nat * fol.Term L) :
  {y : fol.Formula L | depth L y = depth L (impH f g)} :=
  match frec p with
  | exist f' prf1 =>
      match grec p with
      | exist g' prf2 =>
          exist
            (fun y : fol.Formula L =>
               depth L y = S (Nat.max (depth L f) (depth L g))) 
            (impH f' g')
            (eq_ind_r
               (fun n : nat =>
                  S (Nat.max n (depth L g')) =
                    S (Nat.max (depth L f) (depth L g)))
               (eq_ind_r
                  (fun n : nat =>
                     S (Nat.max (depth L f) n) =
                       S (Nat.max (depth L f) (depth L g)))
                  (refl_equal (S (Nat.max  (depth L f) (depth L g))))
                  prf2) prf1)
      end
  end.

Remark substituteFormulaImpNice :
  forall (f g : fol.Formula L)
         (z1 z2 : nat * fol.Term L ->
                  {y : fol.Formula L | depth L y = depth L f}),
    (forall q : nat * fol.Term L, z1 q = z2 q) ->
    forall
      z3 z4 : nat * fol.Term L ->
              {y : fol.Formula L | depth L y = depth L g},
      (forall q : nat * fol.Term L, z3 q = z4 q) ->
      forall q : nat * fol.Term L,
        substituteFormulaImp f z1 g z3 q =
          substituteFormulaImp f z2 g z4 q.
Proof.
  intros f g z1 z2 H z3 z4 H0 q; unfold substituteFormulaImp in |- *.
  rewrite H, H0; reflexivity. 
Qed.

Definition substituteFormulaNot (f : fol.Formula L)
  (frec : nat * fol.Term L ->
          {y : fol.Formula L | depth L y = depth L f})
  (p : nat * fol.Term L) :
  {y : fol.Formula L | depth L y = depth L (notH f)} :=
  match frec p with
  | exist f' prf1 =>
      exist (fun y : fol.Formula L => depth L y = S (depth L f)) 
        (notH f')
        (eq_ind_r (fun n : nat => S n = S (depth L f))
           (refl_equal (S (depth L f))) prf1)
  end.

Remark substituteFormulaNotNice :
  forall (f : fol.Formula L)
         (z1 z2 : nat * fol.Term L ->
                  {y : fol.Formula L | depth L y = depth L f}),
    (forall q : nat * fol.Term L, z1 q = z2 q) ->
    forall q : nat * fol.Term L,
      substituteFormulaNot f z1 q = substituteFormulaNot f z2 q.
Proof.
  intros ? ? ? H ?; unfold substituteFormulaNot in |- *;
    now rewrite H.
Qed.
    
Definition substituteFormulaForall (n : nat) (f : fol.Formula L)
  (frec : forall b : fol.Formula L,
      lt_depth b (forallH n f) ->
      nat * fol.Term L -> {y : fol.Formula L | depth L y = depth L b})
  (p : nat * fol.Term L) :
  {y : fol.Formula L | depth L y = depth L (forallH n f)} :=
  match p with
  | (v, s) =>
      match eq_nat_dec n v with
      | left _ =>
          exist (fun y : fol.Formula L => depth L y = S (depth L f))
            (forallH n f) (refl_equal (depth L (forallH n f)))
      | right _ =>
          match In_dec eq_nat_dec n (freeVarTerm s) with
          | left _ =>
              let nv := newVar (v :: freeVarTerm s ++ freeVarFormula f) in
              match frec f (depthForall L f n) (n, var nv) with
              | exist f' prf1 =>
                  match
                    frec f'
                      (eqDepth L f' f (forallH n f) 
                         (sym_eq prf1) (depthForall L f n)) p
                  with
                  | exist f'' prf2 =>
                      exist
                        (fun y : fol.Formula L => depth L y = S (depth L f))
                        (forallH nv f'')
                        (eq_ind_r (fun n : nat => S n = S (depth L f))
                           (refl_equal (S (depth L f))) 
                           (trans_eq prf2 prf1))
                  end
              end
          | right _ =>
              match frec f (depthForall L f n) p with
              | exist f' prf1 =>
                  exist (fun y : fol.Formula L => depth L y = S (depth L f))
                    (forallH n f')
                    (eq_ind_r (fun n : nat => S n = S (depth L f))
                       (refl_equal (S (depth L f))) prf1)
              end
          end
      end
  end.

Remark substituteFormulaForallNice :
  forall (v : nat) (a : fol.Formula L)
         (z1 z2 : forall b : fol.Formula L,
             lt_depth b (forallH v a) ->
             nat * fol.Term L -> {y : fol.Formula L | depth L y = depth L b}),
    (forall (b : fol.Formula L) (q : lt_depth b (forallH v a))
            (r : nat * fol.Term L), z1 b q r = z2 b q r) ->
    forall q : nat * fol.Term L,
      substituteFormulaForall v a z1 q = substituteFormulaForall v a z2 q.
Proof.
  intros v a z1 z2 H [a0 b]; unfold substituteFormulaForall in |- *.
  destruct (eq_nat_dec v a0) as [e | n] ; simpl in |- *.
  - reflexivity.
  - induction (In_dec eq_nat_dec v (freeVarTerm b)); simpl in |- *.
    + rewrite H;
        destruct
          (z2 a (depthForall L a v)
             (v, var (newVar
                        (a0 :: freeVarTerm b ++ freeVarFormula a)))). 
         now rewrite H.  
    + now rewrite H.
Qed.

Definition substituteFormulaHelp (f : fol.Formula L) 
  (v : nat) (s : fol.Term L) : {y : fol.Formula L | depth L y = depth L f}.
Proof.
  apply
    (Formula_depth_rec2 L
       (fun f : fol.Formula L =>
          nat * fol.Term L -> {y : fol.Formula L | depth L y = depth L f})).
  - intros t t0 H; induction H as (a, b).
    exists (equal (substituteTerm t a b) (substituteTerm t0 a b)); auto.
  - intros r t H; induction H as (a, b).
    exists (atomic r (substituteTerms _ t a b)); auto.
  - exact substituteFormulaImp.
  - exact substituteFormulaNot.
  - exact substituteFormulaForall.
  - exact (v, s).
Defined.

Definition substituteFormula (f : fol.Formula L) (v : nat) (s : fol.Term L) :
  fol.Formula L := proj1_sig (substituteFormulaHelp f v s).

Lemma subFormulaEqual :
  forall (t1 t2 : fol.Term L) (v : nat) (s : fol.Term L),
    substituteFormula (equal t1 t2) v s =
      equal (substituteTerm t1 v s) (substituteTerm t2 v s).
Proof. reflexivity. Qed.

Lemma subFormulaRelation :
  forall (r : Relations L) (ts : fol.Terms L (arityR L r)) 
         (v : nat) (s : fol.Term L),
    substituteFormula (atomic r ts) v s =
      atomic r (substituteTerms (arityR L r) ts v s).
Proof. reflexivity. Qed.


Lemma subFormulaImp :
  forall (f1 f2 : fol.Formula L) (v : nat) (s : fol.Term L),
    substituteFormula (impH f1 f2) v s =
      impH (substituteFormula f1 v s) (substituteFormula f2 v s).
Proof.
  intros f1 f2 v s. 
  unfold substituteFormula, substituteFormulaHelp in |- *.
  rewrite
    (Formula_depth_rec2_imp L)
    with
    (Q := 
       fun _ : fol.Formula L =>
         (nat * fol.Term L)%type)
    (P := 
       fun x : fol.Formula L =>
         {y : fol.Formula L | depth L y = depth L x}).
  unfold substituteFormulaImp at 1 in |- *.
  - induction
      (Formula_depth_rec2 L
         (fun x : fol.Formula L =>
            nat * fol.Term L -> {y : fol.Formula L | depth L y = depth L x})
         (fun (t t0 : fol.Term L) (H : nat * fol.Term L) =>
            prod_rec
              (fun _ : nat * fol.Term L =>
                 {y : fol.Formula L | depth L y = depth L (equal  t t0)})
              (fun (a : nat) (b : fol.Term L) =>
                 exist
                   (fun y : fol.Formula L => 
                      depth L y = depth L (equal t t0))
                   (equal (substituteTerm t a b) (substituteTerm t0 a b))
                   (refl_equal (depth L (equal t t0)))) H)
         (fun (r : Relations L) 
              (t : fol.Terms L (arityR L r))
              (H : nat * fol.Term L) =>
            prod_rec
              (fun _ : nat * fol.Term L =>
                 {y : fol.Formula L | depth L y = depth L (atomic r t)})
              (fun (a : nat) (b : fol.Term L) =>
                 exist
                   (fun y : fol.Formula L => depth L y = 
                                               depth L (atomic r t))
                   (atomic r (substituteTerms (arityR L r) 
                                t a b))
                   (refl_equal (depth L (atomic r t)))) H)
         substituteFormulaImp
         substituteFormulaNot substituteFormulaForall f1 
         (v, s)).
    induction
      (Formula_depth_rec2 L
         (fun x0 : fol.Formula L =>
            nat * fol.Term L -> {y : fol.Formula L | depth L y = depth L x0})
         (fun (t t0 : fol.Term L) (H : nat * fol.Term L) =>
            prod_rec
              (fun _ : nat * fol.Term L =>
                 {y : fol.Formula L | depth L y = depth L (equal t t0)})
              (fun (a : nat) (b : fol.Term L) =>
                 exist
                   (fun y : fol.Formula L => 
                      depth L y = depth L (equal t t0))
                   (equal (substituteTerm t a b) (substituteTerm t0 a b))
                   (refl_equal (depth L (equal t t0)))) H)
         (fun (r : Relations L) 
              (t : fol.Terms L (arityR L r))
              (H : nat * fol.Term L) =>
            prod_rec
              (fun _ : nat * fol.Term L =>
                 {y : fol.Formula L | depth L y = depth L (atomic r t)})
              (fun (a : nat) (b : fol.Term L) =>
                 exist
                   (fun y : fol.Formula L => 
                      depth L y = depth L (atomic r t))
                   (atomic r (substituteTerms (arityR L r) 
                                t a b))
                   (refl_equal (depth L (atomic r t)))) H) 
         substituteFormulaImp
         substituteFormulaNot substituteFormulaForall f2 
         (v, s)).
    reflexivity.
  - apply substituteFormulaImpNice.
  - apply substituteFormulaNotNice.
  - apply substituteFormulaForallNice.
Qed.

Lemma subFormulaNot :
  forall (f : fol.Formula L) (v : nat) (s : fol.Term L),
    substituteFormula (notH f) v s = notH (substituteFormula f v s).
Proof.
  intros f v s; 
  unfold substituteFormula, substituteFormulaHelp.
  rewrite (Formula_depth_rec2_not L) with
    (Q := fun _ : fol.Formula L => (nat * fol.Term L)%type)
    (P := fun x : fol.Formula L =>
         {y : fol.Formula L | depth L y = depth L x}).
  - unfold substituteFormulaNot at 1 in |- *.
    induction
      (Formula_depth_rec2 L
         (fun x : fol.Formula L =>
            nat * fol.Term L -> {y : fol.Formula L | depth L y = depth L x})
         (fun (t t0 : fol.Term L) (H : nat * fol.Term L) =>
            prod_rec
              (fun _ : nat * fol.Term L =>
                 {y : fol.Formula L | depth L y = depth L (equal t t0)})
              (fun (a : nat) (b : fol.Term L) =>
                 exist
                   (fun y : fol.Formula L => depth L y = 
                                               depth L (equal t t0))
                   (equal (substituteTerm t a b) (substituteTerm t0 a b))
                   (refl_equal (depth L (equal t t0)))) H)
         (fun (r : Relations L) 
              (t : fol.Terms L (arityR L r))
              (H : nat * fol.Term L) =>
            prod_rec
              (fun _ : nat * fol.Term L =>
                 {y : fol.Formula L | depth L y = depth L (atomic r t)})
              (fun (a : nat) (b : fol.Term L) =>
                 exist
                   (fun y : fol.Formula L =>
                      depth L y = depth L (atomic r t))
                   (atomic r
                      (substituteTerms (arityR L r) t a b))
                   (refl_equal (depth L (atomic r t)))) H)
         substituteFormulaImp
         substituteFormulaNot substituteFormulaForall f 
         (v, s)); reflexivity.
  - apply substituteFormulaImpNice.
  - apply substituteFormulaNotNice.
  - apply substituteFormulaForallNice.
Qed.
    

Lemma subFormulaForall :
  forall (f : fol.Formula L) (x v : nat) (s : fol.Term L),
    let nv := newVar (v :: freeVarTerm s ++ freeVarFormula f) in
    substituteFormula (forallH x f) v s =
      match eq_nat_dec x v with
      | left _ => forallH x f
      | right _ =>
          match In_dec eq_nat_dec x (freeVarTerm s) with
          | right _ => forallH x (substituteFormula f v s)
          | left _ =>
              forallH nv (substituteFormula 
                            (substituteFormula f x (var nv)) v s)
          end
      end.
Proof.
  intros f x v s nv.
  unfold substituteFormula at 1 in |- *.
  unfold substituteFormulaHelp in |- *.
  rewrite (Formula_depth_rec2_forall L)
    with
    (Q := 
       fun _ : fol.Formula L =>
         (nat * fol.Term L)%type)
    (P := 
       fun x : fol.Formula L =>
         {y : fol.Formula L | depth L y = depth L x}).
  - simpl in |- *; induction (eq_nat_dec x v); simpl in |- *.
    + reflexivity.
    + induction (In_dec eq_nat_dec x (freeVarTerm s)); simpl in |- *.
      fold nv in |- *.
      unfold substituteFormula at 2 in |- *; 
        unfold substituteFormulaHelp in |- *;
        simpl in |- *.
      * induction
          (Formula_depth_rec2 L
             (fun x0 : fol.Formula L =>
                nat * fol.Term L -> 
                {y : fol.Formula L | depth L y = depth L x0})
             (fun (t t0 : fol.Term L) (H : nat * fol.Term L) =>
                prod_rec
                  (fun _ : nat * fol.Term L => 
                     {y : fol.Formula L | depth L y = 0})
                  (fun (a0 : nat) (b0 : fol.Term L) =>
                     exist (fun y : fol.Formula L => depth L y = 0)
                       (equal (substituteTerm t a0 b0) 
                          (substituteTerm t0 a0 b0))
                       (refl_equal 0)) H)
             (fun (r : Relations L) 
                  (t : fol.Terms L (arityR L r))
                  (H : nat * fol.Term L) =>
                prod_rec
                  (fun _ : nat * fol.Term L => 
                     {y : fol.Formula L | depth L y = 0})
                  (fun (a0 : nat) (b0 : fol.Term L) =>
                     exist (fun y : fol.Formula L => depth L y = 0)
                       (atomic r (substituteTerms
                                    (arityR L r) t a0 b0))
                       (refl_equal 0)) H) substituteFormulaImp
             substituteFormulaNot
             substituteFormulaForall f (x, var nv)).
        unfold substituteFormula in |- *; unfold substituteFormulaHelp in |- *;
          simpl in |- *.
        induction
          (Formula_depth_rec2 L
             (fun x1 : fol.Formula L =>
                nat * fol.Term L -> 
                {y : fol.Formula L | depth L y = depth L x1})
             (fun (t t0 : fol.Term L) (H : nat * fol.Term L) =>
                prod_rec
                  (fun _ : nat * fol.Term L => 
                     {y : fol.Formula L | depth L y = 0})
                  (fun (a0 : nat) (b0 : fol.Term L) =>
                     exist (fun y : fol.Formula L => depth L y = 0)
                       (equal (substituteTerm t a0 b0) 
                          (substituteTerm t0 a0 b0))
                       (refl_equal 0)) H)
             (fun (r : Relations L) 
                  (t : fol.Terms L (arityR L r))
                  (H : nat * fol.Term L) =>
                prod_rec
                  (fun _ : nat * fol.Term L => 
                     {y : fol.Formula L | depth L y = 0})
                  (fun (a0 : nat) (b0 : fol.Term L) =>
                     exist (fun y : fol.Formula L => depth L y = 0)
                       (atomic r (substituteTerms 
                                    (arityR L r) t a0 b0))
                       (refl_equal 0)) H) substituteFormulaImp 
             substituteFormulaNot
             substituteFormulaForall x0 (v, s)).
        simpl in |- *; reflexivity.
      * unfold substituteFormula in |- *; unfold substituteFormulaHelp in |- *;
          simpl in |- *.
        induction
          (Formula_depth_rec2 L
             (fun x0 : fol.Formula L =>
                nat * fol.Term L -> 
                {y : fol.Formula L | depth L y = depth L x0})
             (fun (t t0 : fol.Term L) (H : nat * fol.Term L) =>
                prod_rec
                  (fun _ : nat * fol.Term L => 
                     {y : fol.Formula L | depth L y = 0})
                  (fun (a : nat) (b1 : fol.Term L) =>
                     exist (fun y : fol.Formula L => depth L y = 0)
                       (equal (substituteTerm t a b1) (substituteTerm t0 a b1))
                       (refl_equal 0)) H)
             (fun (r : Relations L) 
                  (t : fol.Terms L (arityR L r))
                  (H : nat * fol.Term L) =>
                prod_rec
                  (fun _ : nat * fol.Term L => 
                     {y : fol.Formula L | depth L y = 0})
                  (fun (a : nat) (b1 : fol.Term L) =>
                     exist (fun y : fol.Formula L => depth L y = 0)
                       (atomic r (substituteTerms
                                    (arityR L r) t a b1))
                       (refl_equal 0)) H) substituteFormulaImp
             substituteFormulaNot
             substituteFormulaForall f (v, s)).
        simpl in |- *; reflexivity.
  - apply substituteFormulaImpNice.
  - apply substituteFormulaNotNice.
  - apply substituteFormulaForallNice.
Qed.

Section Extensions.


Lemma subFormulaOr :
  forall (f1 f2 : fol.Formula L) (v : nat) (s : fol.Term L),
    substituteFormula (orH f1 f2) v s =
      orH (substituteFormula f1 v s) (substituteFormula f2 v s).
Proof.
  intros f1 f2 v s; unfold orH;
    now rewrite subFormulaImp, subFormulaNot.
Qed.

Lemma subFormulaAnd :
  forall (f1 f2 : fol.Formula L) (v : nat) (s : fol.Term L),
    substituteFormula (andH f1 f2) v s =
      andH (substituteFormula f1 v s) (substituteFormula f2 v s).
Proof.
  intros ? ? ? ?; unfold andH in |- *.
  rewrite subFormulaNot, subFormulaOr; now repeat rewrite subFormulaNot.
Qed.

Lemma subFormulaExist :
  forall (f : fol.Formula L) (x v : nat) (s : fol.Term L),
    let nv := newVar (v :: freeVarTerm s ++ freeVarFormula f) in
    substituteFormula (existH x f) v s =
      match eq_nat_dec x v with
      | left _ => existH x f
      | right _ =>
          match In_dec eq_nat_dec x (freeVarTerm s) with
          | right _ => existH x (substituteFormula f v s)
          | left _ =>
              existH nv (substituteFormula 
                           (substituteFormula f x (var nv)) v s)
          end
      end.
Proof.
  intros ? ? ? ? nv; unfold existH.
  rewrite subFormulaNot, subFormulaForall.
  destruct (eq_nat_dec x v).
  - reflexivity.
  - induction (In_dec eq_nat_dec x (freeVarTerm s));
      now repeat rewrite subFormulaNot.
Qed.

Lemma subFormulaIff :
  forall (f1 f2 : fol.Formula L) (v : nat) (s : fol.Term L),
    substituteFormula (iffH f1 f2) v s =
      iffH (substituteFormula f1 v s) (substituteFormula f2 v s).
Proof.
  intros ? ? v s; unfold iffH in |- *.
  rewrite subFormulaAnd; now repeat rewrite subFormulaImp.
Qed.

Lemma subFormulaIfThenElse :
  forall (f1 f2 f3 : fol.Formula L) (v : nat) (s : fol.Term L),
    substituteFormula (ifThenElseH f1 f2 f3) v s =
      ifThenElseH (substituteFormula f1 v s) (substituteFormula f2 v s)
        (substituteFormula f3 v s).
Proof.
  intros ? ? ? ? ?; unfold ifThenElseH.
  now rewrite subFormulaAnd, !subFormulaImp,  subFormulaNot.
Qed.

End Extensions.

Lemma subFormulaDepth :
  forall (f : fol.Formula L) (v : nat) (s : fol.Term L),
    depth L (substituteFormula f v s) = depth L f.
Proof.
  intros f v s; unfold substituteFormula in |- *.
  induction (substituteFormulaHelp f v s) as [x p]; now simpl. 
Qed.

Section Substitution_Properties.

Lemma subTermId :
  forall (t : fol.Term L) (v : nat), substituteTerm t v (var v) = t.
Proof.
  intros ? ?; 
    elim t using Term_Terms_ind
    with
    (P0 := fun (n : nat) (ts : fol.Terms L n) =>
             substituteTerms n ts v (var v) = ts).
  - simpl in |- *; intros n.
    induction (eq_nat_dec v n) as [a | b].
    + now rewrite a.
    + reflexivity.
  -  intros f t0 H; simpl in |- *; now rewrite H.
  -  reflexivity.
  -  intros ? ? H t1 H0; simpl in |- *; now rewrite H, H0. 
Qed.

Lemma subTermsId :
  forall (n : nat) (ts : fol.Terms L n) (v : nat),
    substituteTerms n ts v (var v) = ts.
Proof.
  intros n ts v; induction ts as [| n t ts Hrects].
  - reflexivity. 
  - simpl in |- *;  now rewrite Hrects,  subTermId.
Qed.

Lemma subFormulaId :
  forall (f : fol.Formula L) (v : nat), substituteFormula f v (var v) = f.
Proof.
  intros f v.
  induction f as [t t0| r t| f1 Hrecf1 f0 Hrecf0| f Hrecf| n f Hrecf].
  - now rewrite subFormulaEqual, !subTermId.
  - now rewrite subFormulaRelation, subTermsId.
  - now rewrite subFormulaImp, Hrecf1,  Hrecf0.
  - now rewrite subFormulaNot, Hrecf.
  - rewrite subFormulaForall; destruct  (eq_nat_dec n v) as [e|ne].
    + reflexivity.
    + induction (In_dec eq_nat_dec n (freeVarTerm (var v))) as [a|b].
      * elim ne; destruct a as [H| H].
        -- now subst.
        -- destruct H.
      * now rewrite Hrecf.
Qed.

Lemma subFormulaForall2 :
  forall (f : fol.Formula L) (x v : nat) (s : fol.Term L),
  exists nv : nat,
    ~ In nv (freeVarTerm s) /\
      nv <> v /\
      ~ In nv (List.remove  eq_nat_dec x (freeVarFormula f)) /\
      substituteFormula (forallH x f) v s =
        match eq_nat_dec x v with
        | left _ => forallH x f
        | right _ =>
            forallH nv (substituteFormula (substituteFormula f x (var nv)) v s)
        end.
Proof.
  intros f x v s; rewrite subFormulaForall.
  induction (eq_nat_dec x v) as [a | b].
  - set
      (A1 :=
         v :: freeVarTerm s ++ List.remove eq_nat_dec x (freeVarFormula f)) 
      in *.
    exists (newVar A1); repeat split.
    + unfold not in |- *; intros; elim (newVar1 A1).
      unfold A1 in |- *; right.
      apply in_or_app; auto.
    + unfold not in |- *; intros; elim (newVar1 A1).
      rewrite H; left; auto.
    + unfold not in |- *; intros; elim (newVar1 A1).
      right; apply in_or_app; auto.
  - induction (In_dec eq_nat_dec x (freeVarTerm s)) as [a | b0].
    + set (A1 := v :: freeVarTerm s ++ freeVarFormula f) in *.
      exists (newVar A1); repeat split.
      * unfold not in |- *; intros; elim (newVar1 A1); right.
        apply in_or_app; auto.
      * unfold not in |- *; intros; elim (newVar1 A1); rewrite H; left; auto.
      * unfold not in |- *; intros; elim (newVar1 A1); right;  apply in_or_app.
        right; eapply in_remove; apply H.
    + exists x; repeat split; auto.
      intro H; eapply (in_remove_neq _ _ _ _ _ H).
      * reflexivity.
      * now rewrite subFormulaId.
Qed.


Lemma subFormulaExist2 :
  forall (f : fol.Formula L) (x v : nat) (s : fol.Term L),
  exists nv : nat,
    ~ In nv (freeVarTerm s) /\
      nv <> v /\
      ~ In nv (List.remove eq_nat_dec x (freeVarFormula f)) /\
      substituteFormula (existH x f) v s =
        match eq_nat_dec x v with
        | left _ => existH x f
        | right _ =>
            existH nv (substituteFormula (substituteFormula f x (var nv)) v s)
        end.
Proof.
  intros f x v s; rewrite subFormulaExist.
  induction (eq_nat_dec x v) as [a | b].
  - set
      (A1 :=
         v :: freeVarTerm s ++ List.remove eq_nat_dec x (freeVarFormula f)) 
      in *.
    exists (newVar A1); repeat split.
    + unfold not in |- *; intros; elim (newVar1 A1).
      unfold A1 in |- *; right; apply in_or_app; auto.
    + unfold not in |- *; intros; elim (newVar1 A1); rewrite H; now left.
    + unfold not in |- *; intros; elim (newVar1 A1); right; apply in_or_app; 
        auto.
  - induction (In_dec eq_nat_dec x (freeVarTerm s)) as [a | b0].
    + set (A1 := v :: freeVarTerm s ++ freeVarFormula f) in *.
      exists (newVar A1);  repeat split.
      * unfold not in |- *; intros; elim (newVar1 A1); right; apply in_or_app; auto.
      * unfold not in |- *; intros; elim (newVar1 A1); rewrite H; left; auto.
      * unfold not in |- *; intros; elim (newVar1 A1); right;  apply in_or_app.
        right; eapply in_remove; apply H.
    + exists x; repeat split; auto.
      intros H; eapply (in_remove_neq _ _ _ _ _ H).
      * reflexivity.
      * rewrite subFormulaId; auto.
Qed.

End Substitution_Properties.

End Substitution.
  
Definition Sentence (f:Formula) := (forall v : nat, ~ In v (freeVarFormula f)).

End Fol_Properties.



