(**  LNN.v : Language of Natural Numbers ([LNT]+ [<]) 


Original version by Russel O'Connor

*)


From Coq Require Import Arith Ensembles List.

Require Export Languages folProof  folProp  folLogic3.
From LibHyps Require Import LibHyps. 
Require Import MoreLibHyps NewNotations.

(** * Instantiations of a few generic constructs 

  _To do_ perhaps these redefinitions should be deprecated, because they cause some issues 
  in statements which mix [LNN] and [LNT] terms and formulas 
*)

(* begin snippet Instantiations *)
Definition Formula := Formula LNN.
Definition Formulas := Formulas LNN.
Definition System := System LNN.
Definition Sentence := Sentence LNN.
Definition Term := Term LNN.
Definition Terms := Terms LNN.
Definition SysPrf := SysPrf LNN.

#[local] Arguments apply _ _ _ : clear implicits.
#[local] Arguments atomic _ _ _ : clear implicits.

Definition Plus (x y : Term) : Term :=
  apply LNN Plus_ (Tcons x (Tcons y (Tnil))).

Definition Times (x y : Term) : Term :=
  apply LNN Times_ (Tcons x (Tcons y (Tnil))).

Definition Succ (x : Term) : Term :=
  apply LNN Succ_ (Tcons x (Tnil)).


Definition Zero : Term := apply LNN Zero_ (Tnil).

Definition LT (x y : Term) : Formula :=
  atomic LNN LT_ (Tcons x (Tcons y (Tnil))). 
(* end snippet Instantiations *)

(** * Notations (Experimental and unstable)  *)

Module NNnotations. 

Declare Scope nn_scope.
Delimit Scope nn_scope with nn. 


Infix "=" := (equal _): nn_scope.
Infix "\/" := (orH): nn_scope.
Infix "/\" := (andH):nn_scope.
Infix "->" := (impH): nn_scope.
Notation "~ A" := (@notH _ A): nn_scope. 
Notation "A <-> B" := (@iffH _ A B): nn_scope.

Notation "t = u" := (@equal _ t u): nn_scope.
Notation "t <> u" := (~ t = u)%nn : nn_scope.

Reserved Notation "x '\/'' y" (at level 85, right associativity).
Reserved Notation "x '/\'' y" (at level 80, right associativity).
Reserved Notation "x '<->'' y" (at level 95, no associativity).
Reserved Notation "x '<->''' y" (at level 95, no associativity).



Notation "x \/' y" := (~ x -> y)%nn : nn_scope. 
Notation "x /\' y" := (~ (~ x \/'  ~ y))%nn : nn_scope.
Notation "x <->'' y" := ((x -> y) /\ (y -> x))%nn:  nn_scope.
Notation "x <->' y" := (~ (~ (x -> y) \/' ~(y -> x)))%nn : nn_scope.

Notation "'v#' i" := (var i) (at level 3, format "'v#' i") : nn_scope. 
Notation exH' v A := (~ (forallH v (~ A)))%nn.

Notation "'exH' x .. y , p" := (@existH  LNN x .. (@existH LNN y p) ..)
  (x at level 0, y at level 0, at level 200, right associativity) : nn_scope. 

Notation "'allH' x .. y , p" := (@forallH LNN  x .. (@forallH LNN y p) ..)
  (x at level 0, y at level 0, at level 200, right associativity) : nn_scope. 

Notation S_ := Succ.

Infix "+" := Plus: nn_scope.
Infix "*" := Times: nn_scope.
Infix "<" := LT: nn_scope.
End NNnotations.

Import NNnotations. 



Lemma LNN_eqdec : language_decidable LNN.
Proof. split; decide equality. Qed.

Section Free_Variables.

Lemma freeVarPlus (x y : Term) :
 freeVarT LNN (Plus x y) = freeVarT LNN x ++ freeVarT LNN y.
Proof. now rewrite (app_nil_end (freeVarT LNN y)). Qed.

Lemma freeVarTimes (x y : Term):
 freeVarT LNN (Times x y) = freeVarT LNN x ++ freeVarT LNN y.
Proof. now rewrite (app_nil_end (freeVarT LNN y)). Qed.

Lemma freeVarSucc (x : Term): 
  freeVarT LNN (Succ x) = freeVarT LNN x.
Proof.
  now rewrite (app_nil_end (freeVarT LNN x)).
Qed.

Lemma freeVarZero : freeVarT LNN Zero = nil.
Proof. reflexivity. Qed.

Lemma freeVarLT (x y : Term) :
 freeVarF LNN (LT x y) = freeVarT LNN x ++ freeVarT LNN y.
Proof.
  now rewrite (app_nil_end (freeVarT LNN y)).
Qed.

End Free_Variables.

(** * Basic and derived properties *)
Section Logic.

Lemma Axm (T : System) (f : Formula): mem _ T f -> SysPrf T f.
Proof. apply (Axm LNN). Qed.

Lemma sysExtend (T U : System) (f : Formula):
 Included _ T U -> SysPrf T f -> SysPrf U f.
Proof. apply (sysExtend LNN). Qed.

Lemma sysWeaken (T : System) (f g : Formula):
  SysPrf T f -> SysPrf (Ensembles.Add _ T g) f.
Proof. apply (sysWeaken LNN). Qed.

Lemma impI (T : System) (f g : Formula):
 SysPrf (Ensembles.Add _ T g) f -> SysPrf T (g -> f)%nn.
Proof. apply (impI LNN). Qed.

Lemma impE  (T : System) (f g : Formula):
  SysPrf T (g -> f)%nn -> SysPrf T g -> SysPrf T f.
Proof. apply (impE LNN). Qed.

Lemma contradiction (T : System) (f g : Formula):
  SysPrf T f -> SysPrf T (~ f)%nn -> SysPrf T g.
Proof. apply (contradiction LNN). Qed.

Lemma nnE (T : System) (f : Formula):
  SysPrf T (~~ f)%nn -> SysPrf T f.
Proof. apply (nnE LNN). Qed.

Lemma noMiddle (T : System) (f : Formula):  SysPrf T (~ f \/ f)%nn.
Proof. apply (noMiddle LNN). Qed.

Lemma nnI  (T : System) (f : Formula):
  SysPrf T f -> SysPrf T (~ ~ f)%nn.
Proof. apply (nnI LNN). Qed.

Lemma cp1 (T : System) (f g : Formula) :
 SysPrf T (~ f -> ~ g)%nn -> SysPrf T (impH g f).
Proof. apply (cp1 LNN). Qed.

Lemma cp2 (T : System) (f g : Formula):
 SysPrf T (g -> f)%nn -> SysPrf T (~ f -> ~ g)%nn.
Proof. apply (cp2 LNN). Qed.

Lemma orI1 (T : System) (f g : Formula): 
  SysPrf T f -> SysPrf T (f \/ g)%nn.
Proof. apply (orI1 LNN). Qed.

Lemma orI2  (T : System) (f g : Formula): 
  SysPrf T g -> SysPrf T (f \/ g)%nn.
Proof. apply (orI2 LNN). Qed.

Lemma orE (T : System) (f g h : Formula):
  SysPrf T (f \/ g)%nn ->
  SysPrf T (f -> h)%nn -> SysPrf T (g -> h)%nn -> SysPrf T h.
Proof. apply (orE LNN). Qed.

Lemma orSys  (T : System) (f g h : Formula) :
 SysPrf (Ensembles.Add _ T f) h -> SysPrf (Ensembles.Add _ T g) h -> 
 SysPrf (Ensembles.Add _ T (f \/ g)%nn) h.
Proof. apply (orSys LNN). Qed.

Lemma andI (T : System) (f g : Formula):
 SysPrf T f -> SysPrf T g -> SysPrf T (f /\ g)%nn.
Proof. apply (andI LNN). Qed.

Lemma andE1 (T : System) (f g : Formula): 
  SysPrf T (f /\ g)%nn -> SysPrf T f.
Proof. apply (andE1 LNN). Qed.

Lemma andE2  (T : System) (f g : Formula):
  SysPrf T (f /\ g)%nn -> SysPrf T g.
Proof. apply (andE2 LNN). Qed.

Lemma iffI (T : System) (f g : Formula):
 SysPrf T (f -> g)%nn -> SysPrf T (g -> f)%nn -> 
 SysPrf T (f <-> g)%nn.
Proof. apply (iffI LNN). Qed.

Lemma iffE1 (T : System) (f g : Formula):
 SysPrf T (f <-> g)%nn -> SysPrf T (f -> g)%nn.
Proof. apply (iffE1 LNN). Qed.

Lemma iffE2 (T : System) (f g : Formula):
 SysPrf T (f <-> g)%nn -> SysPrf T (g -> f)%nn.
Proof. apply (iffE2 LNN). Qed.

Lemma forallI (T : System) (f : Formula) (v : nat):
 ~ In_freeVarSys LNN v T -> SysPrf T f -> SysPrf T (allH v, f)%nn.
Proof. apply (forallI LNN). Qed.

Lemma forallE  (T : System) (f : Formula) (v : nat) (t : Term):
 SysPrf T (allH v, f)%nn -> SysPrf T (substF LNN f v t).
Proof. apply (forallE LNN). Qed.

Lemma forallSimp (T : System) (f : Formula) (v : nat) :
 SysPrf T (allH v, f)%nn -> SysPrf T f.
Proof. apply (forallSimp LNN). Qed.

Lemma existI (T : System) (f : Formula) (v : nat) (t : Term):
 SysPrf T (substF LNN f v t) -> SysPrf T (exH v, f)%nn.
Proof. apply (existI LNN). Qed.

Lemma existE (T : System) (f g : Formula) (v : nat):
  ~ In_freeVarSys LNN v T ->
  ~ In v (freeVarF LNN g) ->
  SysPrf T (exH v, f)%nn -> SysPrf T (f -> g)%nn -> 
  SysPrf T g.
Proof. apply (existE LNN). Qed.

Lemma existSimp (T : System) (f : Formula) (v : nat):
  SysPrf T f -> SysPrf T (exH v, f)%nn.
Proof. apply (existSimp LNN). Qed.

Lemma existSys (T : System) (f g : Formula) (v : nat):
  ~ In_freeVarSys LNN v T ->
  ~ In v (freeVarF LNN g) ->
  SysPrf (SetAdds T f) g -> 
  SysPrf (SetAdds T (exH v, f)%nn) g.
Proof. apply (existSys LNN). Qed.

Lemma absurd1  (T : System) (f : Formula):
 SysPrf T (f -> ~ f)%nn -> SysPrf T (~ f)%nn.
Proof. apply (absurd1 LNN). Qed.

Lemma nImp (T : System) (f g : Formula):
 SysPrf T (f /\ ~ g)%nn -> SysPrf T (~ (f -> g))%nn.
Proof. apply (nImp LNN). Qed.

Lemma nOr (T : System) (f g : Formula):
 SysPrf T (~ f /\ ~ g)%nn -> SysPrf T (~ (f \/ g))%nn.
Proof. apply (nOr LNN). Qed.

Lemma nAnd (T : System) (f g : Formula):
 SysPrf T (~ f \/ ~ g)%nn -> SysPrf T (~ (f /\ g))%nn.
Proof. apply (nAnd LNN). Qed.

Lemma nForall (T : System) (f : Formula) (v : nat):
 SysPrf T (exH v, ~ f)%nn -> SysPrf T (~ (allH v, f))%nn.
Proof. apply (nForall LNN). Qed.

Lemma nExist (T : System) (f : Formula) (v : nat):
 SysPrf T (allH v, ~ f)%nn -> SysPrf T (~ (exH v, f))%nn.
Proof. apply (nExist LNN). Qed.

Lemma impRefl (T : System) (f : Formula):  SysPrf T (f -> f)%nn.
Proof. apply (impRefl LNN). Qed.

Lemma impTrans (T : System) (f g h : Formula):
 SysPrf T (f -> g)%nn -> SysPrf T (g -> h)%nn -> SysPrf T (f -> h)%nn.
Proof. apply (impTrans LNN). Qed.

Lemma orSym (T : System) (f g : Formula):
  SysPrf T (f \/ g)%nn -> SysPrf T (g \/ f)%nn.
Proof. apply (orSym LNN). Qed.

Lemma andSym (T : System) (f g : Formula):
SysPrf T (f /\ g)%nn -> SysPrf T (g /\ f)%nn.
Proof. apply (andSym LNN). Qed.

Lemma iffRefl (T : System) (f : Formula):  SysPrf T (f <-> f)%nn.
Proof. apply (iffRefl LNN). Qed.

Lemma iffSym  (T : System) (f g : Formula):
  SysPrf T (f <-> g)%nn -> SysPrf T (g <-> f)%nn.
Proof. apply (iffSym LNN). Qed.

Lemma iffTrans (T : System) (f g h : Formula):
  SysPrf T (f <-> g)%nn -> SysPrf T (g <-> h)%nn -> 
  SysPrf T (f <-> h)%nn.
Proof. apply (iffTrans LNN). Qed.

Lemma eqRefl (T : System) (a : Term): SysPrf T (a = a)%nn.
Proof. apply (eqRefl LNN). Qed.

Lemma eqSym (T : System) (a b : Term):
 SysPrf T (a = b)%nn -> SysPrf T (b = a)%nn.
Proof. apply (eqSym LNN). Qed.

Lemma eqTrans (T : System) (a b c : Term):
SysPrf T (a = b)%nn -> SysPrf T (b = c)%nn -> SysPrf T (a = c)%nn.
Proof. apply (eqTrans LNN). Qed.

(* TODO explicit inversion intro patterns *)
Lemma eqPlus (T : System) (a b c d : Term):
  SysPrf T (a = b)%nn -> SysPrf T (c = d)%nn -> 
  SysPrf T (a + c = b + d)%nn.
Proof.
  intros H H0; unfold Plus; apply (equalFunction); simpl.  
  destruct (consTerms LNN 1 (Tcons a (Tcons c (Tnil))))
    as [(a0, b0) p]. 
  simpl; 
    destruct  (consTerms LNN 1 (Tcons b (Tcons d (Tnil))))
    as [(a1, b1) p0].
  simpl; destruct  (consTerms LNN 0 b0) as [(a2, b2) p1].
  simpl; destruct  (consTerms LNN 0 b1) as [(a3,b3) p2].
  simpl; repeat split.
  - simpl in p; inversion p /r; intros H2 H3.
    simpl in p0; inversion p0 /r; intros H4 H5.
    apply H.
  - simpl in p; inversion p /r; intros H2 H3.
    rewrite <- p1 in H3.
    simpl in H3; inversion H3 /r; intros H4 H5.
    simpl in p0; inversion p0 /r; intros H6 H7.
    rewrite <- p2 in H7.
    inversion H7; apply H0.
Qed.

Lemma eqTimes (T : System) (a b c d : Term):
 SysPrf T (a = b)%nn -> SysPrf T (c = d)%nn -> 
 SysPrf T (a * c = b * d)%nn.
Proof.
  intros H H0; unfold Times; apply (equalFunction LNN).
  simpl; 
    destruct (consTerms LNN 1 (Tcons a (Tcons c (Tnil))))
    as [(a0, b0) p].
  simpl; destruct (consTerms LNN 1 (Tcons b (Tcons d (Tnil))))
    as [(a1, b1) p0].
  simpl; destruct  (consTerms LNN 0 b0) as [(a2, b2) p1].
  simpl; induction (consTerms LNN 0 b1) as [(a3,b3) p2].
  repeat split.
  - simpl in p; inversion p /r; intros H2 H3.
    simpl in p0; inversion p0 /r; intros H4 H5.
    apply H.
  - simpl in p; inversion p /r; intros H2 H3.
    rewrite <- p1 in H3;  simpl in H3; inversion H3 /r; intros H4 H5.
    simpl in p0; inversion p0 /r; intros H6 H7.
    rewrite <- p2 in H7; inversion H7; apply H0.
Qed.

Lemma eqSucc (T : System) (a b : Term):
  SysPrf T (a = b)%nn -> SysPrf T (Succ a = Succ b)%nn.
Proof.
  intro H; unfold Succ; apply (equalFunction LNN).
  simpl; destruct (consTerms LNN 0 (Tcons a (Tnil)))
    as [(a0, b0) p].
  simpl; destruct  (consTerms LNN 0 (Tcons b (Tnil)))
    as [(a1, b1) p0].
  simpl; repeat split.
  simpl in p.
  inversion p /r; intros H1 H2;  simpl in p0.
  inversion p0; apply H.
Qed.

Lemma eqLT (T : System) (a b c d : Term):
 SysPrf T (a = b)%nn -> SysPrf T (c = d)%nn -> 
 SysPrf T (a < c <-> b < d)%nn.
Proof.
  intros H H0; unfold LT; apply (equalRelation LNN).
  simpl;  destruct  (consTerms LNN 1 (Tcons a (Tcons c (Tnil))))
    as [(a0, b0) p].
  simpl; destruct (consTerms LNN 1 (Tcons b (Tcons d (Tnil))))
    as [(a1, b1) p0].
  simpl; destruct (consTerms LNN 0 b0) as [(a2, b2) p1]. 

  destruct  (consTerms LNN 0 b1) as [(a3, b3) p2]. 
  simpl;repeat split.
  - simpl in p; inversion p /r; intros H2 H3.
    simpl in p0; inversion p0 /r; intros H4 H5.
    apply H.
  - simpl in p; inversion p /r; intros H2 H3.
    rewrite <- p1 in H3; simpl in H3.
    inversion H3 /r; intros H4 H5.
    simpl in p0; inversion p0 /r; intros H6 H7.
    rewrite <- p2 in H7; inversion H7; apply H0.
Qed.

End Logic.

Fixpoint natToTerm (n : nat) : Term :=
  match n with
  | O => Zero
  | S m => Succ (natToTerm m)
  end.

Lemma closedNatToTerm :
 forall a v : nat, ~ In v (freeVarT LNN (natToTerm a)).
Proof.
intros a v; induction a as [| a Hreca].
 - simpl; auto. 
  - simpl; now rewrite freeVarSucc.
Qed.


