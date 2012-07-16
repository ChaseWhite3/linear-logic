Variable Atom : Type.

Inductive Formula : Type :=
| F_Atom : Atom -> Formula
| F_Impl : Formula -> Formula -> Formula
| F_Both : Formula -> Formula -> Formula
| F_Choo : Formula -> Formula -> Formula
| F_Eith : Formula -> Formula -> Formula
| F_OfCo : Formula -> Formula.

Inductive Assumption : Type :=
| A_Linear : Formula -> Assumption
| A_Intuit : Formula -> Assumption.

Definition Assumptions := list Assumption.

Require Import List.
Open Scope list_scope.

Inductive Provable : Assumptions -> Formula -> Prop :=
| P_L_Id    : forall A,
  Provable ((A_Linear A)::nil) A
| P_I_Id    : forall A,
  Provable ((A_Intuit A)::nil) A
| P_Exc     : forall (Gamma Delta:Assumptions) (A: Formula),
  Provable (Gamma++Delta) A -> Provable (Delta ++ Gamma ) A
| P_Contract: forall (Gamma:Assumptions) (A B:Formula),
  Provable (Gamma ++ (A_Intuit A)::(A_Intuit A)::nil) B ->
            Provable (Gamma ++ (A_Intuit A)::nil) B
| P_Weaken  : forall (Gamma:Assumptions) (A B: Formula),
  Provable Gamma B -> Provable (Gamma++(A_Intuit A)::nil) B
| P_OfCoId  : forall (Gamma:Assumptions) (A : Formula),
  (forall A, In A Gamma -> exists F, A = A_Intuit F) ->
  Provable Gamma A -> Provable Gamma (F_OfCo A)
| P_OfCoEl  : forall (Gamma Delta:Assumptions) (A B : Formula),
  Provable Gamma (F_OfCo A) -> Provable (Delta ++ (A_Intuit A)::nil) B ->
            Provable (Gamma ++ Delta) B
| P_ImplId  : forall (Gamma : Assumptions) (A B: Formula),
  Provable (Gamma ++ (A_Linear A)::nil) B -> Provable Gamma (F_Impl A B)
| P_ImplEl  : forall (Gamma Delta : Assumptions) (A B : Formula),
  Provable Gamma (F_Impl A B) -> Provable Delta A -> Provable (Gamma++Delta) B
| P_BothId  : forall (Gamma Delta: Assumptions) (A B : Formula),
  Provable Gamma A -> Provable Delta B -> Provable (Gamma ++ Delta) (F_Both A B)
| P_BothEl  : forall (Gamma Delta : Assumptions) (A B C : Formula),
  Provable Gamma (F_Both A B) -> Provable (Gamma ++ (A_Linear A)::(A_Linear B)::nil) C ->
            Provable (Gamma++Delta) C
| P_ChooId  : forall (Gamma : Assumptions) (A B : Formula),
  Provable Gamma A -> Provable Gamma B -> Provable Gamma (F_Choo A B)
| P_ChooEl1 : forall (Gamma : Assumptions) (A B : Formula),
  Provable Gamma (F_Choo A B) -> Provable Gamma A
| P_ChooEl2 : forall (Gamma : Assumptions) (A B : Formula),
  Provable Gamma (F_Choo A B) -> Provable Gamma B
| P_EithId1 : forall (Gamma : Assumptions) (A B : Formula),
  Provable Gamma A -> Provable Gamma (F_Eith A B)
| P_EithId2 : forall (Gamma : Assumptions) (A B : Formula),
  Provable Gamma B -> Provable Gamma (F_Eith A B)
| P_EithEl  : forall (Gamma Delta: Assumptions) (A B C: Formula),
  Provable Gamma (F_Eith A B) -> Provable (Gamma ++ (A_Linear A)::nil) C ->
            Provable (Delta ++(A_Linear B)::nil) C -> Provable (Gamma ++ Delta) C.

 

Section By_Definition.

 Theorem simple_linear_assumption : forall (A:Atom),
  Provable ((A_Linear (F_Atom A))::nil) (F_Atom A).
 Proof.
 intros.
  apply P_L_Id.
 Qed.

 Theorem simple_intuit_assumption : forall (A:Atom),
  Provable ((A_Intuit (F_Atom A))::nil) (F_Atom A).
 Proof.
 intros.
  apply P_I_Id.
 Qed.

 Theorem simple_exchange : forall (Gamma Delta : Assumptions) (A: Atom),
  Provable (Gamma++Delta) (F_Atom A) -> Provable (Delta ++ Gamma ) (F_Atom A).
 Proof.
 intros.
  apply P_Exc.
  apply H.
 Qed.

 Theorem simple_contract : forall (Gamma : Assumptions) (A B : Atom),
  Provable (Gamma ++ (A_Intuit (F_Atom A))::(A_Intuit (F_Atom A))::nil) (F_Atom B) ->
            Provable (Gamma ++ (A_Intuit (F_Atom A))::nil) (F_Atom B).
 Proof.
 intros.
  apply P_Contract.
  apply H.
 Qed.
 
 Theorem simple_weakening : forall (Gamma:Assumptions) (A B : Atom),
  Provable Gamma (F_Atom B) -> Provable (Gamma++(A_Intuit (F_Atom A))::nil) (F_Atom B).
 Proof.
 intros.
  apply P_Weaken.
  apply H.
 Qed. 

 Definition gamma_i : Assumptions := nil. 
 Theorem simpl_of_course_id : forall (A : Formula),
  Provable gamma_i A -> Provable gamma_i (F_OfCo A).
 Proof.
  intros A PA.
  apply P_OfCoId.
  intros A' IN.
  simpl in IN.
  contradiction IN.
  exact PA.
 Qed.
 
 Theorem simpl_of_course_elimination : forall (Gamma Delta:Assumptions) (A B : Formula),
  Provable Gamma (F_OfCo A) -> Provable (Delta ++ (A_Intuit  A)::nil)  B ->
            Provable (Gamma ++ Delta) B.
 Proof.
 intros.
  apply P_OfCoEl with (A:=A).
  exact H.
  exact H0.
 Qed.

 Theorem simpl_impl_id : forall (Gamma : Assumptions) (A B: Formula),
  Provable (Gamma ++ (A_Linear A)::nil) B -> Provable Gamma (F_Impl A B).
 Proof.
 intros.
  apply P_ImplId.
  apply H.
 Qed.
 
 Theorem simpl_impl_elimination : forall (Gamma Delta : Assumptions) (A B : Formula),
  Provable Gamma (F_Impl A B) -> Provable Delta A -> Provable (Gamma++Delta) B.
 Proof.
 intros.
  apply P_ImplEl with (A:=A).
  apply H.
  apply H0.
 Qed.

 Theorem simpl_and_both_id : forall (Gamma Delta: Assumptions) (A B : Formula),
  Provable Gamma A -> Provable Delta B -> Provable (Gamma ++ Delta) (F_Both A B).
 Proof.
 intros.
  apply P_BothId.
  apply H.
  apply H0.
 Qed.

 Theorem simpl_and_both_el: forall (Gamma Delta : Assumptions) (A B C : Formula),
  Provable Gamma (F_Both A B) -> Provable (Gamma ++ (A_Linear A)::(A_Linear B)::nil) C ->
            Provable (Gamma++Delta) C.
 Proof.
 intros.
  apply P_BothEl with (A:=A) (B:=B).
  apply H.
  apply H0.
 Qed.

 Theorem simpl_choose_id: forall (Gamma : Assumptions) (A B : Formula),
  Provable Gamma A -> Provable Gamma B -> Provable Gamma (F_Choo A B).
 Proof.
 intros.
  apply P_ChooId.
  apply H.
  apply H0.
 Qed.

 Theorem simpl_choose_el_one: forall (Gamma : Assumptions) (A B : Formula),
  Provable Gamma (F_Choo A B) -> Provable Gamma A.
 Proof.
 intros. 
  apply P_ChooEl1 with (B:=B).
  apply H.
 Qed.
 
 Theorem simpl_choose_el_two: forall (Gamma : Assumptions) (A B : Formula),
  Provable Gamma (F_Choo A B) -> Provable Gamma B.
 Proof.
 intros.
  apply P_ChooEl2 with (A:=A).
  apply H.
 Qed.

 Theorem simpl_either_id_1: forall (Gamma : Assumptions) (A B : Formula),
  Provable Gamma A -> Provable Gamma (F_Eith A B).
 Proof.
  intros.
   apply P_EithId1.
   apply H.
 Qed.
 
 Theorem simpl_either_id_2: forall (Gamma : Assumptions) (A B : Formula),
  Provable Gamma B -> Provable Gamma (F_Eith A B).
 Proof.
  intros.
   apply P_EithId2.
   apply H.
 Qed.

 Theorem simpl_either_el: forall (Gamma Delta: Assumptions) (A B C: Formula),
  Provable Gamma (F_Eith A B) -> Provable (Gamma ++ (A_Linear A)::nil) C ->
            Provable (Delta ++(A_Linear B)::nil) C -> Provable (Gamma ++ Delta) C.
 Proof.
  intros. apply P_EithEl with (A:=A) (B:=B). apply H. apply H0. apply H1.
 Qed.

End By_Definition.


Section Generic_proofs.

 Theorem gamma_intuit_assumption_proves_b: forall (Gamma: Assumptions) (A B: Formula),
  Provable (Gamma ++ A_Linear A :: nil) B ->Provable (Gamma ++ (A_Intuit A)::nil) B.
 Proof.
  intros.
  apply P_ImplEl with (A:=A).
  apply P_ImplId. apply H. apply P_I_Id.
 Qed.

 Theorem need_for_intuit_assumptions: forall (A B : Formula),
  Provable ((A_Linear (F_Impl A (F_OfCo B)))::(A_Linear A)::nil) (F_OfCo B).
 Proof.
  intros. 
   apply P_ImplEl with (Gamma:= (A_Linear (F_Impl A (F_OfCo B)))::nil)(Delta:= (A_Linear A)::nil) (A:=A);
   apply P_L_Id. 
 Qed. 

End Generic_proofs.
  
Theorem theorem_prover:
 forall A F,
  { Provable A F } + { ~ Provable A F }.
Proof.
 intros. induction F. induction A. right. intros H. 
   inversion H.

   (** Weakening -nil- *)
   Focus 3. apply app_eq_nil in H0. inversion H0. inversion H4.
   (** Both elimination -nil- *)
   (** Focus 5. *)
   (** Contraction -nil- *)
   (** Focus 2. *)
   (** Choose Elimination1 -nil- *)
   (** Focus 6. *)
   (** Choose Elimination2 -nil- *)
   (** Focus 7. *)
   (** Either Elimination -nil- *)
   (** Focus 8. *)

   (** Impl elimination -nil- *) 
   Focus 4. apply app_eq_nil in H0. inversion H0. rewrite H4 in H1. rewrite H4 in H1. assert (Gamma ++ Delta = nil). SearchAbout Lists.  
Admitted.

Check theorem_prover.

 
   