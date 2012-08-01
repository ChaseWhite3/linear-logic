Variable Atom : Type.

Inductive Formula : Type :=
| F_Atom : Atom -> Formula
| F_Impl : Formula -> Formula -> Formula
| F_Both : Formula -> Formula -> Formula
| F_Choo : Formula -> Formula -> Formula
| F_Eith : Formula -> Formula -> Formula
| F_OfCo : Formula -> Formula.
Hint Constructors Formula.

Inductive Assumption : Type :=
| A_Linear : Formula -> Assumption
| A_Intuit : Formula -> Assumption.
Hint Constructors Assumption.

Definition Assumptions := list Assumption.
Hint Unfold Assumptions.

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
(*| P_ImplId  : forall (Gamma : Assumptions) (A B: Formula),
  Provable (Gamma ++ (A_Linear A)::nil) B -> Provable Gamma (F_Impl A B)*)
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
(**
| P_EithId1 : forall (Gamma : Assumptions) (A B : Formula),
  Provable Gamma A -> Provable Gamma (F_Eith A B)
| P_EithId2 : forall (Gamma : Assumptions) (A B : Formula),
  Provable Gamma B -> Provable Gamma (F_Eith A B) *)
| P_EithEl  : forall (Gamma Delta: Assumptions) (A B C: Formula),
  Provable Gamma (F_Eith A B) -> Provable (Gamma ++ (A_Linear A)::nil) C ->
            Provable (Delta ++(A_Linear B)::nil) C -> Provable (Gamma ++ Delta) C.
Hint Constructors Provable.

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

(** Theorem simpl_impl_id : forall (Gamma : Assumptions) (A B: Formula),
  Provable (Gamma ++ (A_Linear A)::nil) B -> Provable Gamma (F_Impl A B).
 Proof.
 intros.
  apply P_ImplId.
  apply H.
 Qed. *)
 
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

(** Theorem simpl_either_id_1: forall (Gamma : Assumptions) (A B : Formula),
  Provable Gamma A -> Provable Gamma (F_Eith A B).
 Proof.
  intros.
   apply P_EithId1.
   apply H.
 Qed. *)
 
(** Theorem simpl_either_id_2: forall (Gamma : Assumptions) (A B : Formula),
  Provable Gamma B -> Provable Gamma (F_Eith A B).
 Proof.
  intros.
   apply P_EithId2.
   apply H.
 Qed. *)

 Theorem simpl_either_el: forall (Gamma Delta: Assumptions) (A B C: Formula),
  Provable Gamma (F_Eith A B) -> Provable (Gamma ++ (A_Linear A)::nil) C ->
            Provable (Delta ++(A_Linear B)::nil) C -> Provable (Gamma ++ Delta) C.
 Proof.
  intros. apply P_EithEl with (A:=A) (B:=B). apply H. apply H0. apply H1.
 Qed.

End By_Definition.


Section Generic_proofs.

(** Theorem gamma_intuit_assumption_proves_b: forall (Gamma: Assumptions) (A B: Formula),
  Provable (Gamma ++ A_Linear A :: nil) B ->Provable (Gamma ++ (A_Intuit A)::nil) B.
 Proof.
  intros.
  apply P_ImplEl with (A:=A).
  apply P_ImplId. apply H. apply P_I_Id.
 Qed. *)

 Theorem need_for_intuit_assumptions: forall (A B : Formula),
  Provable ((A_Linear (F_Impl A (F_OfCo B)))::(A_Linear A)::nil) (F_OfCo B).
 Proof.
  intros. 
   apply P_ImplEl with (Gamma:= (A_Linear (F_Impl A (F_OfCo B)))::nil)(Delta:= (A_Linear A)::nil) (A:=A);
   apply P_L_Id. 
 Qed. 

End Generic_proofs.

(*
Section not_decide.
 Variable a : Atom.  

 Lemma nil_proves:
   exists F, Provable nil F.
 Proof.
  exists (F_Impl (F_Atom a) (F_Atom a)).
  apply P_ImplId.
  simpl.
  apply P_L_Id.
 Qed.
End not_decide.
*)

Theorem nil_doesnt_prove:
 forall F,
  ~ Provable nil F.
Proof.
Admitted.

(** Fixpoint all_theorems_fun (A:Assumptions) : list Formula :=



 match A with
 | nil =>
   nil
 | a :: A =>
   match a with
   | A_Intuit F =>
     let A_sub := all_theorems_fun A in
     A_sub
     ++ (suppose that (F -> b) is in A_sub,
         then b should be in the result,
          because we can get (F->b) then apply P_ImplEl with f)
   | A_Linear F =>
     nil
   end
 end. *)

Section all_cases.
 Variable all : Assumptions -> list Formula.
 Hypothesis all_nil_eq:
  all nil = nil.
 Hint Rewrite all_nil_eq.
 Hypothesis all_sound:
  forall A f,
   In f (all A) -> Provable A f.
 Hint Resolve all_sound.

Definition all_P_L_Id A :=
 match A with
 | nil => nil
 | a :: l =>
   match l with
   | nil => 
     match a with
     | A_Linear f =>
	f :: nil
     | _ =>
        nil
     end
   | _ :: _ =>
     nil
   end
 end.

Lemma all_P_L_Id_sound:
 forall A f,
  In f (all_P_L_Id A) -> Provable A f.
Proof.
 induction A as [|a A]; simpl; intros f; try tauto.
 destruct A as [|b A]; simpl; try tauto.
 destruct a as [a|a]; simpl; try tauto.
 intros [EQ | F]; try tauto.
 rewrite EQ.
 eauto.
 (** apply P_L_Id. **)
Qed.

Fixpoint all_splits {X:Type} (a: list X) : list ((list X)*(list X)) :=
 (nil,a) :: match a with
  | nil => nil
  | f :: t => map (fun p => match p with 
			     |(x,y) => ((f :: x),y)
                            end)
                        (all_splits t)
 end.

Theorem all_splits_correct : forall {X:Type} (l a b: list X) ,
 In (a,b) (all_splits l) <-> a++b = l.
Proof.
 induction l as [|e l]; intros a b; simpl; split; intros H.
 (** nil case *)
 inversion H. inversion H0. simpl. reflexivity. inversion H0. left.
 apply app_eq_nil in H. inversion H. rewrite H0. rewrite H1. reflexivity.
 (** inductive case *)
 inversion H. inversion H0. simpl. reflexivity. SearchAbout In. clear H. apply in_map_iff in H0.
 inversion H0. inversion H. clear H H0. destruct x. apply IHl in H2. inversion H1. rewrite <-H3.
 rewrite <-H2. reflexivity. 
 (**  *)
 rewrite in_map_iff. destruct a. left. simpl in H. rewrite H. auto. right. exists (a,b). split.
 inversion H. auto. apply IHl. inversion H. auto. Qed.

Definition all_P_OfCoEl all (A:Assumptions) :=
 flat_map
  (fun gamma_delta:(Assumptions*Assumptions) =>
    let (gamma,delta) := gamma_delta in
    let gamma_proves := all gamma in
    flat_map
     (fun f =>
      match f with
      | F_OfCo f_a =>
        all (delta ++ ((A_Intuit f_a)::nil))
      | _ =>
        nil
      end)
     gamma_proves)
  (all_splits A).

Theorem all_P_OfCoEl_sound:
 forall A f,
  In f (all_P_OfCoEl all A) -> Provable A f.
Proof.
 induction A as [|a A]; simpl; intros f.

 unfold all_P_OfCoEl. simpl. rewrite all_nil_eq. 
 simpl.

 tauto.
 unfold all_P_OfCoEl. rewrite in_flat_map.
 intros [[gamma delta] [In_S In_a]].
 rewrite in_flat_map in In_a.
 destruct In_a as [a_f [In_a_g In_a_d]].
 rewrite (all_splits_correct (a::A) gamma delta) in In_S.
 rewrite <- In_S.
 destruct a_f; simpl in In_a_d; try tauto.
 eauto.
 (** apply (P_OfCoEl gamma delta a_f f).
     apply all_sound. exact In_a_g.
     apply all_sound. exact In_a_d. **)
Qed.

End all_cases.

Fixpoint all_theorems (n:nat) A :=
 match n with
 | O => nil
 | S n =>
  (all_P_L_Id A)
  ++ (all_P_OfCoEl (all_theorems n) A)
  (* ++ one for each case *)
 end.

Theorem all_theorems_nil:
 forall n,
  all_theorems n nil = nil.
Proof.
 induction n as [|n]; simpl; try tauto.

 (* one for each case *)
 unfold all_P_OfCoEl. simpl. rewrite IHn.
 simpl. tauto.
Qed.

Theorem all_theorems_sound:
 forall n A f,
   In f (all_theorems n A) -> Provable A f.
Proof.
 induction n as [|n];
  intros A f;
  simpl.
 tauto.
 rewrite in_app_iff.
 intros [In_L_Id | In_P_OfCoEl (*| one for each case *) ].
 apply all_P_L_Id_sound. exact In_L_Id.
 apply (all_P_OfCoEl_sound (all_theorems n)).
 apply all_theorems_nil.
 apply IHn.
 exact In_P_OfCoEl.
Qed.

(* Completeness: *)
(* Provable -> In needs a bound *)

Theorem all_theorems:
 forall A,
  { FS | forall F, Provable A F <-> In F FS }.
Proof.
 intros. induction A.

 exists nil. intros F. split; intros P.
 
 unfold In. eapply nil_doesnt_prove. apply P.
 unfold In in P. tauto.

 (** If we add an assumption will it still be true? Well the old proof is no longer valid
   what is valid though is a proof where we use it and all of the previous items. *)
 destruct IHA as [ FS P_eq_FS ].
 destruct a as [a | a].
 Focus 2.

 exists (FS). intros F. split.
 Focus 2.

 intros IN. rewrite <- P_eq_FS in IN.
 apply (P_Exc A (A_Intuit a::nil) F).
 apply (P_Weaken A a F).
 apply IN.

 Focus 2.
 

 intros P. rewrite <- P_eq_FS.
         
 


Theorem theorem_prover:
 forall A F,
  { Provable A F } + { ~ Provable A F }.
Proof.
 intros. induction F. induction A. right. intros H. 
   inversion H.

   (** Weakening -nil- *)
   Focus 3. apply app_eq_nil in H0. inversion H0. inversion H4.
   (** Exchange -nil- *)
   Focus 1. apply app_eq_nil in H0. inversion H0.
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

 
   