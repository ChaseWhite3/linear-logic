
Variable Atom : Set.
Hypothesis Atom_eq_dec:
 forall (x y:Atom),
  {x = y} + {x <> y}.
Hint Resolve Atom_eq_dec.

Inductive Formula : Set :=
| F_Atom : Atom -> Formula
| F_Impl : Formula -> Formula -> Formula
| F_Both : Formula -> Formula -> Formula
| F_Choo : Formula -> Formula -> Formula
| F_Eith : Formula -> Formula -> Formula
| F_OfCo : Formula -> Formula.
Hint Constructors Formula.

Theorem Formula_eq_dec:
 forall (x y:Formula),
  {x = y} + {x <> y}.
Proof.
 decide equality.
Qed.

Inductive Assumption : Set :=
| A_Linear : Formula -> Assumption
| A_Intuit : Formula -> Assumption.
Hint Constructors Assumption.

Definition Assumptions := list Assumption.
Hint Unfold Assumptions.

Require Import List.
Open Scope list_scope.

Inductive Proof : Set :=
| Pr_L_Id : Formula -> Proof.
Hint Constructors Proof.

Inductive Provable : Assumptions -> Formula -> Prop :=
| P_L_Id    : forall A,
  Provable ((A_Linear A)::nil) A
| P_I_Id    : forall A,
  Provable ((A_Intuit A)::nil) A
| P_Exc     : forall (Gamma Delta:Assumptions) (A: Formula),
  Provable (Gamma++Delta) A -> Provable (Delta ++ Gamma ) A
| P_Contract: forall (Gamma:Assumptions) (A B:Formula),
  Provable ((A_Intuit A)::(A_Intuit A)::Gamma) B ->
  Provable ((A_Intuit A)::Gamma) B
| P_Weaken  : forall (Gamma:Assumptions) (A B: Formula),
  Provable Gamma B -> Provable ((A_Intuit A)::Gamma) B
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
  Provable Gamma (F_Both A B) -> Provable (Delta ++ (A_Linear A)::(A_Linear B)::nil) C ->
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
  Provable Gamma (F_Eith A B) -> Provable (Delta ++ (A_Linear A)::nil) C ->
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
  Provable ((A_Intuit (F_Atom A))::(A_Intuit (F_Atom A))::Gamma) (F_Atom B) ->
            Provable ((A_Intuit (F_Atom A))::Gamma) (F_Atom B).
 Proof.
 intros.
  apply P_Contract.
  apply H.
 Qed.
 
 Theorem simple_weakening : forall (Gamma:Assumptions) (A B : Atom),
  Provable Gamma (F_Atom B) -> Provable ((A_Intuit (F_Atom A))::Gamma) (F_Atom B).
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
  Provable Gamma (F_Both A B) -> Provable (Delta ++ (A_Linear A)::(A_Linear B)::nil) C ->
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
  Provable Gamma (F_Eith A B) -> Provable (Delta ++ (A_Linear A)::nil) C ->
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

(*
Theorem nil_doesnt_prove:
 forall F,
  ~ Provable nil F.
Proof.
Admitted.
*)

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

Check all_P_L_Id.

Definition all_P_L_Id_p (A:Assumptions) :
 { F : list Formula | forall f, In f F -> (Provable A f) }.
Proof.
 destruct A as [|a l].
 exists nil. intros f. simpl. tauto.
 destruct l as [|x l].
 destruct a as [lf|nf].
 exists (lf :: nil).
 intros sf. simpl. intros [EQ | F]; try tauto.
 rewrite EQ. apply P_L_Id.
 exists nil. intros f. simpl. tauto.
 exists nil. intros f. simpl. tauto.
Qed.

End all_cases.

Extraction all_P_L_Id_p.

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
Pr
oof.
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
 (** eauto. *)
 apply (P_OfCoEl gamma delta a_f f).
 apply all_sound. exact In_a_g.
 apply all_sound. exact In_a_d. 
Qed.

Definition all_P_I_Id A:=
 match A with
 | nil => nil
 | a :: l =>
   match l with
   | nil => 
     match a with
     | A_Intuit f =>
	f :: nil
     | _ =>
        nil
     end
   | _ :: _ =>
     nil
   end
 end.

Lemma all_P_I_Id_sound:
 forall A f,
  In f (all_P_I_Id A) -> Provable A f.
Proof.
 induction A as [|a A]; simpl; intros f; try tauto.
 destruct A as [|b A]; simpl; try tauto.
 destruct a as [a|a]; simpl; try tauto.
 intros [EQ | F]; try tauto.
 rewrite EQ.
 eauto.
 (** apply P_L_Id. **)
Qed.

Check all_P_OfCoEl. 

Print flat_map.

Definition all_P_Exc (all: Assumptions -> list Formula) (A:Assumptions) :=
 flat_map (** make 1 list out of something done to every element of the list you pass in *)
  (fun gamma_delta: (Assumptions*Assumptions) =>
    let (gamma, delta) :=gamma_delta in
     all (delta++ gamma))
  (all_splits A).

Check all_P_Exc.
Lemma all_P_Exc_sound:
 forall A f,
  In f (all_P_Exc all A) -> Provable A f.
Proof.
 induction A as [|a A]; simpl; intros f.
 unfold all_P_Exc. simpl. rewrite all_nil_eq. simpl. tauto.

 unfold all_P_Exc. rewrite in_flat_map.
 intros [[gamma delta] [In_S In_a]].
 rewrite (all_splits_correct (a::A) gamma delta) in In_S.
 rewrite <- In_S.
 eauto.
 Qed.


Definition all_P_Contract (all: Assumptions -> list Formula) (A:Assumptions) : list Formula :=
 match A with
  | (A_Intuit f_a)::t => (all ((A_Intuit f_a)::(A_Intuit f_a)::t))
  | _ => nil
  end.

Lemma all_P_Contract_sound:
 forall A f,
  In f (all_P_Contract all A) -> Provable A f.
Proof.
 induction A as [|a A]; simpl.
 tauto. 
 intros. destruct a. apply in_nil in H. tauto.
 eauto.
 Qed.
 
 

Definition all_P_Weaken (all: Assumptions -> list Formula) (A:Assumptions) :=
 match A with
  | (A_Intuit f_a)::t => (all t)
  | _ => nil
  end. 

Lemma all_P_Weaken_sound:
 forall A f,
  In f (all_P_Weaken all A) -> Provable A f.
Proof.
 induction A as [|a A]; simpl.
 tauto.
 intros. destruct a. apply in_nil in H. 
 tauto.
 eauto.
 Qed.

(** P_OfCoId  : forall (Gamma:Assumptions) (A : Formula),
     (forall A, In A Gamma -> exists F, A = A_Intuit F) ->
     Provable Gamma A -> Provable Gamma (F_OfCo A) *)

Definition all_intuit :=
  forallb (fun a => match a with
                    | A_Intuit _ => true
                    | _ => false
                    end).

Eval compute in all_intuit nil.
Variable Z:Atom.
Eval compute in all_intuit ((A_Intuit (F_Atom Z))::nil).
Eval compute in all_intuit ((A_Intuit (F_Atom Z))::(A_Intuit (F_Atom Z))::(A_Intuit (F_Atom Z))::nil).
Eval compute in all_intuit ((A_Intuit (F_Atom Z))::(A_Linear (F_Atom Z))::(A_Intuit (F_Atom Z))::nil).
Eval compute in all_intuit ((A_Linear (F_Atom Z))::nil).

Lemma all_intuit_correct:
 forall A,
  true = all_intuit A ->
  forall a, In a A -> exists F, a = A_Intuit F.
Proof.
 induction A; simpl. tauto. 
 destruct a; simpl. intros H. inversion H.
 intros EQ a [EQ_a | IN_a]. exists f. symmetry. tauto.
 auto.
Qed.

Definition all_P_OfCoId (all: Assumptions -> list Formula) (A:Assumptions) :=
 let gamma_proves := if all_intuit A then all A else nil in
 flat_map 
  (fun f =>
    (F_OfCo f) :: nil)
  gamma_proves.

Lemma all_P_OfCoId_sound:
 forall A f,
  In f (all_P_OfCoId all A) -> Provable A f.
Proof.
 unfold all_P_OfCoId.
 induction A as [|a A]; simpl; intros f; rewrite in_flat_map; simpl.

 rewrite all_nil_eq. simpl.
 intros [x [H_F H_A]]. tauto.

 intros [x [H_I [H_Xeq | H_F]]]; try tauto.
 rewrite <- H_Xeq in *. clear H_Xeq f.
 destruct a as [a|a]; simpl in H_I.
 tauto.
 remember (all_intuit A). destruct b.
 apply all_sound in H_I.
 apply P_OfCoId.

 apply all_intuit_correct. simpl. tauto.
 tauto.
 simpl in H_I.
 tauto.
Qed.

Definition all_P_ImplEl (all: Assumptions -> list Formula) (A:Assumptions) :=
 flat_map
  (fun gamma_delta:(Assumptions*Assumptions) =>
    let (gamma,delta) := gamma_delta in
    let gamma_proves := all gamma in
    let delta_proves := all delta in
    flat_map
     (fun fd =>
      flat_map
      (fun fg =>
       match fg with
       | F_Impl f_a f_b =>
         if Formula_eq_dec fd f_a then
         f_b::nil else nil
       | _ =>
        nil
       end)
      gamma_proves)
     delta_proves)
  (all_splits A).

Lemma all_P_ImplEl_sound:
 forall A f,
  In f (all_P_ImplEl all A) -> Provable A f.
Proof.
 unfold all_P_ImplEl.
 intros A f.
 rewrite in_flat_map.
 intros [[gamma delta] [IN_all_splits IN_f_flat]].
 rewrite in_flat_map in IN_f_flat.
 destruct IN_f_flat as [fg [IN_allg IN_f_flat]].
 rewrite in_flat_map in IN_f_flat.
 destruct IN_f_flat as [fd [IN_alld IN_f_match]].
 destruct fd; simpl in IN_f_match; try tauto.
 destruct (Formula_eq_dec fg fd1); simpl in IN_f_match; try tauto.
 destruct IN_f_match as [EQ_f | F]; try tauto.
 rewrite EQ_f in *; clear EQ_f fd2.
 rewrite <- e in *; clear e fd1.
 apply all_splits_correct in IN_all_splits.
 rewrite <- IN_all_splits.
 eapply P_ImplEl; eauto.
Qed. 

Definition all_P_BothId (all: Assumptions -> list Formula) (A:Assumptions) :=
 flat_map
  (fun gamma_delta:(Assumptions*Assumptions) =>
    let (gamma,delta) := gamma_delta in
    let gamma_proves := all gamma in
    let delta_proves := all delta in
    flat_map
     (fun fd =>
      flat_map
      (fun fg =>
       F_Both fg fd :: nil 
       )
      gamma_proves)
     delta_proves)
  (all_splits A).

Lemma all_P_BothId_sound:
 forall A f,
  In f (all_P_BothId all A) -> Provable A f.
Proof.
 unfold all_P_BothId.
 intros A f.
 rewrite in_flat_map.
 intros [[gamma delta] [IN_all_splits IN_f_flat]].
 rewrite in_flat_map in IN_f_flat.
 destruct IN_f_flat as [fg [IN_allg IN_f_flat]].
 rewrite in_flat_map in IN_f_flat.
 destruct IN_f_flat as [fd [IN_alld IN_f_both]].
 destruct f; simpl in IN_f_both; inversion IN_f_both; inversion H; try tauto.
 apply all_splits_correct in IN_all_splits. rewrite <- IN_all_splits.
 eapply P_BothId. 
 apply all_sound. rewrite <- H1. apply IN_alld.
 apply all_sound. rewrite <- H2. apply IN_allg.
Qed.

Definition all_P_BothEl all (A:Assumptions) :=
 flat_map
  (fun gamma_delta:(Assumptions*Assumptions) =>
    let (gamma,delta) := gamma_delta in
    let gamma_proves := all gamma in
    flat_map
     (fun f =>
      match f with
      | F_Both f_a f_b =>
        all (delta ++ ((A_Linear f_a) :: (A_Linear f_b) ::nil))
      | _ =>
        nil
      end)
     gamma_proves)
  (all_splits A).

Lemma all_P_BothEl_sound:
 forall A f,
  In f (all_P_BothEl all A) -> Provable A f.
Proof.
 induction A as [|a A]; simpl; intros f.

 unfold all_P_BothEl. simpl. rewrite all_nil_eq. 
 simpl.

 tauto.
 unfold all_P_BothEl. rewrite in_flat_map.
 intros [[gamma delta] [In_S In_a]].
 rewrite in_flat_map in In_a.
 destruct In_a as [a_f [In_a_g In_a_d]].
 rewrite (all_splits_correct (a::A) gamma delta) in In_S.
 rewrite <- In_S.
 destruct a_f; simpl in In_a_d; try tauto.
 (** eauto. *)
 apply (P_BothEl gamma delta a_f1 a_f2).
 apply all_sound. exact In_a_g.
 apply all_sound. exact In_a_d. 
Qed.

Definition all_P_ChooId all (A:Assumptions) :=
  let gamma_proves := all A in
  flat_map
  (fun f_a =>
     flat_map
     (fun f_b =>
      F_Choo f_a f_b :: nil 
     )
    gamma_proves)
  gamma_proves.

Lemma all_P_ChooId_sound:
 forall A f,
  In f (all_P_ChooId all A) -> Provable A f.
Proof.
 unfold all_P_ChooId.
 intros A f. 
 rewrite in_flat_map.
 intros [g [IN_all_splits IN_f_flat]].
 rewrite in_flat_map in IN_f_flat.
 destruct IN_f_flat as [g' [IN_allg IN_f_flat]].

 apply all_sound in IN_allg.
 apply all_sound in IN_all_splits.
 simpl in IN_f_flat.
 destruct IN_f_flat as [EQ|F]; try tauto.
 rewrite <- EQ in *; clear EQ f.
 eauto.
Qed.

Definition all_P_ChooEl1 all (A:Assumptions) :=
 let gamma_proves := all A in
 flat_map 
 (fun fChoo =>
  match fChoo with
  | F_Choo f_a f_b => f_a :: nil
  | _ => 
   nil
  end
  )
 gamma_proves.

Lemma all_P_ChooEl1_sound:
 forall A f,
  In f (all_P_ChooEl1 all A) -> Provable A f.
Proof.
 unfold all_P_ChooEl1.
 intros A f.
 rewrite in_flat_map.
 intros [g [IN_all_splits IN_f_match]].
 destruct g; simpl in IN_f_match; try tauto.
 destruct IN_f_match as [EQ|F]; try tauto.
 rewrite <- EQ in *; clear EQ f.
 eauto.
Qed.

Definition all_P_ChooEl2 all (A:Assumptions) :=
 let gamma_proves := all A in
 flat_map 
 (fun fChoo =>
  match fChoo with
  | F_Choo f_a f_b => f_b :: nil
  | _ => 
   nil
  end
  )
 gamma_proves.

Lemma all_P_ChooEl2_sound:
 forall A f,
  In f (all_P_ChooEl2 all A) -> Provable A f.
Proof.
 unfold all_P_ChooEl2.
 intros A f.
 rewrite in_flat_map.
 intros [g [IN_all_splits IN_f_match]].
 destruct g; simpl in IN_f_match; try tauto.
 destruct IN_f_match as [EQ|F]; try tauto.
 rewrite <- EQ in *; clear EQ f.
 eauto.
Qed.

Definition all_P_EithEl all (A:Assumptions) :=
  flat_map
  (fun gamma_delta:(Assumptions*Assumptions) =>
    let (gamma,delta) := gamma_delta in
    let gamma_proves := all gamma in
    flat_map
     (fun f =>
      match f with
      | F_Eith f_a f_b =>
        (** filter out all the c's that are in this env, use in_dec to prove it*)
        let delta_a_proves := (all (delta ++ ((A_Linear f_a) ::nil))) in
        let delta_b_proves := (all (delta ++ ((A_Linear f_b)::nil))) in
        flat_map 
         (fun f_c1 =>
          flat_map
           (fun f_c2 =>
             if Formula_eq_dec f_c1 f_c2 then
                f_c1::nil else nil)
           delta_b_proves)
         delta_a_proves
      | _ =>
        nil
      end)
     gamma_proves)
  (all_splits A).

Lemma all_P_EithEl_sound:
 forall A f,
  In f (all_P_EithEl all A) -> Provable A f.
Proof.
 unfold all_P_EithEl.
 intros A f.
 rewrite in_flat_map.
 intros [[gamma delta] [IN_all_splits IN_f_flat]].
 rewrite in_flat_map in IN_f_flat.
 destruct IN_f_flat as [fg [IN_allg IN_f_flat]].
 destruct fg; simpl in IN_f_flat; try tauto.
 rewrite in_flat_map in IN_f_flat.
 destruct IN_f_flat as [f_c1 [IN_allda IN_f_eq]].
 rewrite in_flat_map in IN_f_eq.
 destruct IN_f_eq as [f_c2 [IN_alldb IN_f_eq2]].
 destruct (Formula_eq_dec f_c1 f_c2); simpl in IN_f_eq2; try tauto. 
 destruct IN_f_eq2 as [EQ_f | F]; try tauto.
 rewrite EQ_f in *.
 rewrite <- e in *.
 apply all_splits_correct in IN_all_splits.
 rewrite <- IN_all_splits.
 eapply P_EithEl; eauto.
Qed. 
 





End all_cases.

Fixpoint all_theorems (n:nat) A :=
 match n with
 | O => nil
 | S n =>
  (all_P_L_Id A)
  ++ (all_P_I_Id A)
  ++ (all_P_Exc (all_theorems n) A)
  ++ (all_P_Contract (all_theorems n) A)
  ++ (all_P_Weaken (all_theorems n) A)
  ++ (all_P_OfCoId (all_theorems n) A)
  ++ (all_P_OfCoEl (all_theorems n) A)
  ++ (all_P_ImplEl (all_theorems n) A)
  ++ (all_P_BothId (all_theorems n) A)
  ++ (all_P_BothEl (all_theorems n) A)
  ++ (all_P_ChooId (all_theorems n) A)
  ++ (all_P_ChooEl1 (all_theorems n) A)
  ++ (all_P_ChooEl2 (all_theorems n) A)
  ++ (all_P_EithEl (all_theorems n) A)
  (* ++ one for each case *)
 end.

Theorem all_theorems_nil:
 forall n,
  all_theorems n nil = nil.
Proof.
 induction n as [|n]; simpl; try tauto.

 (* one for each case *)
 unfold all_P_OfCoEl. simpl. rewrite IHn.
 simpl. unfold all_P_Exc. simpl. rewrite IHn.
 unfold all_P_OfCoId. simpl. rewrite IHn. simpl.
 unfold all_P_ImplEl. simpl. rewrite IHn. simpl.
 unfold all_P_BothId. simpl. rewrite IHn. 
 unfold all_P_BothEl. simpl. rewrite IHn.
 unfold all_P_ChooId. simpl. rewrite IHn.
 unfold all_P_ChooEl1. simpl. rewrite IHn.
 unfold all_P_ChooEl2. simpl. rewrite IHn.
 unfold all_P_EithEl. simpl. rewrite IHn. simpl. tauto.
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
 rewrite in_app_iff.
 rewrite in_app_iff.
 rewrite in_app_iff.
 rewrite in_app_iff.
 rewrite in_app_iff.
 rewrite in_app_iff.
 rewrite in_app_iff.
 rewrite in_app_iff.
 rewrite in_app_iff.
 rewrite in_app_iff.
 rewrite in_app_iff.
 rewrite in_app_iff.
 intros [In_L_Id | [In_I_Id | [In_P_Exc | [In_P_Contract|[In_P_Weaken | [In_P_OfCoId |[In_P_OfCoEl| [In_P_ImplEl| [In_P_BothId| [In_P_BothEl| [In_P_ChooId| [In_P_ChooEl1| [In_P_ChooEl2 | In_P_EithEl]]]]]]]]]]]](*| one for each case *) ].
 apply all_P_L_Id_sound. exact In_L_Id.
 apply all_P_I_Id_sound. exact In_I_Id.
 apply (all_P_Exc_sound (all_theorems n)).
 apply all_theorems_nil.
 apply IHn.
 exact In_P_Exc.
 apply (all_P_Contract_sound (all_theorems n)).
 apply IHn.
 exact In_P_Contract.
 apply (all_P_Weaken_sound (all_theorems n)).
 apply IHn.
 apply In_P_Weaken.
 apply (all_P_OfCoId_sound (all_theorems n)).
 apply all_theorems_nil.
 apply IHn.
 exact In_P_OfCoId. 
 apply (all_P_OfCoEl_sound (all_theorems n)).
 apply all_theorems_nil.
 apply IHn.
 exact In_P_OfCoEl.
 apply (all_P_ImplEl_sound (all_theorems n)).
 apply IHn.
 exact In_P_ImplEl.
 apply (all_P_BothId_sound (all_theorems n)).
 apply IHn.
 exact In_P_BothId.
 apply (all_P_BothEl_sound (all_theorems n)).
 apply all_theorems_nil.
 apply IHn.
 exact In_P_BothEl.
 apply (all_P_ChooId_sound (all_theorems n)).
 apply IHn.
 exact In_P_ChooId.
 apply (all_P_ChooEl1_sound (all_theorems n)).
 apply IHn.
 exact In_P_ChooEl1.
 apply (all_P_ChooEl2_sound (all_theorems n)).
 apply IHn.
 exact In_P_ChooEl2.
 apply (all_P_EithEl_sound (all_theorems n)).
 apply IHn.
 exact In_P_EithEl.
Qed.

(* Completeness: *)
(* Provable -> In needs a bound *)

         
(** Theorem theorem_prover:
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

Check theorem_prover. *)

Extraction Language Ocaml.

Extract Constant Atom => "string".
Extract Constant Atom_eq_dec => "(=)".

Extract Constant Formula_eq_dec => "(=)".

Extract Inductive unit => "unit" [ "()" ].
Extract Inductive bool => "bool" [ "true" "false" ].
Extract Inductive sumbool => "bool" [ "true" "false" ].
Extract Inductive list => "list" [ "[]" "(::)" ].
Extract Inductive prod => "(*)"  [ "(,)" ].

(**
Extract Constant app => "set_app". <--- bad, unsound
Extract Constant map => "map".
Extract Constant forallb => "for_all".
**)

Extract Inductive nat => int [ "0" "succ" ]
  "(fun fO fS n -> if n=0 then fO () else fS (n-1))".

Set Extraction AccessOpaque.

Extraction "basic.ml" all_theorems.
