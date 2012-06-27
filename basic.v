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

Require Import Lists.
Open Scope list_scope.

Inductive Provable : Assumptions -> Formula -> Prop :=
| P_L_Id    : forall A,
  Provable ((A_Linear A)::nil) A
| P_I_Id    : forall A,
  Provable ((A_Intuit A)::nil) A
| P_Exc     : forall (Gamma Delta:Assumptions) (A: Formula),
  Provable (Gamma++Delta) A -> Provable (Delta ++ Gamma ) A
| P_contract: forall (Gamma:Assumptions) (A B:Formula),
  Provable (Gamma ++ (A_Intuit A)::(A_Intuit A)::nil) B ->
            Provable (Gamma ++ (A_Intuit A)::nil) B
| P_Weaken  : forall (Gamma:Assumptions) (A B: Formula),
  Provable Gamma B -> Provable (Gamma++(A_Intuit A)::nil) B
(**This Gamma needs to be soley intuit assumptions*)
| P_OfCoId  : forall (Gamma:Assumptions) (A : Formula),
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

 

Section Example.
 Variable A : Atom.

 Theorem simple_linear_assumption :
  Provable ((A_Linear (F_Atom A))::nil) (F_Atom A).
 Proof.
  apply P_L_Id.
 Qed.
End Example.

Theorem theorem_prover:
 forall A F,
  { Provable A F } + { ~ Provable A F }.
Proof.
Admitted.

Check theorem_prover.

-----------


Inductive llProp : Type :=
  | linear : llProp
  | intuit : llProp.


Inductive ll : list llProp -> list llProp -> Prop :=
  | linearid : forall A, ll [(linear A)] [A]
  | intuitid : forall A, ll [(intuit A)] [A]
  | exchange : forall Delta Gamma A, ll (Gamma ++ Delta) [A] -> ll (Delta ++ Gamma) [A]
  | contract : forall Gamma A B, 
	ll (Gamma ++[(intuit A),(intuit A)]) [B] -> ll (Gamma ++ [intuit A]) [B]
  | weaken   : forall Gamma B , ll Gamma [B] -> ll (Gamma ++ [intuit A]) [B] 
  | lollypopIden : ll -> ll  Variable Atom : Type.

Inductive Formula : Type :=
| F_Atom : Atom -> Formula
| F_Imples : Formula -> Formula -> Formula.

Inductive Assumption : Type :=
| A_Linear : Formula -> Assumption
| A_Intuit : Formula -> Assumption.

Definition Assumptions := list Assumption.

Require Import Lists.
Open Scope list_scope.

Inductive Provable : Assumptions -> Formula -> Prop :=
| P_L_Id : forall A,
  Provable ((A_Linear A)::nil) A
| P_I_Id : forall A,
  Provable ((A_Intuit A)::nil) A.

Section Example.
 Variable A : Atom.

 Theorem ex :
  Provable ((A_Linear (F_Atom A))::nil) (F_Atom A).
 Proof.
  apply P_L_Id.
 Qed.
End Example.

Theorem theorem_prover:
 forall A F,
  { Provable A F } + { ~ Provable A F }.
Proof.
Admitted.

Check theorem_prover.

-----------


Inductive llProp : Type :=
  | linear : llProp
  | intuit : llProp.


Inductive ll : list llProp -> list llProp -> Prop :=
  | linearid : forall A, ll [(linear A)] [A]
  | intuitid : forall A, ll [(intuit A)] [A]
  | exchange : forall Delta Gamma A, ll (Gamma ++ Delta) [A] -> ll (Delta ++ Gamma) [A]
  | contract : forall Gamma A B, 
	ll (Gamma ++[(intuit A),(intuit A)]) [B] -> ll (Gamma ++ [intuit A]) [B]
  | weaken   : forall Gamma B , ll Gamma [B] -> ll (Gamma ++ [intuit A]) [B] 
  | lollypopIden : ll -> ll  
   