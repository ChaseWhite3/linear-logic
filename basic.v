Variable Atom : Type.

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
   