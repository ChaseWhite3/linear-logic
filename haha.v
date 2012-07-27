Require Import List.
Open Scope list_scope.

Check pair.

Check cons.



Fixpoint all_splits {X:Type} (a: list X) : list ((list X)*(list X)) :=
 (nil,a) :: match a with
  | nil => nil
  | f :: t => map (fun p => match p with 
			     |(x,y) => ((f :: x),y)
                            end)
                        (all_splits t)
 end.

Fixpoint all_splits_two {X:Type} (a: list X) (b : list X) : list ((list X)*(list X)):=
 match b with
  | nil => (a, nil)::nil
  | f::t => (a, b):: (all_splits_two (a++(f::nil)) t)
 end.
 


Eval simpl in (all_splits (1::nil)).

Eval simpl in (all_splits (1::2::3::4::nil)).

Theorem equiv_split : forall {X:Type} (l a b: list X) ,
 In (a,b) (all_splits l) <-> a++b = l.
Proof.
 induction l as [|e l]; intros a b; simpl; split; intros H.
 (** nil case *)
 inversion H. inversion H0. simpl. reflexivity. inversion H0. left. SearchAbout app.  
 apply app_eq_nil in H. inversion H. rewrite H0. rewrite H1. reflexivity.
 (** inductive case *)
 (** SearchAbout In. apply in_inv. *)
 
 

 
 inversion H. inversion H0. simpl. reflexivity. SearchAbout In. clear H. apply in_map_iff in H0.
 inversion H0. inversion H. clear H H0. destruct x. apply IHl in H2. inversion H1. rewrite <-H3.
 rewrite <-H2. reflexivity. 
 (**  *)
 rewrite in_map_iff. destruct a. left. simpl in H. rewrite H. auto. right. exists (a,b). split.
 inversion H. auto. apply IHl. inversion H. auto. Qed.
 

 (**Focus 3. SearchAbout In. in_map (In x l) found on right side of assumption*)
 
 