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
 


(** Theorem nil_split_or_false : *)
 


Eval simpl in (all_splits (1::nil)).

Eval simpl in (all_splits (1::2::3::4::nil)).

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

Theorem sublist_Proof : forall {X:Type} (l : list X) ,
 {sl | forall a b, In (a,b) sl <-> a++b = l}.
Proof.
 induction l as [|e l]. exists (cons (nil, nil) nil). intros a b. simpl. split.
 intros. inversion H. inversion H0. auto. inversion H0. intros. left.
 apply app_eq_nil in H.  inversion H.  rewrite H0.  rewrite H1. auto.
 (** inductive case *)
 destruct IHl. exists ((nil,e::l) :: (map (fun p => match p with
                                     | (x, y) => ((e :: x), y)
                                     end)
                           x)).
 intros a b. split. intros. SearchAbout In. apply in_inv in H. inversion H. inversion H0. auto.
 
 apply in_map_iff in H0. inversion H0. destruct x0. inversion H1. inversion H2. apply i in H3.
 rewrite <- H3. rewrite <- H6. reflexivity.


 intros.
 apply in_or_app with (l:=(nil,e::l)::nil) 
                      (a:= (a,b)) 
                      (m:= map (fun p : list X * list X => let (x0, y) := p in (e :: x0, y)) x). 
 destruct a. left. SearchAbout In. simpl. left. simpl in H. rewrite H. auto.
 
 right. rewrite in_map_iff. exists (a,b). inversion H. split. auto. rewrite i. apply H2. Qed.
  
  

 