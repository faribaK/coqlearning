(* dummy context to set up H of the correct type, for testing it out *)
Lemma SomeName (term : Type) (P : term -> term -> Prop) :
  (forall x : term, ~ (exists (y : term), P x y /\ ~ P y x)) ->
  True. (* dummy goal *)
Proof.
  intro H.
  (* end dummy context *)
(* Here's the long version, with some explanations: *)

  (* this states the goal, result will be put into the context as H' *)
  assert (forall (x y : term), (P x y /\ ~ P y x) -> False) as H'.
    (* get rid of unneeded variables in context, get new args *)
    clear - H; intros x y Pxy.
    (* unfolding the not shows the computational structure of this *)
    unfold not at 1 in H.
    (* yay... (x, y, Pxy) will produce False via H *)
    (* specialize to x and apply... *)
    apply (H x).
    (* ...and provide the witness. *)
    exists y.  exact Pxy.
    (* done. *)

  (* let's do it again... *)
  clear H'.
(* you can also do it in a single statement: *)

  assert (forall x y, (P x y /\ ~ P y x) -> False) as H'.
    clear -H. intros x y Pxy. apply (H x (ex_intro _ y Pxy)).

  (* and again... *)
  clear H'.
(* simple stuff like this can also be written by hand: *)

  pose proof (fun x y Pxy => H x (ex_intro _ y Pxy)) as H'; simpl in H'.

 clear H; rename H' into H. apply I.

Qed.