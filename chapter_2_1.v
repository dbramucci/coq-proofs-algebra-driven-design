Axiom Tile : Type.

Axiom haskell : Tile.
Axiom sandy : Tile.
Axiom cw : Tile -> Tile.


Axiom cw'cw'cw'cw :
  forall t : Tile,
    cw (cw (cw (cw t))) = t.

Axiom ccw : Tile -> Tile.

Axiom ccw'cw :
  forall t : Tile,
    ccw (cw t) = t.

Axiom cw'ccw :
  forall t : Tile,
    cw (ccw t) = t.

Theorem ccw_is_redundant :
  forall t : Tile,
    ccw t = cw (cw (cw t)).
Proof.
intros.
symmetry.
rewrite <- cw'cw'cw'cw.
rewrite cw'ccw.
reflexivity.
Qed.

Axiom flipH : Tile -> Tile.

Axiom flipH'flipH :
  forall t : Tile,
    flipH (flipH t) = t.

Axiom flipH'cw'cw'flipH :
  forall t : Tile,
    flipH (cw (cw (flipH t))) = cw (cw t).

(* I need to define repeated composition *)
Fixpoint repeat_compose {a : Type}
  (n : nat) (f : a -> a) (x : a) := 
match n with
| 0 => x
| S n => f (repeat_compose n f x)
end.
(* And give it the same ^ notation from the book *)
Notation "f ^ n" := (repeat_compose n f).

Theorem flipH_2ncw_flipH :
  forall (n : nat) (t : Tile),
    flipH ((cw^(n*2)) (flipH t)) = (cw^(n*2)) t.
Proof.
intros.
induction n.
simpl.
rewrite flipH'flipH.
reflexivity.
simpl.
rewrite <- IHn.
symmetry.
rewrite <- flipH'cw'cw'flipH.
rewrite flipH'flipH.
reflexivity.
Qed.

Axiom x_symmetry :
  forall t : Tile,
    flipH (cw t) = ccw (flipH t).

Axiom flipV : Tile -> Tile.

(*
Axiom flipV'flipV :
  forall t : Tile,
    flipV (flipV t) = t.
*)

Axiom ccw'flipH'cw :
  forall t : Tile,
    flipV t = ccw (flipH (cw t)).

(*
Axiom flipV'flipH :
  forall t : Tile,
    flipV (flipH t) = cw (cw t).
*)

Theorem flipV'flipV :
  forall t : Tile,
    flipV (flipV t) = t.
Proof.
intros.
symmetry.
rewrite ccw'flipH'cw.
rewrite ccw'flipH'cw.
rewrite cw'ccw.
rewrite flipH'flipH.
rewrite ccw'cw.
reflexivity.
Qed.



Theorem flipV'flipH :
  forall t : Tile,
    flipV (flipH t) = cw (cw t).
Proof.
intros.
rewrite ccw'flipH'cw.
rewrite <- flipH'cw'cw'flipH.
rewrite <- x_symmetry.
reflexivity.
Qed.