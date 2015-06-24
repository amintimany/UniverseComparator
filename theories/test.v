Require Import universe_comparator.universe_comparator.

Definition X : Type := Type.

Set Printing Universes.

Print X.

(*

X = Type@{Top.2}
     : Type@{Top.1}
(* Top.1
   Top.2 |= Top.2 < Top.1
 *)

*)

Module M.

Definition XX : Type := Type.
  
Universe m1 m2.

End M.

Print M.XX.

(*

M.XX = Type@{Top.4}
     : Type@{Top.3}
(* Top.3
   Top.4 |= Top.4 < Top.3
             *)

*)

Universe x y.

Constraint x <= y.

Print Universes.

Compare Universes "x" ? "y".

Compare Universes "Top.3" = "Top.4".