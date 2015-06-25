Require Import universe_comparator.universe_comparator.

Set Printing Universes.

Universes i j.

Monomorphic Definition X : Type@{i} := Type@{j}.

(*

Print X.

X = Type@{j}
     : Type@{i}
(*  |= j < i
        *)

*)

(**

Universe variables in X are global (X is not universe polymorphic). Therefore, 'Compare Universes "i" ? "j"' will output 'Inferred relation: i > j'.

*)

Compare Universes "i" ? "j".

Polymorphic Definition PLX : Type := Type.

(*
Print PLX.

Polymorphic PLX = 
Type@{Top.4}
     : Type@{Top.3}
(* Top.3
   Top.4 |= Top.4 < Top.3
             *)

*)

(**

Universe variables in PLX are local (PLX is universe polymorphic). Therefore, 'Compare Universes "Top.3" ? "Top.4"' will output 'Top.3 and Top.4 are not related'.

*)

Compare Universes "Top.3" ? "Top.4".

(**

In this case, one can use 'Compare Universes "Top.3" ? "Top.4" Of PLX' which will output 'Inferred relation: Top.3 > Top.4'

*)

Compare Universes "Top.3" ? "Top.4" Of PLX.

(**

One can also ask if a particular relation holds within the global or local constraints.

Note that universe levels generated internally by Coq, e.g. "Top.3" above, are not fixed and can change. A better way to compare universe levels in a more consistent way is to use declared universe variables, e.g., "x" and "y" below. 

*)

Universe x y.

Polymorphic Definition W := PLX@{x y}.

(**

Here we have bound universe variables of PLX to "x" and "y" in the context of definition W. Therefore, 'Compare Universes "x" ? "y" Of W' now outputs 'Inferred relation: x > y'.

*)

Compare Universes "x" ? "y" Of W.

(**

Compare Universes (acting both globally and locally) can also take into account a relation and check if that relation holds.

The following is a table of commands and their outputs:

#
<table>
<tr> <th>Commad</th> <th>Result</th> </tr>
<tr> <td>Compare Universes "x" < "y" Of W.</td> <td>Doesn't hold because: x > y</td> </tr>
<tr> <td>Compare Universes "x" <= "y" Of W.</td> <td>Doesn't hold because: x > y</td> </tr>
<tr> <td>Compare Universes "x" = "y" Of W.</td> <td>Doesn't hold because: x > y</td> </tr>
<tr> <td>Compare Universes "x" > "y" Of W.</td> <td>Holds: x > y</td> </tr>
<tr> <td>Compare Universes "x" >= "y" Of W.</td> <td>Holds because: x > y</td> </tr>
</table>
#
*)

(*
 ===================================================================
|          Command                   ||         Result              |
|-------------------------------------------------------------------|
| Compare Universes "x" < "y" Of W.  || Doesn't hold because: x > y |
|-------------------------------------------------------------------|
| Compare Universes "x" <= "y" Of W. || Doesn't hold because: x > y |
|-------------------------------------------------------------------|
| Compare Universes "x" = "y" Of W.  || Doesn't hold because: x > y |
|-------------------------------------------------------------------|
| Compare Universes "x" > "y" Of W.  || Holds: x > y                |
|-------------------------------------------------------------------|
| Compare Universes "x" >= "y" Of W. || Doesn't hold because: x > y |
 ===================================================================

 *)

Compare Universes "x" < "y" Of W.
Compare Universes "x" <= "y" Of W.
Compare Universes "x" = "y" Of W.
Compare Universes "x" > "y" Of W.
Compare Universes "x" >= "y" Of W.
