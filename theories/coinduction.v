From epit Require Export cats.
From Coinduction Require Export all.

Arguments Datatypes.id {_} _/.
Instance rw_leq {X} {L: CompleteLattice X}: RewriteRelation (@leq X L) := {}.

Notation "x" := (elem x) (at level 2, only printing). 
