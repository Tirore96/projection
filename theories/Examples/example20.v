From CoTypes Require Export coGlobal coLocal coProj.
From mathcomp Require Import all_ssreflect.
Require Import Paco.paco.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Example20.
Variables (a b c d: ptcp) (k k' : ch) (u : value).
Definition state0 := GRec (GMsg (Action a b k) u (GRec (GBranch (Action c d k') ((GVar 1) :: (GMsg (Action a b k) u (GVar 0))::nil)))).

Definition state1 := (GRec (GBranch (Action c d k') (state0 :: (GMsg (Action a b k) u (GVar 0)::nil)))).

Definition state2 := GMsg (Action a b k) u state1.

Lemma trans_01 : nth GEnd (nextg_unf state0) 0 = state1. 
Proof. done. Qed. 

Lemma trans_10 : nth GEnd (nextg_unf state1) 0 = state0. 
Proof. done. Qed. 

Lemma trans_12 : nth GEnd (nextg_unf state1) 1 = state2. 
Proof. done. Qed. 

Lemma trans_20 : nth GEnd (nextg_unf state2) 0 = state1. 
Proof. done. Qed. 
End Example20.


