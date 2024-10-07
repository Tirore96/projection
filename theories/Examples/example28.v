From CoTypes Require Export coGlobal coLocal coProj.
From mathcomp Require Import all_ssreflect.
Require Import Paco.paco.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import Projection.projectDecide.

Section Example28.
Variables (a b c d: ptcp) (k k' : ch) (u u' : value).
Hypotheses (Hca : c <> a) (Hcb : c <> b).
Definition g0 := GMsg (Action a b k) u (GMsg (Action c d k) u' GEnd).
Definition l0 := EMsg Sd k u' EEnd. 
Definition pair_state0 := (g0,l0).

Definition g1 := (GMsg (Action c d k) u' GEnd).
Definition pair_state1 := (g1,l0).

Definition pair_state2 := (GEnd,EEnd).

Lemma pair_trans_01 : nth (GEnd,EEnd) (nextge_unf c pair_state0) 0 = pair_state1. 
Proof. cbn. rewrite /comp_dir /=. 
have : c == a = false. apply/eqP=>//=. move=>->. 
have : c == b = false. apply/eqP=>//=. move=>->. simpl. done.
Qed.

Lemma pair_trans_12 : nth (GEnd,EEnd) (nextge_unf c pair_state1) 0 = pair_state2. 
Proof. cbn. rewrite /comp_dir /= eqxx //=. Qed. 
End Example28.
