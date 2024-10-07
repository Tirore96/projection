From CoTypes Require Export coGlobal coLocal coProj.
From mathcomp Require Import all_ssreflect.
Require Import Paco.paco.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Example5.
Variables (k : ch) (u : value).
Definition l := ERec (EMsg Sd k u (ERec (EVar 1))).
Definition lc_aux lc := ECMsg Sd k u lc.
CoFixpoint lc := lc_aux lc.

Lemma lc_eq : lc = lc_aux lc. 
Proof. rewrite /lc. rewrite {1}(ec_match (cofix ec := _ )). 
rewrite {1}/lc_aux. 
rewrite {2}/lc_aux. done. 
Qed. 

Lemma unravel_l_lc : lUnravel2 l lc.
Proof. 
pfold.
rewrite /l lc_eq.  con. con.
asimpl. left. 
pcofix CIH.
pfold. con. 
rewrite /l lc_eq. cbn. con.
right. done.
Qed. 
End Example5.


