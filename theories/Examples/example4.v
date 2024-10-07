From CoTypes Require Export coGlobal coLocal coProj.
From mathcomp Require Import all_ssreflect.
Require Import Paco.paco.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Example4.
Variables (p q r s: ptcp) (k k' : ch) (u : value).
Definition g := GRec (GMsg (Action p q k) u (GRec (GBranch (Action r s k') ((GVar 1) :: (GMsg (Action p q k) u (GVar 0))::nil)))).

Definition gc_aux gc := GCMsg (Action p q k) u (GCBranch (Action r s k') (cocons gc (cocons gc conil ))). 

(*Coq allows definition with gc_aux, it has to be obviously productive, we need to use gc_aux2 because unravel judgment has branching rule expecting a list of shap (to_coseq (...)*)
Definition gc_aux2 gc := GCMsg (Action p q k) u (GCBranch (Action r s k') ((to_coseq (gc :: gc ::nil)))).  
CoFixpoint gc := gc_aux gc.

Lemma gc_eq_aux : gc = gc_aux gc. 
Proof. rewrite /gc. rewrite {1}(gc_match (cofix gc := _)).
rewrite {1}/gc_aux. 
rewrite {3}/gc_aux.  done. 
Qed.

Lemma gc_eq_aux2 : gc_aux = gc_aux2.
Proof. fext. intros. rewrite /gc_aux /gc_aux2. 
rewrite !utils.coeq. done. 
Qed.  

Lemma gc_eq : gc = gc_aux2 gc. 
Proof. rewrite {1}gc_eq_aux. rewrite -gc_eq_aux2 //.
Qed.

Lemma unravel_g_gc : gUnravel2 g gc.
Proof.
pcofix CIH.
rewrite /g gc_eq.
pfold. con.
cbn. con.
left. pcofix CIH2.
pfold. con. cbn. con. ssa.
con. right. done.
con. left. pfold. con. cbn. 
rewrite gc_eq. con. right. done.
con.
Qed.
End Example4.


