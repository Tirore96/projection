From CoTypes Require Export coGlobal coLocal coProj.
From mathcomp Require Import all_ssreflect.
Require Import Paco.paco.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Example5.
Variables (r s: ptcp) (k : ch).
Hypotheses (Hrs : r <> s).
Definition g := GRec (GBranch (Action r s k) ((GVar 0) :: GEnd :: nil)).  
Definition gc_aux gc := GCBranch (Action r s k) ((cocons gc (cocons GCEnd conil ))). 
Definition gc_aux2 gc := GCBranch (Action r s k) (to_coseq (gc :: GCEnd :: nil)).  
CoFixpoint gc := gc_aux gc. (*Coq allows definition with gc_aux, it has to be obviously productive, we need to use gc_aux2 because unravel judgment has branching rule expecting a list of shap (to_coseq (...)*)

Lemma gc_aux_aux2 : gc_aux = gc_aux2.
Proof. fext. intros. rewrite /gc_aux /gc_aux2. 
rewrite !utils.coeq. done. 
Qed. 

Lemma gc_eq : gc = gc_aux gc. 
Proof. rewrite /gc. rewrite {1}(gc_match (cofix gc := _)).
rewrite {1}/gc_aux. 
rewrite {3}/gc_aux.  done. 
Qed. 

Lemma unravel_g_gc : gUnravel g gc.
Proof.
pcofix CIH.
pfold. con. pfold_reverse.
apply/gUnravel_iff_R.
pcofix CIH.
rewrite /g gc_eq gc_aux_aux2 /gc_aux2.
pfold. con. cbn. con. done. con. 
right. apply/CIH. con. simpl. 
left. pfold. con. con. con. 
Qed.
End Example5. 
