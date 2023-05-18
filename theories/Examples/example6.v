From CoTypes Require Export coGlobal coLocal coProj.
From mathcomp Require Import all_ssreflect.
Require Import Paco.paco.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Example6.
Variables (a b c d: ptcp) (k k' : ch) (u : value).
Hypotheses (Hac : a <> c) (Had : a <> d).
Definition g := GRec (GMsg (Action a b k) u (GRec (GBranch (Action c d k') ((GVar 1) :: (GMsg (Action a b k) u (GVar 0))::nil)))).
Definition l := ERec (EMsg Sd k u (EVar 0)).
Definition gc_aux gc := GCMsg (Action a b k) u (GCBranch (Action c d k') (cocons gc (cocons gc conil ))). 
Definition gc_aux2 gc := GCMsg (Action a b k) u (GCBranch (Action c d k') ((to_coseq (gc :: gc ::nil)))).  
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

Definition lc_aux lc := ECMsg Sd k u lc.
CoFixpoint lc := lc_aux lc.
Lemma lc_eq : lc = lc_aux lc. 
Proof. rewrite /lc. rewrite {1}(ec_match (cofix ec := _ )). 
rewrite {1}/lc_aux. 
rewrite {2}/lc_aux. done. 
Qed. 
Print gUnravel. Print gUnravel2. 



Lemma unravel_g_gc : gUnravel g gc.
Proof.
pcofix CIH.
pfold. con. pfold_reverse.
apply/gUnravel_iff_R.
pcofix CIH.
rewrite /g gc_eq gc_aux_aux2 /gc_aux2.
pfold. con. cbn. con. left. 
pfold. con. cbn. con. ssa. 
con. 
- simpl. right. apply/CIH. 
- con;try done. right. apply/CIH0. 
Qed.

Lemma unravel_l_lc : lUnravel l lc.
Proof. 
rewrite /l lc_eq. pcofix CIH. pfold. con. simpl. 
con. rewrite lc_eq. auto. 
Qed. 

Lemma Project_example : CProject gc a lc.
Proof.
pcofix CIH. 
rewrite gc_eq gc_aux_aux2 lc_eq.
pfold. con. rewrite /comp_dir /= eqxx //=. left. 
pfold. rewrite lc_eq. rewrite /lc_aux. econstructor. 
rewrite /comp_dir /=. have : a == c = false. apply/eqP=>//=. move =>->.
have : a == d = false. apply/eqP=>//=. move=>->. done. 
simpl. auto. 
intros. simpl in H. destruct H;subst. 
- ssa. rewrite gc_eq /gc_aux. con. rewrite /comp_dir /= eqxx //=.  
  right. rewrite lc_eq in CIH. done. 
- destruct H;try done. subst. ssa. rewrite gc_eq /gc_aux. con. rewrite /comp_dir /= eqxx //=.  
  right. rewrite lc_eq in CIH. done. 
Qed. 

End Example6.


