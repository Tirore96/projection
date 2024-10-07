From CoTypes Require Export coGlobal coLocal coProj.
From mathcomp Require Import all_ssreflect.
Require Import Paco.paco.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Example2.
Variables (p q r s: ptcp) (k k' : ch) (u : value).
Hypotheses (Hac : p <> r) (Had : p <> s).
Definition g := GRec (GMsg (Action p q k) u (GRec (GBranch (Action r s k') ((GVar 1) :: (GMsg (Action p q k) u (GVar 0))::nil)))).
Definition l := ERec (EMsg Sd k u (ERec (EVar 1))).
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

Definition lc_aux lc := ECMsg Sd k u lc.
CoFixpoint lc := lc_aux lc.

Lemma lc_eq : lc = lc_aux lc. 
Proof. rewrite /lc. rewrite {1}(ec_match (cofix ec := _ )). 
rewrite {1}/lc_aux. 
rewrite {2}/lc_aux. done. 
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

Lemma Project_example : CProject gc p lc.
Proof.
pcofix CIH. 
rewrite gc_eq lc_eq.
pfold. con. rewrite /comp_dir /= eqxx //=. left. 
pfold. rewrite lc_eq. rewrite /lc_aux. econstructor. 
rewrite /comp_dir /=. have : p == r = false. apply/eqP=>//=. move =>->.
have : p == s = false. apply/eqP=>//=. move=>->. done. 
simpl. auto. 
intros. simpl in H. destruct H;subst. 
- ssa. rewrite gc_eq /gc_aux. con. rewrite /comp_dir /= eqxx //=.  
  right. rewrite lc_eq in CIH. done. 
- destruct H;try done. subst. ssa. rewrite gc_eq /gc_aux. con. rewrite /comp_dir /= eqxx //=.  
  right. rewrite lc_eq in CIH. done. 
Qed. 
End Example2.


