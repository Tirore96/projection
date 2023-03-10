From CoTypes Require Export coGlobal coLocal coProj.
From mathcomp Require Import all_ssreflect.
Require Import Paco.paco.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(*Example 5*)
Section Example5.
Variables (a b c d: ptcp) (k k' : ch) (u : value).
Hypotheses (Hac : a <> c) (Had : a <> d).
Definition g := GRec (GMsg (Action a b k) u (GRec (GBranch (Action c d k') ((GVar 1) :: (GMsg (Action a b k) u (GVar 0))::nil)))).
Definition l := ERec (EMsg Sd k u (EVar 0)).
Definition gc_aux gc := GCMsg (Action a b k) u (GCBranch (Action c d k') (cocons gc (cocons gc conil ))). 
Definition gc_aux2 gc := GCMsg (Action a b k) u (GCBranch (Action c d k') ((to_coseq (gc :: gc ::nil)))).  
CoFixpoint gc := gc_aux gc. (*Coq allows definition with gc_aux, obviously productive, we need to use gc_aux2 because unravel judgment has branching rule expecting a list of shap (to_coseq (...)*)

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
Lemma gUnravel_iff_R : forall e ec R, paco2 gUnravel_gen R e ec <->  paco2 (UnfgUnravel \o gUnravel2_gen) R e ec. 
Proof. intros. split. 
move : e ec. pcofix CIH. 
intros. punfold H0.  induction H0. pclearbot. pfold.
constructor. rewrite /full_unf /=.  constructor. 
inv H. eauto. eauto. pfold. con. con. done. 
elim : gs gcs H H0. case=>//=. intros.  
destruct gcs;try done. inv H1. con. 
inv H4;auto. ssa. 
punfold IHgUnravel_gen. inv IHgUnravel_gen. pfold. con. 
rewrite full_unf_subst. done. 
pfold. con.  con.
intros. 
move : e ec H.  pcofix CIH. intros. punfold H0. inv H0. 
inv H. apply/gUnravel_unf6. rewrite -H1. pfold. constructor.
inv H2;auto. 
apply/gUnravel_unf6. rewrite -H1. pfold. constructor. done. 
induction H3;auto. con;eauto.  inv H3;eauto. 
apply/gUnravel_unf6. rewrite -H2. pfold. constructor. 
Qed.


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

End Example5.


Section Example19.
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
End Example19.


Section Example22.
Definition Unravels g := gUnravel g (gtocoind g).
Lemma decide_Unravels : forall g, Unravels g <-> next_rec nil has_treeP (fun _ => true) g.
Proof. intros. rewrite /Unravels.  rewrite next_recP //=. Qed.
End Example22.

Require Import Projection.projectDecide.
Section Example25.
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
End Example25.
