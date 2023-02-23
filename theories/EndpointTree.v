From mathcomp Require Import all_ssreflect zify.

From Proj Require Import Syntax Elimination Utils.
Require Import Paco.paco.

Check upaco2. 
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


Definition eunf g := if g is ERec g' then g' [e g.:EVar]  else g.



Lemma emu_height_ren : forall g sigma, emu_height g ⟨e sigma ⟩  = emu_height g.
Proof.
elim;rewrite /=;try done;intros.
f_equal. apply : H. 
Qed.

Lemma emu_height_subst : forall g0 sigma, (forall n, ~~ eguarded n g0 -> emu_height (sigma n) = 0) ->  emu_height (g0[e sigma]) = emu_height g0.
Proof. 
elim; try solve [by rewrite /=];intros.
asimpl. move : (H n). destruct (emu_height (sigma n)) eqn:Heqn. done. have : 0 < n0.+1 by lia. move => + HH. simpl. 
simpl in HH. lia. 
simpl. f_equal. asimpl. apply H. case. done.  simpl. intros. asimpl. rewrite emu_height_ren. apply/H0. done. 
Qed.


Lemma emu_height_unf : forall g , eguarded 0 g -> (emu_height g) = emu_height (g [e ERec g .: EVar]).
Proof.
move => g. rewrite /=. case : g; try solve [intros;rewrite /=;done].
intros. rewrite /=. destruct n. done. done. ssa. erewrite emu_height_subst. done. case. done. 
intros. simpl. asimpl. destruct n. lia.  simpl. done. 
Qed.

Lemma emu_height_unf2 : forall g sigma i, ~~ eguarded i g -> (emu_height g) + emu_height (sigma i) = emu_height (g [e sigma]).
Proof. 
elim;rewrite //=;intros. have : n = i by lia.  intros. subst. lia. 
asimpl. erewrite <- H. 2 : { eauto. } simpl. asimpl. rewrite emu_height_ren. lia. 
Qed.


Lemma eguarded_test : forall e sigma i,  ~~ eguarded i e -> iter (emu_height e) eunf e [ sigma ] = sigma i. 
Proof. 
elim;rewrite //=;intros. 
have : n = i. lia.  move=>->. done.  asimpl. rewrite -iterS iterSr. simpl. asimpl. erewrite H. 
2 : { eauto. } simpl. done. 
Qed.


Definition full_eunf g := (iter (emu_height g) eunf g).

(*Even non contractive terms have the property that full unfolding equals full unfolding plus 1. This is what we need in projection lemma
 so we don't have to derive contractiveness of e from projection derivation*)
Lemma full_eunf_subst : forall e, full_eunf (ERec e) = full_eunf (e [e ERec e .: EVar]). 
Proof. 
intros. rewrite /full_eunf. 
intros. simpl.  rewrite -iterS iterSr. simpl. 
destruct (eguarded 0 e) eqn:Heqn.  rewrite emu_height_unf. done. done. 
 erewrite eguarded_test.  2 : { lia. } 
simpl. 
erewrite <-emu_height_unf2. 2 : { lia.  } simpl. 
rewrite addnC.  
rewrite iterD. erewrite eguarded_test. 2 : { lia.  } simpl. rewrite -iterS iterSr /=. 
erewrite eguarded_test. 2 : { lia. } done. 
Qed.




Lemma full_eunf2 : forall n e, full_eunf (iter n eunf e) = full_eunf e. 
Proof. 
elim. done. 
intros. rewrite iterS. 
destruct (if (iter n eunf e) is ERec _ then true else false) eqn:Heqn. 
destruct ((iter n eunf e))eqn:Heqn2;try done. simpl. 
rewrite -(H e) Heqn2. rewrite full_eunf_subst. done. 
have : eunf (iter n eunf e) = iter n eunf e. destruct ((iter n eunf e));try done. 
move=>->. rewrite H. done. 
Qed.


Lemma full_eunf_idemp : idemp full_eunf. 
Proof. 
intros. rewrite /idemp. intros. rewrite {2}/full_eunf. rewrite full_eunf2. done. 
Qed.




(*
Fixpoint muv n g := 
match g with 
| ERec g0 => muv n.+1 g0
| EVar n0 => n == n0
| _ => false 
end. 

Lemma not_eguarded_muv : forall g n, ~~ eguarded n g -> muv n g. 
Proof. 
elim=>//=;intros; solve [ lia | auto].   
Qed.


Lemma not_eguarded_muv2 : forall g n,  muv n g -> ~~ eguarded n g.
Proof. 
elim=>//=;intros; solve [ lia | auto].   
Qed.


Lemma muv_uniq : forall g n0 n1, muv n0 g -> muv n1 g -> n0 = n1. 
Proof. 
elim=>//=. 
intros. lia. 
intros. suff : n0.+1 = n1.+1.  lia. apply/H=>//=. 
Qed.

Lemma muv_ren : forall g n sigma, muv n g -> muv (sigma n) g ⟨e sigma ⟩.
Proof. simpl. 
elim=>//=;intros. 
move/eqP : H=>Heq. subst=>//=. 
asimpl. apply (@H _  (0 .: sigma >> succn)) in H0. 
move : H0. asimpl=>//=. 
Qed.



Lemma muv_subst : forall g n n0 sigma, muv n (sigma n0) -> muv n0 g -> muv n g[e sigma].
Proof. simpl. 
elim=>//=;intros. 
move/eqP : H0=>Heq. subst=>//=. 
asimpl. apply/H;eauto. asimpl.  apply (@muv_ren _ _ succn) in H0. 
done. 
Qed.

Lemma muv_unf : forall g n, muv n g -> full_eunf g = EVar n. 
Proof. 
intros. rewrite /full_eunf. remember (emu_height g). 
move : n0 g Heqn0 H.  
elim=>//=. case=>//=. intros. f_equal=>//=. lia. 
intros. 
destruct g;try done. simpl in Heqn0.
rewrite -iterS iterSr /=. rewrite H. done. 
rewrite emu_height_subst. inv Heqn0=>//=. 
case. 
simpl. move/not_eguarded_muv=>Hm. simpl in H0. have : 0 = n.+1. 
apply/muv_uniq;eauto. done. 
done. 
simpl in *. apply/muv_subst;eauto. simpl. done. 
Qed.

Lemma var_muv  : forall g n, g = EVar n -> muv n g. 
Proof.
case=>//=. intros. inv H. done. 
Qed.*)

Lemma unf_eguarded  : forall g n, eguarded n g  -> eunf g <> EVar n.  
Proof. 
case=>//=. intros. move => HH. inv HH. lia. 
intros. destruct e;try done.   move : H. 
asimpl. destruct n0. done. asimpl. case. simpl. intros. move=> HH.  inv HH. lia. 
Qed.


Lemma eguarded_ren : forall g n sigma, injective sigma ->  eguarded n g -> eguarded (sigma n) (g ⟨e sigma ⟩).
Proof. 
elim=>//=;intros. apply/eqP. move => HH.  apply H in HH. lia. 
move : H1. asimpl. intros.
have : injective (0 .: sigma >> succn). eauto.  
move/H. move/(_ n.+1).  asimpl. eauto. 
Qed. 

Lemma eguarded_ren2 : forall g n sigma, eguarded (sigma n) (g ⟨e sigma ⟩) -> eguarded n g.
Proof. 
elim=>//=;intros. apply/eqP. move => HH.  apply/negP. apply/H. apply/eqP. f_equal. done. 
apply/H.
instantiate (1 := (0 .: sigma >> succn)). asimpl. done. 
Qed. 

Lemma eguarded_ren_iff : forall g n sigma, injective sigma ->  eguarded n g <-> eguarded (sigma n) (g ⟨e sigma ⟩).
Proof. intros. split;intros. apply/eguarded_ren;eauto. apply/eguarded_ren2. eauto. 
Qed. 

Lemma eguarded_subst : forall g n sigma , (forall n0, eguarded n0 g = false  -> eguarded n (sigma n0)) -> eguarded n (g [e sigma]). 
Proof. 
elim=>//=;intros. apply/H. lia. 
move : H0.  asimpl. intros. 

apply/H.  ssa. 
destruct n0;try done. asimpl. apply/eguarded_ren. done. eauto. 
Qed. 


Lemma eguarded_subst2 : forall g n n0 sigma ,  eguarded n (g [e sigma]) ->  eguarded n (sigma n0) = false -> eguarded n0 g. 
Proof. 
elim=>//=;intros. destruct (eqVneq n n1);try done. subst. rewrite H0 in H. done. 
move/H : H0. asimpl. move/(_ n0.+1). asimpl.
move => HH. apply HH. apply/negP=> HH2. apply/negP. move : H1. move/negP/negP. eauto. 
apply eguarded_ren2 in HH2. eauto. 
Qed. 

(*Lemma eguarded_subst2 : forall g n n0 sigma ,  eguarded n (g [e sigma]) ->  eguarded n0 g = false  -> eguarded n (sigma n0). 
Proof. 
elim=>//=;intros. have : n = n1 by lia. move=><-. done.
move/H : H0. asimpl. move/(_ n0.+1). move/(_ H1). asimpl. 
move/eguarded_ren2. done. 
Qed. *)


Lemma eguarded_eunf  : forall g n, eguarded n g -> eguarded n (eunf g).
Proof. 
case=>//=;intros.
apply/eguarded_subst. 
ssa. destruct n0;try done. simpl. destruct (eqVneq n0 n). subst. lia. done. 
Qed.

Lemma eguarded_eunf2  : forall g n, eguarded n (eunf g) -> eguarded n g.
Proof. 
case=>//=;intros.
eapply eguarded_subst2 in H. eauto. asimpl. simpl. lia. 
Qed.


Lemma eguarded_iter_unf : forall n0 g n,  eguarded n g -> eguarded n (iter n0 eunf g).
Proof. 
elim. case => //=. 
intros. simpl. apply/eguarded_eunf. eauto. 
Qed.

Lemma eguarded_iter_unf2 : forall n0 g n,  eguarded n (iter n0 eunf g) -> eguarded n g.
Proof. 
elim. case => //=. 
intros. simpl. rewrite iterSr in H0.  apply/eguarded_eunf2. eauto. 
Qed.


Lemma eguarded_full_unf : forall e n, eguarded n e -> eguarded n (full_eunf e). 
Proof. 
intros. rewrite /full_eunf. remember (emu_height e). clear Heqn0.  apply/eguarded_iter_unf. done. 
Qed.

Lemma eguarded_full_unf2 : forall e n, eguarded n (full_eunf e) -> eguarded n e. 
Proof. 
intros. rewrite /full_eunf. remember (emu_height e). clear Heqn0.  apply/eguarded_iter_unf2. eauto. 
Qed.


Lemma iter_unf_eguarded  : forall n0 n g, eguarded n g ->  iter n0 eunf g <> EVar n.
Proof. 
elim;intros.
simpl in H. subst. simpl. destruct g;try done. simpl in H. move=> HH. inv HH. lia.
rewrite iterSr.  apply H. apply/eguarded_eunf. done. 
Qed.

(*Lemma iter_unf_eguarded2  : forall n g, full_eunf g <> EVar n -> eguarded n g.
Proof. intros. apply/eguarded_full_unf2. 
destruct (full_eunf g) eqn:Heqn;try done. simpl. apply/negP=> HH. apply H. f_equal. lia.*) 

Lemma eguarded_notn : forall e n, eguarded n e -> full_eunf e <> EVar n.
Proof. 
intros. apply eguarded_full_unf in H. destruct (full_eunf e);try done. simpl in H. move => HH. inv HH. lia. 
Qed. 


(*Lemma eguarded_subst3 : forall g n n0 sigma, eguarded n (sigma n0) -> muv n0 g -> muv n g[e sigma].
Proof. simpl. 
elim=>//=;intros. 
move/eqP : H0=>Heq. subst=>//=. 
asimpl. apply/H;eauto. asimpl.  apply (@muv_ren _ _ succn) in H0. 
done. 
Qed.*)

Lemma eguarded_uniq : forall g n0 n1, eguarded n0 g = false -> eguarded n1 g = false -> n0 = n1.
Proof. 
elim=>//=. 
intros. lia. 
intros. suff : n0.+1 = n1.+1.  lia. apply/H=>//=. 
Qed.



Lemma eguarded_unfv : forall g n, eguarded n g = false -> full_eunf g = EVar n. 
Proof. 
intros. rewrite /full_eunf. remember (emu_height g). 
move : n0 g Heqn0 H.  
elim=>//=. case=>//=. intros. f_equal=>//=. lia. 
intros. 
destruct g;try done. simpl in Heqn0.
rewrite -iterS iterSr /=. rewrite H. done. 
rewrite emu_height_subst. inv Heqn0=>//=. 
case. simpl. intros. simpl in H0. have : n.+1 = 0. apply/eguarded_uniq. lia. lia. 
done. done. 
simpl in *. apply/negP=> HH. apply/negP. move/negP/negP : H0. eauto. 
eapply eguarded_subst2 in HH. eauto. asimpl. simpl. lia. 
Qed.

(*Lemma eguarded_not1 : forall n0 e n, iter n0 eunf e <> EVar n  -> eguarded n e.
Proof.
  elim;intros.  simpl in H . elim : n H . destruct e;try done.  simpl. apply/negP. move/eqP. move => HH. subst. eauto. 
simpl. 
apply eqP in HH. destruct 
intros. destruct (eqVneq (full_eunf e) (EVar n)). done. exfalso. apply/negP. 
move/negP/negP : H=>HH. apply/HH. 
apply (negP H). H. apply/muv_unf. apply/not_eguarded_muv. lia. 
Qed. 


Lemma eguardedP : forall e n,  eguarded n e = (full_eunf e != EVar n).
Proof. intros. apply/eq_iff. split. move/eguarded_not0. move/eqP.  lia. 
intros. destruct (eguarded n e) eqn:Heqn. done. apply eguarded_not1 in Heqn. rewrite Heqn in H. 
move : H. move/eqP. eauto. 
Qed. 





Lemma unf_eguarded  : forall g n, eunf g = EVar n -> eguarded n g = false. 
Proof. 
case=>//=. intros. inv H. lia. 
intros. destruct e;try done.   move : H. 
asimpl. destruct n0. done. asimpl. case. move=>->. 
simpl. lia. 
Qed.*)







(*Lemma unf_muv  : forall g n, eunf g = EVar n -> muv n g. 
Proof. 
case=>//=. intros. inv H. done.
intros. destruct e;try done.   move : H. 
asimpl. destruct n0. done. asimpl. case. move=>->. 
simpl. lia. 
Qed.


Lemma muv_ren2 : forall g n sigma, injective sigma ->  muv (sigma n) (g ⟨e sigma ⟩) -> muv n g.  
Proof. 
elim=>//=;intros. apply/eqP. apply/H. lia. 
move : H1. asimpl. intros. apply/(@H _ (0 .: sigma >> succn)). 
auto. asimpl. done.
Qed.

Lemma muv_subst2 : forall g n sigma, muv n (g [e sigma]) -> exists n0,  muv n0 g /\ muv n (sigma n0).
Proof.
elim=>//=;intros. 
exists n. ssa. 
apply H in H0.
move : H0.  asimpl. 
case. ssa. 
destruct x;try done. 
move : H1. asimpl. move/muv_ren2=>HH. 
exists x. ssa. 
Qed.



Lemma muv_unf2 : forall g n,  muv n (eunf g) -> muv n g. 
Proof. 
case=>//=;intros.
move : H. move/muv_subst2=>[] . 
ssa. destruct x;try done. simpl in H0.
rewrite (eqP H0). done. 
Qed.

Lemma muv_iter_unf2 : forall n0 g n,  muv n (iter n0 eunf g) -> muv n g. 
Proof. 
elim. case => //=. 
intros. simpl in H0. apply/H.
apply/muv_unf2. done. 
Qed.

Lemma muv_full_unf2 : forall g n,  muv n (full_eunf g) -> muv n g. 
Proof. 
intros. rewrite /full_eunf in H.  apply/muv_iter_unf2=>//=. eauto. 
Qed.

Lemma iter_unf_muv  : forall n0 n g, iter n0 eunf g = EVar n -> muv n g. 
Proof. 
elim;intros.
simpl in H. subst. simpl. lia.
simpl in H0. 
apply unf_muv in H0. 
apply/muv_iter_unf2. eauto. 
Qed.*)

(*Lemma eguarded_not_var : forall g n, eguarded n g -> muv n g = false. 
Proof. 
elim => //=;intros. lia. 
auto. 
Qed.*)

Definition is_evar e := if e is EVar _ then true else false. 


Lemma eunf_subst : forall e sigma, is_evar e = false ->  eunf (e [e sigma]) = (eunf e)[e sigma].
Proof. 
case;rewrite //=;intros. 
asimpl. f_equal. 
Qed.




Lemma full_unf_com : forall g sigma,  (forall n : nat_eqType, ~~ eguarded n g -> emu_height (sigma n) = 0) -> full_eunf g [e sigma] = (full_eunf g) [e sigma ]. 
Proof. 
intros. rewrite /full_eunf. rewrite emu_height_subst. 
remember (emu_height g). 
clear Heqn. 
elim : n g H. simpl. done. 
intros. simpl. rewrite H //=.
destruct (is_evar (iter n eunf g)) eqn:Heqn.  

destruct (iter n eunf g) eqn:Heqn2;try done. asimpl. simpl. 


have : emu_height (sigma n0) = 0. 
apply/H0. apply/negP=>HH. Check iter_unf_eguarded. 
apply (@iter_unf_eguarded n) in HH. rewrite Heqn2 in HH. done. 
destruct (sigma n0);try done. 
rewrite eunf_subst //=. eauto. 
Qed.



Lemma unf_com_ren : forall g sigma, eunf g ⟨e sigma ⟩ = (eunf g) ⟨e sigma ⟩.
Proof. 
elim;intros;try done. asimpl. simpl. asimpl. done. 
Qed. 
Lemma iter_unf_com_ren : forall i g sigma, iter i eunf g ⟨e sigma ⟩ = (iter i eunf g) ⟨e sigma ⟩.
Proof. 
elim;intros;simpl. 
done. rewrite H. rewrite unf_com_ren. done. 
Qed. 

Lemma full_unf_com_ren : forall g sigma, full_eunf g ⟨e sigma ⟩ = (full_eunf g) ⟨e sigma ⟩.
Proof. intros. rewrite /full_eunf. rewrite iter_unf_com_ren. rewrite emu_height_ren. done. 
Qed. 




CoInductive ecType :=
 | ECEnd
 | ECMsg : dir -> ch -> value -> ecType -> ecType
 | ECBranch : dir -> ch -> coseq ecType  -> ecType.


Lemma ec_match : forall e, e = match e with | ECEnd => ECEnd | ECMsg d a u g0 => ECMsg d a u g0 |  ECBranch d a gs => ECBranch d a gs end. 
Proof. case;auto. Qed.


Definition e_to_c' (f : endpoint -> ecType)  g :=
match full_eunf g with 
| EMsg d a u g0 =>  ECMsg d a u (f g0) 
| EBranch d a gs => ECBranch d a (comap f (to_coseq gs))
| _  => ECEnd
end.

CoFixpoint e_to_c g := e_to_c' e_to_c g. 

Lemma e_to_c'_eq g : e_to_c' e_to_c g =
match full_eunf g with 
| EMsg d a u g0 =>  ECMsg d a u (e_to_c g0) 
| EBranch d a gs => ECBranch d a (map e_to_c gs)
| _  => ECEnd
end.
Proof. 
rewrite /e_to_c'. destruct (full_eunf g);try done. 
f_equal. elim : l. simpl. rewrite !Utils.coeq comap_eq //=. 
intros. rewrite Utils.coeq. rewrite Utils.comap_eqs /=. rewrite Utils.coeq.  f_equal. done. 
Qed.

Lemma e_to_c_eq g : e_to_c g = e_to_c' e_to_c g. 
Proof. 
intros. rewrite /e_to_c'.  rewrite (ec_match (e_to_c g)). 
destruct g;try done;simpl. 
rewrite /e_to_c'. 
destruct (full_eunf (ERec g));try done. 
Qed.

Let e_to_cs_eqs := (e_to_c'_eq, e_to_c_eq). 

Lemma full_eunf_end  : full_eunf EEnd = EEnd.  
Proof. done. Qed.

Lemma full_eunf_msg d c u e0 : full_eunf (EMsg d c u e0) = EMsg d c u e0.
Proof. done. Qed.

Lemma full_eunf_branch d c es : full_eunf (EBranch d c es) = (EBranch d c es).  
Proof. done. Qed.

Let eunf_eqs := (full_eunf_end, full_eunf_msg, full_eunf_branch). 

Let eqs := (Utils.comap_eqs,e_to_cs_eqs, eunf_eqs, Utils.coeq). 

Inductive EQ_gen  (R : ecType -> ecType -> Prop) : ecType -> ecType -> Prop := 
 | eq_end : EQ_gen R ECEnd ECEnd
 | eq_msg e0 e1 d c v : R e0 e1 -> EQ_gen R (ECMsg d c v e0) (ECMsg d c v e1)
 | eq_branch es0 es1 d c : (es0 <<(bot2) (forall_gen R)  >> es1)  -> EQ_gen R (ECBranch d c es0) (ECBranch d c es1).
Notation EQ := (paco2 EQ_gen bot2).

Lemma EQ_gen_mon : monotone2 EQ_gen. 
Proof. 
move => x y R. intros. move : IN. fix IH 1. case. 
constructor.
intros. constructor.  apply/LE. done. 
move => es0 es1 d c. intros. constructor. apply/forall_gen_mon2. eauto. eauto. done. 
Qed.

Hint Resolve EQ_gen_mon : paco.

(*



(*Definition closed2 (A B : Type) (F0 F1 : (A -> B -> Prop) -> (A -> B -> Prop)) (R : A -> B -> Prop) := 
 F0 (F1 R) <2= (paco2 F1 R).  *)

Variant SymF {A : Type} (R : A -> A -> Prop) : A -> A -> Prop  := 
 | symF_intro x0 x1: R x0 x1  -> SymF R x1 x0. 

Hint Constructors SymF. 

Variant Or {A B : Type} (R0 R1 : A -> B -> Prop) : A -> B -> Prop  := 
 | in_L x0 x1 : R0 x0 x1 -> Or R0 R1 x0 x1
 | in_R x0 x1: R1 x0 x1  -> Or R0 R1 x0 x1.
Hint Constructors Or.


Lemma  forall_gen_symFP 
  : forall (A : Type) (P0 P1 : A -> A -> Prop) simC, SymF P0 <2= P1 ->
    Or (SymF (paco2 (forall_gen P0) bot2)) <3= gupaco2 (forall_gen P1) (simC).
Proof.
  gcofix CIH. intros. destruct PR.  
  inv H. punfold H1. inv H1. 
  gstep.  constructor. 
  gstep. constructor. eauto. pclearbot. gbase. eauto. 
  gbase. done. 
Qed.



Lemma forall_gen_sym : forall (A : Type) (P0 P1  : A -> A -> Prop) , SymF P0 <2= P1 ->
  SymF (paco2 (forall_gen P0) bot2)  <2= paco2 (forall_gen P1) bot2.
Proof.
intros. ginit. { eapply cpn2_wcompat. apply/forall_gen_mon.  } 
guclo forall_gen_symFP.  
Qed.

Variant TransF {A : Type} (R : A -> A -> Prop) : A -> A -> Prop  := 
 | transF_intro x0 x1 x2: R x0 x1 -> R x1 x2  -> TransF R x0 x2. 

Hint Constructors TransF. 


Lemma  forall_gen_transFP 
  : forall (A : Type) (P0 P1 : A -> A -> Prop) simC, TransF P0 <2= P1 -> 
    Or (TransF (paco2 (forall_gen P0) bot2)) <3= gupaco2 (forall_gen P1) (simC).
Proof.
  gcofix CIH. intros. destruct PR.  
  inv H. punfold H1. punfold H2. inv H1. inv H2. gstep. constructor. 
  pclearbot. inv H2. gstep. constructor. eauto. 
  pclearbot. gbase. eauto. 
  gbase. done. 
Qed.


Lemma forall_gen_trans : forall (A : Type) (P0 P1  : A -> A -> Prop) , TransF P0 <2= P1 ->
  TransF (paco2 (forall_gen P0) bot2)  <2= paco2 (forall_gen P1) bot2.
Proof.
intros. ginit. { eapply cpn2_wcompat. apply/forall_gen_mon.  } 
guclo forall_gen_transFP.  
Qed.*)




(*Lemma sim_concat
      s0 s1 t0 t1
      (EQ0: sim s0 t0)
      (EQ1: sim s1 t1)
  :
    @sim (concat s0 s1) (concat t0 t1)
.
Proof.
  intros. ginit. { eapply cpn2_wcompat.  pmonauto. } guclo prefixC_spec.
Qed.

Lemma sim_concat_proper: Proper (sim ==> sim ==> sim) concat.
Proof.
  repeat intro. eapply sim_concat; eauto.
Qed.


Lemma forall_gen_sym : forall (A : Type) (r0 r1 : coseq A -> coseq A -> Prop)  (P0 P1 : A -> A -> Prop) ,
 symF P0 <2= P1 -> symF r0 <2= r1 -> symF (forall_gen P0 r0)  <2= paco2 (forall_gen P1) r1.
Proof.
intros. induction PR.  pc. pc. 
Qed.*)


(*Definition closed2 (A B : Type) (P : (A -> B -> Prop) -> (A -> B -> Prop) -> Prop) (F : (A -> B -> Prop) -> (A -> B -> Prop)) (R : A -> B -> Prop) := 
 P R R -> P (F R) (paco2 F R).  

Definition sym_rel {A  : Type}  (F : (A -> A -> Prop) -> (A -> A -> Prop)) (R : A -> A -> Prop) :=
 forall a b, (F R) a b -> paco2 F R b a.*)



(*Lemma forall_gen_sym : forall (A : Type) (r : coseq A -> coseq A -> Prop)  (P : A -> A -> Prop) , sym_rel P P ->
  closed2  sym_rel (forall_gen P) r.
Proof.
rewrite /closed2 /sym_rel.  
intros. move : a b H1. pcofix CIH. 
intros. induction H2. pc. pc. 
Qed.

Definition trans_rel {A : Type}  (R0 R : A -> A -> Prop) := forall a b c, R0 a b -> R0 b c -> R a c.*)


(*Definition transF (A : Type) (R : A -> A -> Prop) x0 x1 := exists x', R x0 x' /\ R x' x1. 

Lemma forall_gen_trans : forall (A : Type) (r0 r1 : coseq A -> coseq A -> Prop)  (P0 P1 : A -> A -> Prop) ,
 transF P0 <2= P1 -> transF r0 <2= r1 -> transF (forall_gen P0 r0)  <2= paco2 (forall_gen P1) r1.
Proof.
rewrite /transF. intros. destruct PR,H1. induction H1. inv H2. pc. 
inv H2. subst. pc. apply/H. exists e1. ssa. right.  apply/H0. exists es1. ssa. 
Qed.*)

(*Lemma forall_gen_trans : forall (A : Type) (r : coseq A -> coseq A -> Prop)  (P : A -> A -> Prop) , trans_rel P P ->
  closed2  trans_rel (forall_gen P) r.
Proof.
rewrite /closed2 /trans_rel.  
intros. move : a b H1 H2. pcofix CIH. 
intros. induction H2. inv H3. pc. inv H3. 
subst. pc. eauto. eauto. 
Qed.*)



(*Lemma forall_gen_sym : forall (A : Type) (r : coseq A -> coseq A -> Prop)  (P : A -> A -> Prop) , 
  @closed2 (coseq A) (coseq A) (@sym_rel (coseq A)) (forall_gen P) r. 


(forall x y, r x y -> r y x) ->
 (forall x y, P x y -> P y x) -> (forall_gen P) r g0 g1 ->  g1 <<(r) (forall_gen P)  >>  g0. 

Lemma forall_gen_sm
Check (@closed2 _ _ sym_rel EQ_gen bot2).


Lemma forall_gen_sym : forall (A : Type) g0 g1 (r : coseq A -> coseq A -> Prop)  (P : A -> A -> Prop) , (forall x y, r x y -> r y x) ->
 (forall x y, P x y -> P y x) -> (forall_gen P) r g0 g1 ->  g1 <<(r) (forall_gen P)  >>  g0. 
Proof. 
intros. move : g0 g1 H1. pcofix CIH. 
intros. induction H2. pc. pc. 
Qed.

Lemma forall_gen_trans : forall (A : Type) g0 g1 g2 (r : coseq A -> coseq A -> Prop)  (P0 P1 P2 : A -> A -> Prop) , (forall x y z, x <<(bot2) (forall_gen P0) >>  y -> r y z -> r x z) -> (forall x y z, P0 x y -> P1 y z -> P2 x z) -> 
 g0 <<(bot2) (forall_gen P0) >> g1 -> (forall_gen P1) r g1 g2 ->  g0 <<(r) (forall_gen P2)  >>  g2. 
Proof. 
intros. move : g0 g1 g2 H1 H2. pcofix CIH. 
intros. uis H2. uis H3.
uis H3. eauto. pclearbot.   inv H9. right.  apply /CIH. apply H4. done. 
right. eauto. 
Qed.*)

(*Lemma forall_gen_sym : forall (A : Type) g0 g1 (r : coseq A -> coseq A -> Prop)  (P : A -> A -> Prop) , (forall x y, r x y -> r y x) -> (forall x y, P x y -> P y x) -> g0 <<(r) (forall_gen P)  >>  g1 ->  g1 <<(r) (forall_gen P)  >>  g0. 
Proof. 
intros. move : g0 g1 H1. pcofix CIH. 
intros. uis H2. inv H3.  
right. apply/CIH. done.
auto.  
Qed.*)

(*Lemma forall_gen_trans : forall (A : Type) g0 g1 g2 (r : coseq A -> coseq A -> Prop)  (P0 P1 P2 : A -> A -> Prop) , (forall x y z, x <<(bot2) (forall_gen P0) >>  y -> r y z -> r x z) -> (forall x y z, P0 x y -> P1 y z -> P2 x z) -> 
 g0 <<(bot2) (forall_gen P0) >> g1 ->  g1 <<(r) (forall_gen P1)  >>  g2 ->  g0 <<(r) (forall_gen P2)  >>  g2. 
Proof. 
intros. move : g0 g1 g2 H1 H2. pcofix CIH. 
intros. uis H2. uis H3.
uis H3. eauto. pclearbot.   inv H9. right.  apply /CIH. apply H4. done. 
right. eauto. 
Qed.*)


Lemma EQ_refl : forall g r,  g <<(r) EQ_gen  >>  g. 
Proof. 
pcofix CIH. case. pfold. constructor. 
intros. pfold. constructor. right. done. 
intros. pfold. constructor. 
apply/forall_gen_refl. auto. (*Compositional*)
Qed.

Hint Resolve EQ_refl.


Lemma EQ_sym : forall g0 g1, EQ g0 g1 -> EQ g1 g0. 
Proof. 
pcofix CIH. intros. punfold H0. inversion H0;subst.  
pfold. constructor. 
pfold. constructor. right.  apply/CIH. pclearbot. auto. 
pfold. constructor. clear H0. move : es1 es0 H. pcofix CIH2.
intros. punfold H0. inversion H0. pfold. constructor. 
subst. pfold. constructor. right. apply/CIH. pclearbot. auto. 
right. apply/CIH2. pclearbot. auto. 
Qed.

Lemma EQ_trans : forall g0 g1 g2, EQ g0 g1 -> EQ g1 g2 -> EQ g0 g2. 
Proof. 
pcofix CIH. 
intros. punfold H0. punfold H1. inversion H0;subst;inversion H1;subst. 
pfold. constructor. 
pfold. constructor. right. pclearbot. apply/CIH. eauto. eauto. 
pfold. constructor. clear H0 H1. 
move : es0 es1 es3 H H6. pcofix CIH2. 
intros. punfold H0. punfold H6. inversion H0;inversion H6;subst. 
pfold. constructor. 
done. 
done. 
pfold. inversion H7.  subst. constructor. right. pclearbot. apply/CIH. eauto. eauto. 
right. apply/CIH2.  pclearbot. eauto. pclearbot. eauto. 
Qed.


(*Lemma sym_forall : forall (A : Type) (P : A -> A -> Prop) (R : coseq A -> coseq A -> Prop), forall_gen P R <2= symF (forall_gen (symF P) (symF R)).
Proof. 
intros. rewrite /symF.  induction PR. constructor. 
constructor. done. done. 
Qed.*)

(*Lemma  EQ_gen_symFP 
  : forall simC,
    Or (SymF (paco2 EQ_gen bot2)) <3= gupaco2 EQ_gen (simC).
Proof.
  gcofix CIH. intros. destruct PR.  
  inv H. punfold H0. inv H0. 
  gstep.  constructor. 
  gstep. constructor. pclearbot. gfinal. eauto.  
  gstep. constructor. apply/forall_gen_sym. intros.
  2 : {  constructor. eauto. } 
  inv PR. pclearbot. gbase. apply/CIH. left. constructor. done. 
  gbase. done. 
Qed.

Lemma EQ_gen_sym : (SymF (paco2 EQ_gen bot2)) <2= paco2 EQ_gen bot2. 
Proof.
intros. ginit. { eapply cpn2_wcompat. apply EQ_gen_mon.  } 
guclo EQ_gen_symFP.  
Qed.


Lemma  EQ_gen_transFP 
  : forall simC,
    Or (TransF (paco2 EQ_gen bot2)) <3= gupaco2 EQ_gen (simC).
Proof.
  gcofix CIH. intros. destruct PR.  
  inv H. punfold H0. punfold H1. inv H0. inv H1. 
  gstep.  constructor. pclearbot.  inv H1.
  gstep. constructor. pclearbot. gfinal. eauto.  
  gstep. inv H1. constructor. apply/forall_gen_trans. intros.
  2 : {  econstructor. eauto. done. } 
  inv PR. pclearbot. gbase. apply/CIH. left. eauto. 
  gbase. done. 
Qed.*)



(*CoFixpoint comap (A B : Type)  (f : A -> B)  (aa : coseq A):= 
match aa with 
| conil => conil 
| cocons a aa' => cocons (f a) (comap f aa')
end.


CoFixpoint e_to_ec e :=
let cofix e_to_ecs  aa := 
match aa with 
| nil => conil 
| cons a aa' => cocons (e_to_ec a) (e_to_ecs aa')
end in 
match full_eunf e  with 
| EMsg d c u e0 =>  ECMsg d c u (e_to_ec e0) 
| EBranch d c es => ECBranch d c (e_to_ecs es)
| _  => ECEnd
end.

CoFixpoint e_to_ecs  aa := 
match aa with 
| nil => conil 
| cons a aa' => cocons (e_to_ec a) (e_to_ecs aa')
end.

Lemma e_to_ecs_nil : e_to_ecs nil = conil. 
Proof. rewrite (coseq_match (e_to_ecs _)) //=. 
Qed.

Lemma e_to_ecs_cons a b : e_to_ecs (a::b) = cocons (e_to_ec a) (e_to_ecs b). 
Proof. 
rewrite (coseq_match (e_to_ecs _)) /=. done. 
Qed.



Lemma comap_nil : comap e_to_ec nil = nil. 
Proof.
rewrite (coseq_match (comap _ _)) /=.  coseq_tac. done. 
Qed. 


Lemma comap_cons : forall (A B : Type) (a : A) l (f : A -> B), comap f (cocons a l) = cocons (f a) (comap f l). 
Proof.
intros. rewrite (coseq_match (comap _ _)) /=. done. 
Qed.



Let coeq := (e_to_ecs_nil, e_to_ecs_cons,Utils.coeq). 


Lemma cofix_comap  : forall aa, ((cofix comap  aa := 
match aa with 
| nil  => conil 
| cons a aa' => cocons (e_to_ec a) (comap aa')
end) aa) = e_to_ecs aa. 
Proof. 
elim. done. intros. rewrite coeq /=. 
rewrite (coseq_match  (_ (_::_))). f_equal.  
Qed.




Lemma e_to_ec_eq : forall e, e_to_ec e =
(match full_eunf e  with 
| EMsg d c u g0 =>  ECMsg d c u (e_to_ec g0) 
| EBranch d c es => ECBranch d c (e_to_ecs es)
| _  => ECEnd
end). 
Proof.
move => e. rewrite (ec_match (e_to_ec e)).
rewrite /e_to_ec. destruct (full_eunf e);try done. 
Qed.*)

(*Lemma e_to_ec_branch : forall e d c es, full_eunf e = EBranch d c es -> (e_to_ec e) =(E)= ECBranch d c (comap e_to_ec (to_coseq es)).
Proof.  
intros. 
rewrite e_to_ec_eq. *)
(*Define equality on streams*)

(*CoFixpoint e_to_ecs (es : seq endpoint) : coseq ecType := 
 match es with 
 | nil => conil
 | e' :: es' => cocons (e_to_ec e') (e_to_ecs es')
 end.*)









(*Lemma e_to_ecs_eq : forall es, e_to_ecs es = 
 match es with 
 | nil => conil 
 | g' :: gs' => cocons (e_to_ec g') (e_to_ecs gs')
 end. 
Proof. 
move => es. rewrite (coseq_match (e_to_ecs es)). destruct es. done. simpl. f_equal. 
Qed. *)





(*Inductive forallIC_gen {A B : Type} (P : A -> B -> Prop)  (R : seq A -> coseq B -> Prop)  : seq A -> coseq B -> Prop :=
| FEEIC_nil : forallIC_gen P R nil conil
| FEEIC_cons e0 e1 es0 es1 : P e0 e1 -> R es0 es1 -> forallIC_gen P R (cons e0 es0) (cocons e1 es1).
Lemma forallIC_gen_mon (A B : Type) (P : A -> B -> Prop)  : monotone2 (forallIC_gen P). 
Proof. 
move => x y. intros. induction IN. constructor. constructor. done. auto. 
Qed. 

Hint Resolve forallIC_gen_mon : paco. 

Definition ForallIC {A B : Type} (P : A -> B -> Prop)  es0 es1 := paco2 (forallIC_gen P) bot2 es0 es1. 

Lemma ForallIC_mon : forall (A B : Type) (P0 P1: A -> B -> Prop) es0 es1, (forall x0 x1, P0 x0 x1 -> P1  x0 x1) -> ForallIC P0 es0 es1 -> ForallIC P1 es0 es1. 
Proof.
move => A B P0 P1.
pcofix CIH. 
intros. pfold. punfold H1. inversion H1. subst. constructor. subst. 
constructor. auto. right. apply/CIH. auto. pclearbot. eauto. 
Qed.*)

Inductive Unravele_gen (R : endpoint -> ecType  -> Prop) : endpoint -> ecType  -> Prop :=
 | Unravele_gen_msg e0 ec d c u : R e0 ec -> Unravele_gen R (EMsg d c u e0) (ECMsg d c u ec)
 | Unravele_gen_branch (es : seq endpoint) (ecs : seq ecType) d c : size es = size ecs -> Forall (R_pair R) (zip es ecs)   -> Unravele_gen R (EBranch d c es) (ECBranch d c ecs)
 | Unravele_gen_rec e ec : Unravele_gen R (e [e ERec e .: EVar]) ec  -> Unravele_gen R (ERec e) ec (*guarded*)
 | Unravele_gen_end : Unravele_gen R EEnd ECEnd.



Lemma Unravele_gen_mon : monotone2 Unravele_gen. 
Proof. move => x0 x1. intros. induction IN;try done. con;eauto. 
con;eauto. apply/List.Forall_forall. intros. 
move/List.Forall_forall : H0. eauto. con. eauto. 
con. 
Qed.

Hint Resolve Unravele_gen_mon : paco. 

Definition Unravele e0 e1 := paco2 Unravele_gen bot2 e0 e1.



Variant Unravele2_gen (R : endpoint -> ecType -> Prop) : endpoint -> ecType  -> Prop :=
 | Unravele2_gen_msg d c e0 ec u :  R e0 ec -> Unravele2_gen R  (EMsg d c u e0) (ECMsg d c u ec)
 | Unravele2_gen_branch c (es : seq endpoint)  (ecs : seq ecType) d : size es = size ecs -> Forall (R_pair R) (zip es ecs)  -> Unravele2_gen R (EBranch d c es)  (ECBranch d c ecs)
 | Unravele2_gen_end :   Unravele2_gen R EEnd  ECEnd.

Lemma Unravele2_gen_mon : monotone2 Unravele2_gen. 
Proof. move => x0 x1. intros. induction IN;try done. con;eauto. 
con;eauto. apply/List.Forall_forall. intros. 
move/List.Forall_forall : H0. eauto. con. 
Qed.


Hint Resolve Unravele2_gen_mon. 

Lemma e_to_c_full_eunf : forall e, e_to_c e = e_to_c (full_eunf e). 
Proof. 
intros. rewrite !eqs full_eunf_idemp //=.
Qed.

Notation UnfUnravele := (ApplyF full_eunf ssrfun.id). 




Lemma Unravele_unf  : forall (F : (endpoint -> ecType -> Prop) -> (endpoint -> ecType -> Prop)) a b r, monotone2 F ->  paco2 (UnfUnravele \o F) r  a b <->  paco2 (UnfUnravele \o F) r  (full_eunf a) b.
Proof. 
intros. 
split. 
intros. punfold H0. inv H0. pfold. constructor. rewrite full_eunf_idemp. done. 
intros. punfold H0.  pfold. rewrite /comp. rewrite /comp in H0. inv H0. 
rewrite full_eunf_idemp in H1. constructor. done. 
Qed.

Lemma Unravele_eunf4 :  forall e ec (R: endpoint -> ecType -> Prop), paco2 Unravele_gen R (eunf e) ec -> paco2 Unravele_gen R e ec.
Proof.
intros.  destruct e;try done. pfold. constructor. simpl in H. punfold H. 
Qed.

Lemma Unravele_eunf5 :  forall n e ec (R: endpoint -> ecType -> Prop), paco2 Unravele_gen R (iter n eunf e) ec -> paco2 Unravele_gen R e ec.
Proof.
elim. done. intros. simpl in H0. apply Unravele_eunf4 in H0. auto. 
Qed.

Lemma Unravele_eunf6 :  forall e ec (R: endpoint -> ecType -> Prop), paco2 Unravele_gen R (full_eunf e) ec -> paco2 Unravele_gen R e ec.
Proof. 
intros. rewrite /full_eunf in H. apply/Unravele_eunf5.  eauto. 
Qed.


Lemma Unravele_iff : forall e ec, e << Unravele_gen >> ec <->  e << (UnfUnravele \o Unravele2_gen)  >> ec. 
Proof.
Proof. intros. split. 
move : e ec. pcofix CIH. 
intros. punfold H0.  induction H0. pclearbot. pfold.
constructor. rewrite /full_eunf /=.  constructor. eauto. 
pfold. constructor. rewrite /full_eunf /=. constructor. done. 
induction H0;auto. constructor. pclearbot. eauto. eauto.  
(*pclearbot. 
brewr
move : gs gcs H. elim;intros. 
rewrite coeq in H. rewrite coeq. 
uis H. 
rewrite coeq in H0. rewrite coeq. uis H0. eauto.  
left. apply/H. done. *)
pfold. constructor. rewrite full_eunf_subst. 
punfold IHUnravele_gen. inv IHUnravele_gen. done.
pfold. constructor. rewrite /full_eunf. constructor.
intros. 
move : e ec H.  pcofix CIH. intros. punfold H0. inv H0. 
inv H. apply/Unravele_eunf6. rewrite -H1. pfold. constructor. 
right. apply/CIH. pclearbot. done. 
apply/Unravele_eunf6. rewrite -H1. pfold. constructor. done. 
induction H3;auto. pclearbot. eauto. 
apply/Unravele_eunf6. rewrite -H2. pfold. constructor. 
Qed.




Lemma Unravele_uniq : forall e ec0 ec1, e << Unravele_gen >> ec0 ->  e  << Unravele_gen >> ec1 -> ec0 << EQ_gen >> ec1. 
Proof. 
pcofix CIH. 
move => e ec0 ec1 HH. punfold HH. induction HH. pclearbot.
move => HH2. punfold HH2. inversion HH2;subst.  
pfold. constructor. right. apply/CIH. eauto. pclearbot. done. 
move => HH2. punfold HH2. inversion HH2;subst. 
pfold. constructor. clear HH2. 
eapply coerce_forall2.  lia.

move : es ecs ecs0 H H0 H5 H6. 
elim. case;last done.  case;last done.  simpl. auto. 
move => a0 l IH. case;first done. move => a1 l0. case;first done. 
intros. simpl in *. inv H. inv H5. inv H0.  inv H6. pclearbot. simpl in *.
constructor. rewrite /R_pair /=. eauto. eauto. 
move => HH2. punfold HH2. inversion HH2. subst. 
 apply/IHHH. pfold. done. 
move => HH2. punfold HH2. inversion HH2. pfold. constructor. 
Qed.

Lemma Unravele_eq : forall g gc0 gc1, gc0 << EQ_gen >> gc1 ->  g << (ApplyF full_eunf ssrfun.id \o Unravele2_gen) >> gc0 ->  g  << (ApplyF full_eunf ssrfun.id \o  Unravele2_gen) >> gc1.
Proof.
pcofix CIH. 
intros. punfold H1. pfold.   constructor. inv H1. induction H;pclearbot. uis H0.
constructor.  eauto. 
uis H0. apply coerce_forall in H7. destruct H7. ssa. 
rewrite -H4. 
constructor. lia. clear H4 H0 H1.
elim : es ecs x H H3 H2 H5. case;last done. case;last done. 
simpl. auto. 
move => a l IH [];first done. 
move => a0 l0 [];first done. intros. simpl in *. 
inv H. inv H3.  inv H2.  inv H5. pclearbot. simpl in *. constructor. 
simpl. eauto. eauto. 
uis H0. constructor.
Qed.


Lemma e_to_c_rec e : (e_to_c (ERec e)) = e_to_c (e [e ERec e .: EVar]). 
Proof.
rewrite 4!eqs full_eunf_subst //=.  
Qed.


(*Later perhaps do it with gpaco*)
Lemma unravele_exist : forall e,  e << Unravele_gen >> (e_to_c e) <-> exists ec, e << Unravele_gen >>  ec.
Proof. 
intros. split. 
intros. exists (e_to_c e).  done.
case. move : e. 
intros. 
move : x e p. pcofix CIH. 
move => x e Hu. punfold Hu. induction Hu.
pfold. rewrite 3!eqs. constructor. pclearbot.  eauto. 
rewrite 3!eqs. pfold. constructor. 
rewrite size_map //=.
elim : es ecs H H0. case. simpl. auto. done. 
move => a0 l IH []. done. simpl in *. ssa. inv H0.  
simpl in *. pclearbot. constructor; eauto. 
pfold. constructor. 
rewrite e_to_c_rec. 
punfold IHHu. 
rewrite !eqs. pc. 
Qed.


Fixpoint enum e :=
e::
match e with 
| ERec e0 => map (fun e0 => e0 [e e .: EVar]) (enum e0)
| EMsg d c v e0 => enum e0
| EBranch d c es => flatten (map enum es)
| EEnd => nil
| EVar n => nil
end.

Definition nexte e := 
match e with 
| EMsg _ _ _ e0 => (e0::nil)
| EBranch _ _ es => es 
| _ => nil
end.

Definition nexte_unf e :=nexte (full_eunf e). 

Lemma selfe : forall e, e \in enum e. 
Proof. intros. destruct e;rewrite //=. 
Qed. 




Lemma enum_closed_eunf : forall e, unf_closed (enum e) eunf.
Proof. 
rewrite /unf_closed. 
elim;rewrite //=;intros. 
- rewrite inE in H. rewrite (eqP H). done. 
- rewrite inE in H. rewrite (eqP H). done. 
- rewrite inE in H0. destruct (orP H0). rewrite (eqP H1) /=. 
  rewrite inE. apply/orP. right. apply/map_f/selfe. 
  move : H1. move/mapP=>[]/=. intros. subst. rewrite inE. apply/orP. right.
  destruct (is_evar x) eqn:Heqn. 
  destruct x;try done. simpl.  destruct n. simpl. apply/map_f. apply/selfe. 
  simpl. have : EVar n = (EVar n.+1) [e ERec e .: EVar]. simpl. done. 
  move=>->. apply/map_f. done. 
  rewrite eunf_subst. apply/map_f/H/p. eauto. 
- rewrite inE in H0. destruct (orP H0). rewrite (eqP H1). rewrite /= !inE eqxx //=. 
  rewrite inE. rewrite H. lia. done. 
- rewrite inE in H0. destruct (orP H0). rewrite (eqP H1) inE eqxx //=. 
  rewrite inE. apply/orP. right. apply/flattenP. destruct (flattenP H1). exists x. done. 
  destruct (mapP H2). subst. apply/H. done. done. 
Qed.


Lemma enum_closed_full_eunf : forall e, unf_closed (enum e) full_eunf.    
Proof. 
rewrite /unf_closed. 
intros. rewrite /full_eunf. remember (emu_height a). clear Heqn. 
elim : n. done. intros. simpl. apply/enum_closed_eunf.  done. 
Qed.

Lemma next_subst : forall e sigma, (if e is EVar _ then false else true) ->  nexte (e [e sigma]) = map (fun e0 => e0 [e sigma]) (nexte e).
Proof. 
destruct e;try done. 
Qed.

Lemma enum_closed_nexte : forall e, next_closed (enum e) nexte.  
Proof. 
rewrite /next_closed. 
elim;rewrite //=;intros. 
rewrite inE in H. rewrite (eqP H) //= in H0.  
rewrite inE in H. rewrite (eqP H) //= in H0.  
rewrite inE in H0. destruct (orP H0). 
rewrite (eqP H2) //= in H1. 
move : H2. move/mapP=>[] //=. intros. subst. simpl.
destruct (if x is EVar _ then false else true) eqn:Heqn. 
 rewrite next_subst //= in H1.  
rewrite inE. apply/orP. right. 
destruct (mapP H1). subst. apply/map_f. apply/H. 2 : {  eauto. } 
eauto. 
destruct x;try done. simpl. destruct n. simpl. done. done.  
rewrite inE in H0. destruct (orP H0). rewrite (eqP H2) /= in H1. rewrite inE in H1.  rewrite (eqP H1) inE selfe. 
lia. rewrite inE. erewrite H. lia. eauto. done. 
rewrite inE in H0. destruct (orP H0). rewrite (eqP H2) /= in H1. rewrite inE. apply/orP. right.
apply/flattenP. exists (enum a'). apply/mapP.  exists a'. done. done. apply/selfe. 
rewrite inE. apply/orP. right. destruct (flattenP H2). 
destruct (mapP H3). subst. apply/flattenP. exists (enum x0). done.
apply/H. done. eauto. done. 
Qed.

Lemma enum_closed_nexte_unf : forall e, next_closed (enum e) nexte_unf.  
Proof. 
rewrite /next_closed. intros. rewrite /nexte_unf in H0. apply/enum_closed_nexte. 
2 : { eauto. } rewrite /full_eunf. 
apply/enum_closed_full_eunf. done. 
Qed.


Lemma enum_ren : forall e sigma, enum e ⟨e sigma⟩ = map (fun e0 => e0 ⟨e sigma⟩) (enum e).
Proof. 
elim;rewrite //=;intros. 
asimpl. f_equal. rewrite H.  rewrite -!map_comp. rewrite /comp. apply/eq_in_map => x xIn. 
asimpl. done. 
f_equal. done. f_equal. rewrite -map_comp. rewrite !map_flatten. 
rewrite -map_comp. f_equal.  rewrite /comp. apply/eq_in_map=> x xIn.
apply/H.  done. 
Qed.
 
Lemma enum_subst : forall e e' sigma (S : seq endpoint), (forall n e0, ~~ is_evar (sigma n) -> e0 \in enum (sigma n) -> e0 \in S) -> e' \in enum e [e sigma] -> e' \in map (fun e0 =>  e0 [e sigma]) (enum e) \/ e' \in S. 
Proof. 
elim;rewrite //=;intros. 
destruct (is_evar (sigma n)) eqn:Heqn. destruct (sigma n);try done. simpl in H0. rewrite inE in H0. rewrite (eqP H0). 
auto. right. apply/H. lia. done. 
rewrite inE in H0. rewrite (eqP H0). auto.
rewrite inE in H1.  destruct (orP H1). 
rewrite (eqP H2). rewrite inE. left. rewrite eqxx. lia. 
rewrite -!map_comp. 
rewrite /comp. 
have : map (fun x => x [e ERec e .: EVar] [e sigma]) (enum e) =  map (fun x =>  x [eERec e [eEVar 0 .: sigma >> ⟨e ↑ ⟩] .: sigma]) (enum e). 
apply/eq_in_map. move=> x xIn. asimpl. done. move=>->. 
move : H2. move/mapP=>[]. intros. 
subst. 
intros.
asimpl. 
eapply H in p. 
destruct p. destruct (mapP H2). subst. asimpl. left. rewrite inE. apply/orP. right. apply/map_f. done. 
right. 
2 : { intros. move : H2 H3. destruct n. asimpl. done. asimpl. rewrite enum_ren. intros. 
  destruct (mapP H3). subst. apply H0 in H4. instantiate (1 := map (fun e0 => e0 ⟨e succn ⟩) S).
apply/map_f.  done. destruct (sigma n);try done. } 
destruct (mapP H2). subst. asimpl. done.
rewrite inE in H1.  destruct (orP H1). 
rewrite (eqP H2). auto.
rewrite inE. intros. 
eapply H in H2. destruct H2.  left. apply/orP. right. done. eauto. 
auto. 

rewrite inE in H1. destruct (orP H1). rewrite (eqP H2) /=. auto.
clear H1. 
rewrite -map_comp /comp in H2. destruct (flattenP H2). destruct (mapP H1). 
subst. eapply H in H3. 
destruct H3. left. rewrite inE. apply/orP. right. rewrite map_flatten -map_comp /comp. 
destruct (mapP H3). subst. apply/flattenP. exists ([seq e0 [esigma] | e0 <- enum x0]). apply/map_f. done. 
apply/map_f. 
done. 
right.  
eauto. done. done. 
Qed.



Lemma enum_subst_eunf : forall e e', e' \in enum (eunf e)  -> e' \in enum e.  
Proof. 
intros. 
destruct e;try done. 
move : H. simpl. move/enum_subst=>HH. 
move : (HH (enum (ERec e)))=>HH'.
edestruct HH'. case. 
simpl. intros. done. done. 
rewrite inE. rewrite H. lia.
simpl in H. done.  
Qed.

Lemma enum_subst_iter_eunf : forall k e e', e' \in enum (iter k eunf e)  -> e' \in enum e.  
Proof. 
elim. done. 
intros. apply/H. apply/enum_subst_eunf. rewrite -iterS. done. 
Qed.

Lemma enum_subst_nexte : forall e e' e'', e' \in nexte e -> e'' \in enum e'  -> e'' \in enum e.  
Proof. 
case;intros;try done.  
simpl in H. 
rewrite inE in H.  simpl. move : H. move/eqP=>HH. subst. rewrite inE H0 //=. lia. 
simpl in H. simpl. rewrite inE. apply/orP. right. apply/flattenP. exists (enum e'). 
apply/map_f. done. done. 
Qed.

Lemma enum_subst_nexte_unf : forall e e' e'', e' \in nexte_unf e -> e'' \in enum e'  -> e'' \in enum e.  
Proof. 
intros. rewrite /nexte_unf in H.  eapply enum_subst_nexte in H. apply/enum_subst_iter_eunf. eauto. 
done. 
Qed.


Inductive EQ2_gen  (R : endpoint  -> endpoint  -> Prop) : endpoint  -> endpoint  -> Prop := 
 | eq_end2 : EQ2_gen R EEnd EEnd
 | eq_msg2 e0 e1 d c v : R e0 e1 -> EQ2_gen R (EMsg d c v e0) (EMsg d c v e1)
 | eq_branch2 es0 es1 d c : size es0 = size es1 -> Forall (fun p => R p.1 p.2) (zip es0 es1)  -> 
                            EQ2_gen R (EBranch d c es0) (EBranch d c es1).

Lemma EQ2_gen_mon  : monotone2 EQ2_gen. 
Proof. 
move => x0 x1. intros. induction IN;try done. con. con;eauto. con;eauto. 
elim : es0 es1 H H0 LE;try done. case=>//=. move => a l IH [] //=. 
intros. inv H. inv H0. simpl in *. con;eauto .
Qed.


Hint Resolve EQ2_gen_mon : paco.

Notation EQ2 := (fun e0 e1 => paco2 ((ApplyF full_eunf full_eunf) \o EQ2_gen) bot2 e0 e1).


Notation Unravele2 := (fun e ec =>  paco2 (UnfUnravele \o Unravele2_gen) bot2 e ec).

Ltac pc := pclearbot.

Lemma EQ2_spec1 : forall e0 e1 ec0 ec1, Unravele2 e0 ec0 -> Unravele2 e1 ec1 ->  EQ2 e0 e1 -> paco2 EQ_gen bot2 ec0 ec1. 
Proof. 
pcofix CIH. intros. punfold H0. punfold H1. punfold H2.
inv H0. clear H0. 
inv H1. clear H1. 
inv H2. clear H2. 
inv H1;pc. 
rewrite -H3 in H.  rewrite -H4 in H0. inv H. inv H0. done. 
rewrite -H2 in H.  rewrite -H3 in H0. inv H. inv H0. pc. pfold. con. eauto. 
rewrite -H2 in H.  rewrite -H3 in H0. inv H. inv H0. pc. pfold. con.
apply/Forall_ForallC.  lia. 
clear H2 H3 H H0 H1. elim : es0 es1 ecs ecs0 H4 H10 H12 H5 H11 H13. 
case=>//=. 
case=>//=. 
case=>//=. move => a l IH [] //=. move => a0 l0 [] //=. move => a1 l1 [] //=. 
intros. inv H4.  inv H10.  inv H12. inv H5.  inv H11. inv H13. con; eauto. simpl in *. pc. 
eauto. 
Qed. 

Lemma EQ2_spec2 : forall e0 e1 ec0 ec1, Unravele2 e0 ec0 -> Unravele2 e1 ec1 -> paco2 EQ_gen bot2 ec0 ec1 -> EQ2 e0 e1. 
Proof. 
pcofix CIH. intros. punfold H0. punfold H1. punfold H2.
inv H0. clear H0. 
inv H1. clear H1. 
inv H2. clear H2. pfold.  con. 
inv H;pc.  inv H0;pc. con. 
pc. pfold.  con. 
inv H;pc.  inv H0;pc. con. eauto.
pfold.  con. 
inv H;pc.  inv H0;pc. con.  rewrite H6 H9.  
apply coerce_forall in H1. destruct H1. ssa. injt. lia. 
clear H H2 H0 H3 H4.  apply coerce_forall in H1. destruct H1. ssa. injt. 
elim : ecs ecs0 es es0 H H6 H9 H1 H8 H11.
case=>//=.  case=>//=. case. simpl. done. done.  
move => a l IH.  
case =>//=. move => a1 l1. move=> [] //=. move => a0 l0 [] //=.  move => a2 l2. intros. inv H. inv H6. inv H9. inv H1. inv H8. inv H11. pc. simpl in *. 
con;eauto. 
Qed. 


Lemma EQ2_eunf : forall e0 e1 r, e0 <<( r) (ApplyF full_eunf full_eunf \o EQ2_gen) >> (full_eunf e1)  -> e0 <<( r) (ApplyF full_eunf full_eunf \o EQ2_gen) >> e1.
Proof. 
intros. punfold H. inv H. pfold. con. rewrite full_eunf_idemp in H0. done. 
Qed.

Lemma EQ2_eunf2 : forall e0 e1 r, e0 <<( r) (ApplyF full_eunf full_eunf \o EQ2_gen) >> e1  -> e0 <<( r) (ApplyF full_eunf full_eunf \o EQ2_gen) >> (full_eunf e1).
Proof. 
intros. punfold H. inv H. pfold. con. rewrite full_eunf_idemp. done. 
Qed.

Lemma EQ2_eunfl : forall e0 e1 r, (full_eunf e0) <<( r) (ApplyF full_eunf full_eunf \o EQ2_gen) >> e1  -> e0 <<( r) (ApplyF full_eunf full_eunf \o EQ2_gen) >> e1.
Proof. 
intros. punfold H. inv H. pfold. con. rewrite full_eunf_idemp in H0. done. 
Qed.

Lemma EQ2_eunfl2 : forall e0 e1 r, e0 <<( r) (ApplyF full_eunf full_eunf \o EQ2_gen) >> e1  -> (full_eunf e0) <<( r) (ApplyF full_eunf full_eunf \o EQ2_gen) >> e1.
Proof. 
intros. punfold H. inv H. pfold. con. rewrite full_eunf_idemp. done. 
Qed.

Inductive Rollinge2_gen (R : endpoint ->  Prop) : endpoint   -> Prop :=
 | role3_gen_msg e0 c d u :  R e0 -> Rollinge2_gen R  (EMsg d c u e0) 
 | role3_gen_branch c (es : seq endpoint)  d :  Forall R es -> Rollinge2_gen R (EBranch d c es) 
 | role4_gen_end :   Rollinge2_gen R EEnd
 | role4_gen_rec e : Rollinge2_gen R (e [e ERec e .: EVar]) ->  Rollinge2_gen R (ERec e).

Lemma Rollinge2_gen_mon : monotone1 Rollinge2_gen. 
Proof. move => x0 x1. intros. induction IN;try done. con;eauto. 
con;eauto. apply/List.Forall_forall. intros. eauto. 
move/List.Forall_forall : H. eauto. con. con. eauto. 
Qed. 


Hint Resolve Rollinge2_gen_mon : paco. 



Inductive Rollinge_gen (R : endpoint ->  Prop) : endpoint   -> Prop :=
 | role2_gen_msg e0 c d u :  R e0 -> Rollinge_gen R  (EMsg d c u e0) 
 | role2_gen_branch c (es : seq endpoint)  d :  Forall R es -> Rollinge_gen R (EBranch d c es) 
 | role2_gen_end :   Rollinge_gen R EEnd.
(* | role2_gen_rec e : Rollinge_gen R (e [e ERec e .: EVar]) ->  Rollinge_gen R (ERec e).*)

Lemma Rollinge_gen_mon : monotone1 Rollinge_gen. 
Proof. move => x0 x1. intros. induction IN;try done. con;eauto. 
con;eauto. apply/List.Forall_forall. intros. eauto. 
move/List.Forall_forall : H. eauto. con. 
Qed. 


Hint Resolve Rollinge_gen_mon : paco. 
Notation Rollinge := (paco1 (ApplyF1 full_eunf \o Rollinge_gen) bot1).  


Lemma rollinge_eunf4 :  forall e (R: endpoint -> Prop), Rollinge2_gen R (eunf e) -> Rollinge2_gen R e.
Proof.
intros.  destruct e;try done. con. simpl in H. done. 
Qed.

Lemma rollinge_eunf5 :  forall n e (R: endpoint -> Prop), Rollinge2_gen R (iter n eunf e)  -> Rollinge2_gen R e.
Proof.
elim. done. intros. simpl in H0. apply rollinge_eunf4 in H0. auto. 
Qed.

Lemma rollinge_eunf6 :  forall e (R: endpoint -> Prop), Rollinge2_gen R (full_eunf e)  -> Rollinge2_gen R e.
Proof. 
intros. rewrite /full_eunf in H. apply/rollinge_eunf5.  eauto. 
Qed.


(*Lemma rollinge_eunf7 :  forall e (R: endpoint -> Prop), Rollinge2_gen R e -> Rollinge2_gen R (eunf e).
Proof.
intros.  destruct e;try done. simpl. inv H. done. 
Qed.

Lemma rollinge_eunf8 :  forall n e (R: endpoint -> Prop), Rollinge2_gen R e -> Rollinge2_gen R (iter n eunf e).  
Proof.
elim. done. intros. simpl in H0. apply rollinge_eunf7 in H0. rewrite iterSr.  auto. 
Qed.

Lemma rollinge_eunf9 :  forall e (R: endpoint -> Prop), Rollinge2_gen R e  -> Rollinge2_gen R (full_eunf e).
Proof. 
intros. rewrite /full_eunf in H. apply/rollinge_eunf8.  eauto. 
Qed.
*)

Lemma FEQP : forall R x, (ApplyF1 full_eunf \o Rollinge_gen) R x <-> Rollinge2_gen R x. 
Proof. 
intros. split. case. intros. apply/rollinge_eunf6. inv r;eauto. con. done. 
con. done. con. 
intros. con. 
induction H. con. done. con. done. con. 
rewrite full_eunf_subst. done. 
Qed. 






Lemma EQ2_tree : forall e0 e1, EQ2 e0 e1 -> Rollinge e0.
Proof. 
pcofix CIH. intros. 
punfold H0. inv H0. pfold. con. inv H. con. con. pc.  eauto. 
con. clear H1 H2. elim : es0 es1 H3 H4. case. done. done. 
move => a l IH [] //=. intros. inv H3. inv H4. pc. simpl in *. con; eauto. 
Qed. 

Lemma EQ2_tree2 : forall e0 e1, EQ2 e0 e1 -> Rollinge e1.
Proof. 
pcofix CIH. intros. 
punfold H0. inv H0. pfold. con. inv H. con. con. pc.  eauto. 
con. clear H1 H2. elim : es0 es1 H3 H4. case. done. done. 
move => a l IH [] //=. intros. inv H3. inv H4. pc. simpl in *. con; eauto. 
Qed. 

Lemma Rolling_Unravele : forall g ,  Rollinge g -> paco2 (UnfUnravele \o Unravele2_gen) bot2 g (e_to_c g).
Proof. 
pcofix CIH. intros. punfold H0. inv H0. pfold.
rewrite e_to_c_full_eunf.  con. 
inv H;eauto;pclearbot;rewrite !eqs.  
rewrite -e_to_c'_eq -e_to_c_eq. con. eauto. 
con. rewrite size_map //=. 
clear H H1 H0. elim : es H2. simpl.  auto. 
simpl. intros. inv H2. pclearbot. con. eauto. eauto. 
con. 
Qed.


Theorem EQ2_spec : forall e0 e1, EQ2 e0 e1 <-> exists ec0 ec1, Unravele2 e0 ec0 /\ Unravele2 e1 ec1 /\ paco2 EQ_gen bot2 ec0 ec1. 
Proof. 
intros. split. intros. exists (e_to_c e0). exists (e_to_c e1). ssa. 
apply/Rolling_Unravele/EQ2_tree. eauto. 
apply/Rolling_Unravele/EQ2_tree2. eauto. apply/EQ2_spec1.
apply/Rolling_Unravele. apply/EQ2_tree. eauto. 
apply/Rolling_Unravele. apply/EQ2_tree2. eauto. done. 
case. move => x. case. intros. ssa. apply/EQ2_spec2. eauto. eauto. done. 
Qed. 


Lemma Rollinge_iff : forall g, Rollinge g <-> Rollinge (full_eunf g). 
Proof. 
intros. split. intros. punfold H. inv H. pfold. con. rewrite full_eunf_idemp. done. 
intros. punfold H. inv H. rewrite full_eunf_idemp in H0. pfold. con. done. 
Qed.

Lemma EQ2_refl : forall g, Rollinge g ->  g << (ApplyF full_eunf full_eunf \o  EQ2_gen)  >>  g. 
Proof. 
pcofix CIH. intros. punfold H0. inv H0. pfold.  con. inv H. 
con. pclearbot. eauto. con. lia. clear H1. elim : es H2. simpl. done. 
simpl. intros. inv H2. pclearbot. con;eauto. 
con. 
Qed.

Lemma EQ2_reflr : forall g r, Rollinge g ->  g <<(r) (ApplyF full_eunf full_eunf \o  EQ2_gen)  >>  g. 
Proof. 
pcofix CIH. intros. punfold H0. inv H0. pfold.  con. inv H. 
con. pclearbot. eauto. con. lia. clear H1. elim : es H2. simpl. done. 
simpl. intros. inv H2. pclearbot. con;eauto. 
con. 
Qed.

