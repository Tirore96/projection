From mathcomp Require Import all_ssreflect zify finmap.
From Projection Require Export intermediateProj.
Require Import Paco.paco.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Let eqs := intermediateProj.eqs. 

Require Import Program. 
From Equations Require Import Equations. 

Definition has_tree g := next_rec nil has_treeP (fun _ => true) g.

Fixpoint inp p g := 
  match g with
  | GRec g0 => inp p g0
  | GMsg a _ g0 => (comp_dir p a) || (inp p g0)
  | GBranch a gs => (comp_dir p a) || (has (inp p) gs)
  | _ => false 
  end.

Fixpoint inp_all p g := 
  match g with
  | GRec g0 => inp_all p g0
  | GMsg a _ g0 => (comp_dir p a) || (inp_all p g0)
  | GBranch a gs => (comp_dir p a) || (all (inp_all p) gs)
  | _ => false 
  end.

Lemma inp_ren : forall g sigma p,  inp p (g ⟨g sigma ⟩) = inp p g.  
Proof.
elim;rewrite //=;intros. f_equal.  rewrite H //=. 
f_equal. rewrite has_map. apply/eq_in_has. move=> x xIn. 
simpl. 
auto. 
Qed.

Lemma inp_all_ren : forall g sigma p,  inp_all p (g ⟨g sigma ⟩) = inp_all p g.  
Proof.
elim;rewrite //=;intros. f_equal.  rewrite H //=. 
f_equal. rewrite all_map. apply/eq_in_all. move=> x xIn. 
simpl. 
auto. 
Qed.

Lemma inp_subst : forall g sigma p, inp p (g [g sigma ]) -> inp p g \/ exists n, inp p (sigma n).  
Proof.
elim;rewrite //=;intros.
right. exists n. auto. 
apply H in H0. destruct H0. auto. 
destruct H0. right. move : H0. asimpl. 
destruct x. done. simpl. asimpl. rewrite inp_ren. exists x. auto.
destruct (orP H0).  lia. 
auto. 
apply H in H1. destruct H1. lia. auto. 
destruct (orP H0). lia. rewrite has_map /= in H1. 
destruct (hasP H1). simpl in H3. apply H in H3;auto. 
destruct H3. left. apply/orP. right. apply/hasP. exists x. done. done. 
auto. 
Qed.

Lemma inp_all_subst : forall g sigma p, inp_all p (g [g sigma ]) -> inp_all p g \/ exists n, inp_all p (sigma n).  
Proof.
elim;rewrite //=;intros.
right. exists n. auto. 
apply H in H0. destruct H0. auto. 
destruct H0. right. move : H0. asimpl. 
destruct x. done. simpl. asimpl. rewrite inp_all_ren. exists x. auto.
destruct (orP H0).  lia. 
auto. 
apply H in H1. destruct H1. lia. auto.
destruct (comp_dir p a) eqn:Heqn.  simpl. auto. 
simpl in *. 
rewrite all_map in H0. 
elim : l H0 H. ssa. 
move => a0 l IH /= /andP => [] [] . ssa. 
move : (H a0). rewrite inE eqxx //=.  move => HH2.
apply HH2 in a1=>//=. destruct (inp_all p a0) eqn:Heqn2.  simpl. auto. 
simpl. eauto. 
Qed.

Lemma inp_subst2 : forall g sigma p, (forall n, inp p (sigma n) -> inp p g) ->  inp p (g [g sigma ]) ->  inp p g.  
Proof. 
intros. apply inp_subst in H0. destruct H0. done. destruct H0. eauto.  
Qed.

Lemma inp_all_subst2 : forall g sigma p, (forall n, inp_all p (sigma n) -> inp_all p g) ->  inp_all p (g [g sigma ]) ->  inp_all p g.  
Proof. 
intros. apply inp_all_subst in H0. destruct H0. done. destruct H0. eauto.  
Qed.

Lemma ptcps_subst2 : forall g sigma p, inp p g -> inp p (g [g sigma ]).  
Proof.
elim;rewrite //=;intros. auto.
destruct (orP H0);try lia.
rewrite H //=.   lia. 
destruct (orP H0);try lia.
apply/orP. right. rewrite has_map. 
destruct (hasP H1). eapply H in H3. 
apply/hasP. eauto. exists x.  done. simpl.  eauto. done. 
Qed.

Lemma ptcps_all_subst2 : forall g sigma p, inp_all p g -> inp_all p (g [g sigma ]).  
Proof.
elim;rewrite //=;intros. auto.
destruct (orP H0);try lia.
rewrite H //=.   lia. 
destruct (orP H0);try lia.
apply/orP. right. rewrite all_map. 
apply/allP=> x xIn /=. eauto. apply/H=>//=. apply (allP H1)=>//=. 
Qed.

Lemma inp_subst_iff : forall g sigma p, (forall n, inp p (sigma n) -> inp p g) ->  inp p (g [g sigma ]) =  inp p g.  
Proof. 
intros. apply/eq_iff.  split. move/inp_subst2=>HH. apply/HH. auto.
intros.  apply/ptcps_subst2. done. 
Qed.

Lemma inp_all_subst_iff : forall g sigma p, (forall n, inp_all p (sigma n) -> inp_all p g) ->  inp_all p (g [g sigma ]) =  inp_all p g.  
Proof. 
intros. apply/eq_iff.  split. move/inp_all_subst2=>HH. apply/HH. auto.
intros.  apply/ptcps_all_subst2. done. 
Qed.




Inductive Unfg (R : gType -> Prop) : gType -> Prop :=
 | UnfgC g : Unfg R (g [g GRec g .: GVar]) ->  Unfg R (GRec g)
 | UnfgR  g :  R g -> Unfg R g.
Hint Constructors Unfg. 

Print part_of2. Print part_ofFU. Print part_ofF.   Check ApplyF1. 
Print part_of2. Print part_ofFU. 
Inductive part_of3 (p : ptcp) : gType -> Prop :=
    part_of3C g : Unfg ((part_ofF p) (part_of3 p)) g -> part_of3 p g.
Hint Constructors part_of3. 

Check part_of3_ind. 

Lemma part_of3_ind2
     : forall (p : ptcp) (P : gType -> Prop),
       (forall (a : action) (u : value) (g0 : gType), comp_dir p a -> P (GMsg a u g0)) ->
       (forall (a : action) (u : value) (g0 : gType), ~ comp_dir p a -> part_of3 p g0 -> P g0 -> P (GMsg a u g0)) ->
       (forall (a : action) (gs : seq gType), comp_dir p a -> P (GBranch a gs)) ->
       (forall (a : action) (g : gType) (gs : seq gType), ~ comp_dir p a -> In g gs -> part_of3 p g -> P g -> P (GBranch a gs)) ->
       (forall g,  part_of3 p (g [g GRec g .: GVar]) -> P (g [g GRec g .: GVar]) -> P (GRec g) )
 ->
       forall g : gType, part_of3 p g -> P g.
Proof. 
intros. move : g H4. fix IH 2. intros. destruct H4. 
move : g H4. fix IH2 2. intros. destruct H4. apply/H3. con. done. apply/IH2. done.
destruct H4. apply/H. done. 
destruct (comp_dir p a) eqn:Heqn. apply H. rewrite Heqn. done. 
apply H0. rewrite Heqn. done. done. auto. 
destruct (comp_dir p a) eqn:Heqn. apply H1. rewrite Heqn. done. done. 
destruct (comp_dir p a) eqn:heqn. apply/H1. comp_disc. 
eapply H2. comp_disc. eauto. done. apply/IH. done. 
Qed.


Lemma part_of3_subst : forall p g sigma, part_of3 p g -> part_of3 p g [g sigma]. 
Proof. 
intros. elim/part_of3_ind2 : H sigma;intros;simpl. econstructor 1. eauto. 
eauto. con. con. con. done. 
con. con. econstructor 4. 2 : {  apply/H2. apply : sigma. } apply/inP. 
apply/map_f.   apply/inP. done. 
con. asimpl. move : (H0 ( sigma)).  asimpl.
intros. con.   asimpl. inv H1. move : H2. done. 
Qed.

Lemma inp_part_of2 : forall p g, inp p g -> part_of3 p g. 
Proof. 
move => p. elim;intros;try done. 
con. con.  simpl in H0. move/H : H0. 
intros. suff : part_of3 p (g [gGRec g .: var]). case. done. 
apply/part_of3_subst. done. ssa. destruct (orP H0). 
con. con. con. done. 
con. con. econstructor 2. auto. 
simpl in H0. destruct (orP H0). 
con. con. con. done. 
move/hasP : H1. case=> x. intros. 
con. con. econstructor 4. apply/inP. eauto. apply/H. done. done. 
Qed.


Lemma part_of23 : forall p g, part_of3 p g -> part_of2 p g. 
Proof. 
intros. elim/part_of3_ind2 : H;intros. con. con. con. done. 
con. con. cbn. constructor 2. done. 
con. con. con. done. 
con. con. econstructor 4. eauto. done. 
con. con. rewrite full_unf_subst. inv H0. inv H1. done. 
Qed.

Lemma inp_unf : forall g p, inp p (unf g) =  inp p g. 
Proof. 
destruct g;try done. simpl. intros. rewrite  inp_subst_iff //=. 
case. done. done. 
Qed.

Lemma inp_full_unf : forall g p, inp p g = inp p (full_unf g). 
Proof. 
intros. rewrite /full_unf. remember (mu_height g). 
clear Heqn. elim : n g. done. intros. simpl.  rewrite inp_unf. 
done. 
Qed.


Lemma inp_complete : forall g p, part_of2 p g  -> inp p g. 
Proof. intros. 
elim/part_of2_ind2 : H;intros. rewrite inp_full_unf H0 //= H //=. 
rewrite inp_full_unf H2 /=. lia. 
rewrite inp_full_unf H0. ssa. lia. 
rewrite inp_full_unf. rewrite H3 /=. apply/orP. right. 
apply/hasP. exists g0. apply/inP=>//=. done. 
Qed.


(*It is hard to show inp -> part_of2 because of structural induction of inp computation clashes with full unfolding of part_of2, so we make an intermediate judgment, part_of3, prove an induction principle*)
Lemma inp_iff : forall g p, inp p g <-> part_of2 p g. 
Proof. 
intros. split;intros.  apply/part_of23. apply/inp_part_of2. done. 
apply/inp_complete. done. 
Qed.




Inductive part_of_all3 (p : ptcp) : gType -> Prop :=
    part_of_all3C g : Unfg ((part_of_allF p) (part_of_all3 p)) g -> part_of_all3 p g.
Hint Constructors part_of_all3. 

Check part_of_all3_ind. 

Lemma part_of_all3_ind2
     : forall (p : ptcp) (P : gType -> Prop),
       (forall (a : action) (u : value) (g0 : gType), comp_dir p a -> P (GMsg a u g0)) ->
       (forall (a : action) (u : value) (g0 : gType), ~ comp_dir p a -> part_of_all3 p g0 -> P g0 -> P (GMsg a u g0)) ->
       (forall (a : action) (gs : seq gType), comp_dir p a -> P (GBranch a gs)) ->
       (forall (a : action) (gs : seq gType), ~ comp_dir p a -> (forall g, In g gs -> part_of_all3 p g -> P g) -> (forall g, In g gs -> part_of_all3 p g) -> P (GBranch a gs)) ->
       (forall g,  part_of_all3 p (g [g GRec g .: GVar]) -> P (g [g GRec g .: GVar]) -> P (GRec g) )
 ->
       forall g : gType, part_of_all3 p g -> P g.
Proof. 
intros. move : g H4. fix IH 2. intros. destruct H4. 
move : g H4. fix IH2 2. intros. destruct H4. apply/H3. con. done. apply/IH2. done.
destruct H4. apply/H. done. 
destruct (comp_dir p a) eqn:Heqn. apply H. rewrite Heqn. done. 
apply H0. rewrite Heqn. done. done. auto. 
destruct (comp_dir p a) eqn:Heqn. apply H1. rewrite Heqn. done. done. 
destruct (comp_dir p a) eqn:heqn. apply/H1. comp_disc. 
eapply H2. comp_disc. intros.  apply/IH. apply H4. done. eauto. 
Qed.


Lemma part_of_all3_subst : forall p g sigma, part_of_all3 p g -> part_of_all3 p g [g sigma]. 
Proof. 
intros. elim/part_of_all3_ind2 : H sigma;intros;simpl. econstructor 1. eauto. 
eauto. con. con. con. done. 
con. con. econstructor 4. move => g0. move/inP. move/mapP=>[]. intros. subst. apply/H0. 
apply/inP. done. apply/H1. apply/inP. done. 
con. asimpl. move : (H0 ( sigma)).  asimpl.
intros. con.   asimpl. inv H1. move : H2. done. 
Qed.

Lemma inp_part_of_all2 : forall p g, inp_all p g -> part_of_all3 p g. 
Proof. 
move => p. elim;intros;try done. 
con. con.  simpl in H0. move/H : H0. 
intros. suff : part_of_all3 p (g [gGRec g .: var]). case. done. 
apply/part_of_all3_subst. done. ssa. destruct (orP H0). 
con. con. con. done. 
con. con. econstructor 2. auto. 
simpl in H0. destruct (orP H0). 
con. con. con. done. con.  con. econstructor 4. 
intros. apply/H. apply/inP. done. apply (allP H1). apply/inP. done. 
Qed.


Lemma part_of_all23 : forall p g, part_of_all3 p g -> part_of_all2 p g. 
Proof. 
intros. elim/part_of_all3_ind2 : H;intros. con. con. con. done. 
con. con. cbn. constructor 2. done. 
con. con. con. done. 
con. con. econstructor 4. eauto. 
con. con. rewrite full_unf_subst. inv H0. inv H1. done. 
Qed.

Lemma inp_all_unf : forall g p, inp_all p (unf g) =  inp_all p g. 
Proof. 
destruct g;try done. simpl. intros. rewrite  inp_all_subst_iff //=. 
case. done. done. 
Qed.

Lemma inp_all_full_unf : forall g p, inp_all p g = inp_all p (full_unf g). 
Proof. 
intros. rewrite /full_unf. remember (mu_height g). 
clear Heqn. elim : n g. done. intros. simpl.  rewrite inp_all_unf. 
done. 
Qed.


Lemma inp_all_complete : forall g p, part_of_all2 p g  -> inp_all p g. 
Proof. intros. 
elim/part_of_all2_ind2 : H;intros. rewrite inp_all_full_unf H0 //= H //=. 
rewrite inp_all_full_unf H2 /=. lia. 
rewrite inp_all_full_unf H0. ssa. lia. 
rewrite inp_all_full_unf. rewrite H2 /=. apply/orP. right. 
apply/allP. move => x xIn. apply/H1. apply/inP.  done. apply/H0. apply/inP. done. 
Qed.


(*It is hard to show inp -> part_of2 because of structural induction of inp computation clashes with full unfolding of part_of2, so we make an intermediate judgment, part_of3, prove an induction principle*)
Lemma inp_all_iff : forall g p, inp_all p g <-> part_of_all2 p g. 
Proof. 
intros. split;intros.  apply/part_of_all23. apply/inp_part_of_all2. done. 
apply/inp_all_complete. done. 
Qed.




Definition size_pred g := 
match g with 
| GBranch a gs => 0 < size gs 
| _ => true 
end. 

Definition full_geunf ge := (full_unf ge.1,full_eunf ge.2). 
Definition nextge p ge := 
match ge.1 with 
| GMsg a _ g0 => if comp_dir p a then if ge.2 is EMsg _ _ _ e0 then ((g0,e0)::nil) else nil else  ((g0,ge.2)::nil)
| GBranch a gs  => if comp_dir p a then if ge.2 is EBranch  d c es then zip gs es else nil else map (fun g => (g,ge.2)) gs
| _ => nil
end.



Definition nextge_unf p ge :=nextge p (full_geunf ge). 

Definition enumge ge := utils.compose (enumg ge.1) (enum ge.2) pair. 

Definition g_top_act p g := 
match g with 
| GMsg a u _ => if comp_dir p a is Some d then Some (d, action_ch a,inl u) else None
| GBranch a gs => if comp_dir p a is Some d then Some (d, action_ch a,inr (size gs)) else None 
| _ => None
end. 

Definition e_top_act e  := 
match e with 
| EMsg d c u _ => Some (d,c,inl u)
| EBranch d c es => Some (d,c,inr (size es)) 
| _ => None
end. 


Definition project_predP (p : ptcp) (ge : gType * lType) (bs : seq bool) : bool := 
  let ge' := full_geunf ge in 
 if (inp_all p ge.1) && (inp p ge.1) then if g_top_act p ge'.1 is Some l then (Some l == e_top_act ge'.2) && (all id bs) else (size_pred ge'.1) && (all id bs)
  else (has_tree ge.1) && (~~ inp p ge.1) &&  (full_eunf ge'.2 == EEnd).


Lemma enumge_subst_nextg_unf : forall e e' e'' p, e' \in nextge_unf p e -> e'' \in enumge e'  -> e'' \in enumge e.  
Proof. 
intros. rewrite /nextge_unf in H.  rewrite /enumge. destruct e''.
apply mem_compose2 in H0. destruct H0.
destruct e. simpl. destruct e'. simpl in H0,H1.  
have : s1 \in nextg_unf g. 
rewrite /nextge in H. 
rewrite /full_geunf /= in H. rewrite /nextg_unf. 
destruct (full_unf g);try done. 
move : H. case_if. destruct (full_eunf l);try done. 
rewrite inE. move/eqP. case. intros. subst. simpl. auto. 
rewrite inE. move/eqP. case. intros. subst. simpl. auto. 
move : H. case_if. destruct (full_eunf l);try done.  
move/mem_zip. ssa.  move/mapP=>[]. 
intros. inv q. simpl. done. 
intros. 
have : s2 \in (full_eunf l)::(nexte_unf l).
rewrite /nextge in H. 
rewrite /full_geunf /= in H. rewrite /nexte_unf. 
destruct (full_unf g);try done. 
move : H. case_if. destruct (full_eunf l);try done. 
rewrite inE. move/eqP. case. intros. subst. simpl. auto. 
rewrite inE. move/eqP. case. intros. subst. simpl. auto. 
move : H. case_if. destruct (full_eunf l);try done.  
move/mem_zip. ssa.  lia. 
move/mapP=>[]. 
intros. inv q. auto.  
intros. rewrite inE in x0. destruct (orP x0). 
rewrite (eqP H2) in H1. 
apply/mem_compose. apply/enumg_subst_nextg_unf.  eauto. done. 
apply/enum_subst_iter_eunf.  eauto. 
apply/mem_compose. 
apply/enumg_subst_nextg_unf. eauto. done. 
apply/enum_subst_nexte_unf. eauto. done. 
Qed.


Lemma selfge : forall e, e \in enumge e. 
Proof. intros. rewrite /enumge. destruct e. apply/mem_compose=>//=.  
apply/coGlobal.selfe.  apply/selfe. 
Qed. 


Definition gemeasure (ge : gType * lType) (visited : seq ( gType * lType)) := 
size (rep_rem visited (undup (enumge ge))). 
Check nextge_unf. 
Equations pair_next_rec (A : Set ) (p : ptcp) (visited : seq  (gType * lType))  (P : gType * lType -> seq A ->  A) 
    (b : A)  
    (ge : gType * lType): A by wf (gemeasure ge visited) := 
 pair_next_rec p  visited P b ge  with (dec (ge \in visited)) => {
  pair_next_rec _  _ _ _ _ (in_left) := b;
  pair_next_rec p visited  P b ge _ :=  (P ge (foldInMap (nextge_unf p ge) (fun e0 _ => pair_next_rec p (ge::visited) P b e0)))

 }. 
Next Obligation. 
apply/ltP. 
simpl. rewrite /gemeasure /=.
destruct ((g0,l0) \in ((enumge (g,l)))) eqn:Heqn.
apply/size_strict_sub. 
apply/rem_uniq/rep_rem_uniq/undup_uniq. 
intros. destruct (eqVneq x (g0,l0)).  subst. rewrite -mem_rep_iff.  rewrite mem_undup. 
apply/selfge. rewrite e1 //=.
apply mem_rem2 in H;eauto. 
destruct (x \in visited) eqn:Heqn2.
eapply rep_rem_uniq2 in Heqn2. 2 : { apply/undup_uniq. apply (enumge (g,l)). } 
rewrite H in Heqn2. done. 
move : H.  
rewrite -!mem_rep_iff. rewrite  !mem_undup. intros. apply/enumge_subst_nextg_unf.  apply/inP. eauto. 
done. rewrite Heqn2. done. rewrite Heqn2. done. 
instantiate (1 := (g0,l0)).  apply/negP=>HH. rewrite mem_rem_uniqF in HH. done. 
apply/rep_rem_uniq/undup_uniq. 
rewrite -mem_rep_iff.  rewrite mem_undup. apply/enumge_subst_nextg_unf. apply/inP. eauto. done. 
rewrite e1 //=. 
rewrite rem_id. 2 : { 
apply/negP=>HH. move : Heqn. move/negP=>H2. apply/H2.
apply/mem_rep_iff.  apply/negP. clear H2. eauto. apply/rep_rem2. rewrite e1.  done. 
  2 : { eauto. } intros. rewrite mem_undup in H. done.  }
apply/size_strict_sub.  apply/rep_rem_uniq. apply/undup_uniq. 
intros. 2 : {  apply/negP=>HH. move : Heqn. move/negP=>HH2. apply/HH2.
rewrite -mem_undup. 
rewrite mem_rep_iff.  eauto.  rewrite e1 //=. } 
destruct (x \in visited) eqn:Heqn2.
eapply rep_rem_uniq2 in Heqn2. 2 : { apply/undup_uniq. apply (enumge (g,l)). } 
rewrite H in Heqn2. done. 
move : H.  
rewrite -!mem_rep_iff. rewrite  !mem_undup. intros. apply/enumge_subst_nextg_unf.  apply/inP. eauto. 
done. rewrite Heqn2. done. rewrite Heqn2. done. 
rewrite -mem_rep_iff. rewrite mem_undup. apply/selfge.
rewrite e1 //=. 
Defined. 

Lemma has_tree_test : forall g, has_tree g -> has_treeP g nil.
Proof. intros. move : H. rewrite /has_tree. simp next_rec. simpl. 
ssa. move : H. rewrite /has_treeP. ssa. destruct (full_unf g);done. 
Qed. 

Lemma inp_has_treeP : forall g p, inp p g -> has_treeP g nil. 
Proof. intros. apply inp_iff in H.  inv H. rewrite /has_treeP. inv H0. inv H1;ssa. 
Qed.

Lemma projectb_sound_aux : forall g e l p  (R : gType -> lType -> Prop) , pair_next_rec p l (project_predP p) true (g,e) ->  (forall g0 e0, (g0,e0) \in l -> R g0 e0) ->
upaco2 (UnfProj \o  project_gen p) R g e. 
Proof.
intros. 
funelim (pair_next_rec p l (project_predP p) true (g,e)).
right. apply/H0. done. 
rewrite -Heqcall in H0.
left. pcofix CIH.
rewrite {1}/project_predP /= in H0. 
destruct (inp_all p g && (inp p g)) eqn:Heqn. 
pfold. constructor. 

rewrite /nextge_unf in H0.
rewrite foldInMapP in H0.
rewrite /full_geunf /= in H0. 

have : has_treeP g nil. apply/(@inp_has_treeP _ p). move/andP : Heqn. ssa. intros.

rewrite /has_treeP in x. 
destruct (full_unf g) eqn:Heqn2; try solve [ con | done]. 
rewrite inp_all_full_unf in Heqn. rewrite Heqn2 in Heqn. done. 
simpl in H1. ssa. 
destruct (comp_dir p a) eqn:Heqn3. 
ssa. move : H4. move/eqP. destruct (full_eunf e) eqn:Heqn4;try done. 
simpl. case. intros. subst. con. eauto. 
apply/H. 6 : { con. } repeat constructor. 
apply/inP.  rewrite /nextge_unf /full_geunf /=. 
rewrite Heqn2 Heqn4 /=. rewrite /nextge /=. 
rewrite Heqn3 //=. repeat constructor. 
simpl in H5. rewrite /nextge /= in H5. 
rewrite Heqn3 /= in H5. ssa. 
intros. rewrite inE in H0. destruct (orP H0). 
move : H4. move/eqP. case. move=>->->. auto. auto. 

simpl in H0. rewrite /nextge /= in H0. 
rewrite Heqn3 /= in H0. ssa. 
rewrite /id in H4. 
con. done. 
apply/H. 6 : { con. } repeat constructor. 
apply/inP.  rewrite /nextge_unf /full_geunf /=. 
rewrite Heqn2  /=. rewrite /nextge /=. 
rewrite Heqn3 /=. auto. 
repeat constructor. 
rewrite /nextge /= in H4. 
done. 
intros. rewrite inE in H0. 
destruct (orP H0). 
move : H6. move/eqP. case. move=>->->. auto. 
auto. 
apply/inp_all_iff=>//=. rewrite inp_all_full_unf Heqn2 /= Heqn3 //= in H2. 

have : has_treeP g nil. apply/(@inp_has_treeP _ p). move/andP : Heqn. ssa. intros.
rewrite /has_treeP Heqn2 //=in x0. ssa.  
destruct (comp_dir p a) eqn:Heqn3. 
ssa. move : H4.  move/eqP. destruct (full_eunf e) eqn:Heqn4;try done. 
case. intros. subst. con. eauto. 
done. 
rewrite /nextge /= in H5. 
intros. apply/H. repeat constructor. 
rewrite /nextge_unf /full_geunf /= Heqn2 Heqn4 /=. 
rewrite /nextge /= Heqn3 /=. destruct p0.
simpl.  auto. repeat constructor. 

rewrite all_map in H5. apply (allP H5).  

rewrite /nextge  /=  Heqn3 /=.
apply/inP. have : (p0.1,p0.2) = p0. destruct p0. done. move=>->. done. 
intros. rewrite inE in H4. destruct (orP H4). move/eqP : H7. 
case. intros. subst. auto. auto. con. 

intros. have : exists g, In g l.   ssa. destruct l;eauto. done. exists g0. simpl. eauto. move => Hin. destruct Hin. econstructor=>//=. eauto. ssa. apply/inp_all_iff.  rewrite inp_all_full_unf Heqn2 /= Heqn3 /= in H2.  
apply (allP H2). apply/inP. done. 
apply/H. repeat con. 
apply/inP. rewrite /nextge_unf /full_geunf /= Heqn2.
rewrite /nextge /= Heqn3 /=.  
apply/map_f. apply/inP=>//=. repeat con.
apply (allP H7). apply/map_f.

rewrite /nextge /= Heqn3 /=.  apply/map_f. apply/inP. done. 
intros. rewrite inE in H0. destruct (orP H0). 
move/eqP : H8. case. intros. subst. auto. auto. con. 
ssa.  apply/Project_eunf. rewrite full_eunf_idemp in H3. rewrite (eqP H3). 
pfold. con. con. rewrite -part_of2_iff. rewrite -inp_iff. apply/negP=>//=. 
apply/Unravel_gInvPred. rewrite -gUnravel2_iff. apply/next_rec_sound. done. 
Qed.


Lemma Project_not_part2_aux : forall p g e, Project g p e -> ~ part_of2 p g -> EQ2 e  EEnd. 
Proof. 
move => p. 
pcofix CIH. intros. apply part_of2_or_end in H0 as H0'. destruct H0'. 
elim/part_of_all2_ind2 : H e H0  H1;intros. rewrite part_of2_iff H0 in H2.
have : ~ comp_dir p a.  eauto. comp_disc. 
punfold H3. inv H3. rewrite H2 in H5. inv H5. comp_disc. pc.
apply H1. apply/Project_eunf. eauto. rewrite part_of2_iff H2 in H4. eauto. 
pfold. con. rewrite -H6. con. 
rewrite part_of2_iff H0 in H2.
have : ~ comp_dir p a.  eauto. comp_disc. 
rewrite part_of2_iff H2 in H4. punfold H3. inv H3. rewrite H2 in H5. inv H5. comp_disc. 
eapply H1.   eauto. move/H11 : H9. ssa. move/H11 : H9. ssa. pc. apply/Project_eunf. done. 
eauto.  pfold. con. rewrite -H6. con. pfold. con. rewrite H. con. 
Qed. 


Lemma Project_not_part2 : forall p g e, Project g p e -> ~ part_of2 p g -> full_eunf e = EEnd. 
Proof. 
intros. have : EQ2 e EEnd. apply/Project_not_part2_aux;eauto. intros. punfold x. inv x. inv H1. done. 
Qed. 



Lemma projectb_complete_aux: forall g e l p, paco2 (UnfProj \o  project_gen p) bot2 g e -> pair_next_rec p l (project_predP p) true (g,e).  
Proof. 
intros. funelim (pair_next_rec p l (project_predP p) true (g,e)). 
done. 
rewrite -Heqcall foldInMapP. 
rewrite {1}/nextge_unf /full_geunf /=. apply part_of2_or_end in H0 as H0'.  destruct H0'. 
- rewrite {1}/project_predP /=. rewrite -inp_all_iff in H1. rewrite H1. simpl.
  destruct (inp p g) eqn: Hinp. 

punfold H0.  inv H0. 
inv H2=>//=. 
rewrite H5 /=. ssa. 
rewrite /nextge /=. 
rewrite H5 /=. ssa. 
rewrite /id. 

apply/H. repeat con. 
rewrite /nextge_unf /full_geunf /=. 
rewrite -H4 -H3 /nextge /= H5 /=. auto. 
pclearbot. done. con. 
rewrite H4. 
rewrite /nextge_unf /full_geunf /=. 
rewrite /nextge /=  H4 /=. ssa. 
rewrite /id. 

apply/H. repeat con. 
rewrite /nextge_unf /nextge /= -H3 H4 /=.  auto. 
pclearbot. done. con. 

rewrite H5. ssa. 
rewrite H6 //=. 
rewrite /nextge /= H5 /=. 
rewrite all_map. apply/allP=> x xIn. 
simpl. rewrite /id. 
move : H7. move/List.Forall_forall=>HH2. destruct x. 
apply/H. repeat con. 
apply/inP. rewrite /nextge_unf /full_geunf /= -H4 /=. 
rewrite /nextge /= -H3 H5 //=. 
move : xIn. move/inP=>Hin. forallApp HH2 Hin. move => HH3.  pclearbot. simpl in HH3. auto. con. 

rewrite H4. rewrite /nextge /= H4 /=. 
rewrite -map_comp all_map. ssa. destruct gs;try done. 
apply/allP=> x xIn. 
simpl. rewrite /id. apply/H. repeat con. 
apply/inP. rewrite /nextge_unf /full_geunf /= -H3 /=.  
rewrite /nextge /= H4 /=. apply/map_f. done. 
move : xIn. move/inP. move/H6. ssa. pclearbot. done. con. 
rewrite -part_of2_iff in H4. rewrite -inp_iff in H4. rewrite Hinp in H4. done. ssa. 
apply/next_rec_complete_aux. apply/Project_gtree.  eauto. rewrite full_eunf_idemp. apply/eqP. 
apply/ Project_not_part2. eauto. rewrite -inp_iff Hinp //=. 
rewrite H1. rewrite /project_predP /=.  
apply Project_eunf2 in H0. rewrite H1 in H0. apply Project_not_part in H0 as H0'. 
rewrite -inp_iff in H0'. move : H0'. move/negP. move/negbTE.  move=>->.
rewrite andbC /=. rewrite full_eunf_idemp H1 eqxx.    ssa. 

apply/next_rec_complete_aux. apply/Project_gtree. eauto. 
Qed.

Definition projectb g p e := pair_next_rec p nil (project_predP p) true (g,e).

(*Theorem 27*) 
Lemma projectb_iff : forall g p e, projectb g p e <-> Project g p e. 
Proof. 
intros;split.  move/projectb_sound_aux. move=> X.  
suff : upaco2 (UnfProj \o project_gen p) bot2 g e.  case. done. done. apply/X. done. 
apply/projectb_complete_aux. 
Qed.

