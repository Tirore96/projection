From mathcomp Require Import all_ssreflect zify.
From Proj Require Import Utils Syntax Elimination GlobalTree EndpointTree ProjectSpec ProjectDecide.
Require Import Paco.paco.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Let eqs := ProjectSpec.eqs. 


Fixpoint trans p g := 
match g with 
| GMsg a u g0 => if comp_dir p a is Some d then  EMsg d (action_ch a) u (trans p g0) else trans p g0
| GBranch a gs => if comp_dir p a is Some d then EBranch d (action_ch a) (map (trans p) gs) 
                                           else head EEnd (map (trans p) gs)
| GRec g0 => let e := trans p g0 in if eguarded 0 e then ERec e else EEnd
| GVar n => EVar n
| GEnd => EEnd 
end. 

Definition project (g : gType) (p : ptcp) : option endpoint := 
let e := trans p g in if projectb g p e then Some e else None. 

Lemma project_sound_aux : forall g p e, project g p = Some e -> Project g p e. 
Proof. 
intros. rewrite /project in H. move : H. case_if. case. 
move=><-.  apply/projectb_iff. done. done.
Qed.

Lemma project_sound : forall g p e, project g p = Some e -> exists gc ec, Unravelg2 g gc /\ Unravele2 e ec /\ CProject gc p ec. 
Proof. 
intros. move/project_sound_aux : H. move/ICProject_iff=>//=. 
Qed.

(*The rest of this file shows completeness*)


Fixpoint muve e :=
match e with 
| ERec e0 => muve e0
| EVar _ | EEnd => true 
| _ => false 
end.  


(*property for trans recursively defined, so shown by induction on g satisfying muve assuming inp both recursively defined,
 part_of 2 -> inp -> part_of3 ->  part_of2 
 *)
Lemma inp_muve : forall p g, ~~ inp p g  -> muve (trans p g). 
Proof. 
move => p. elim;intros. done. done. 
simpl. 
case_if=>//=. eauto. ssa. rewrite negb_or in H0. ssa. 
destruct (comp_dir p a);try done. eauto. 
simpl in *. rewrite negb_or in H0. ssa. 
destruct (comp_dir p a);try done.
destruct l=>//=.  apply/H.  eauto. 
simpl in *. rewrite negb_or in H2. ssa. 
Qed. 

(*Intermediate judgment that gives us induction principle to show Rolling_no_fv*)
Inductive has_var (n : nat ) :  gType -> Prop := 
 | hv0  : has_var n (GVar n)
 | hv1 a u g0 : has_var n g0 -> has_var n (GMsg a u g0)
 | hv2 g gs a : In g gs -> has_var n g  -> has_var n (GBranch a gs)
 | hv3 g : has_var n (g [g GRec g .: GVar]) ->  has_var n (GRec g).
Hint Constructors has_var. 



Lemma has_var_subst : forall g n n' sigma, has_var n g -> has_var n' (sigma n)  ->  has_var n' g [g sigma]. 
Proof. 
move => g n n' sigma  H. elim : H n' sigma;rewrite //=;intros. 
con. apply/H0. done. simpl. econstructor. apply/inP. apply/mapP. exists g0. apply/inP. done. eauto. 
apply/H1. done. con. asimpl. move/H0 : H1. asimpl. done. 
Qed. 


Fixpoint econtractive2 g := 
match g with
| EVar j => true
| EEnd => true
| EMsg _ _ _ g0 => econtractive2 g0
| EBranch _ _ gs => all econtractive2 gs
| ERec g0 => (eguarded 0 g0) && (econtractive2 g0)
end. 

Lemma project_econtractive2 : forall p g, econtractive2 (trans p g). 
Proof. 
move => p. elim;intros=>//=.  
case_if. ssa.   done. 
destruct (comp_dir _ _);try done. 
destruct (comp_dir _ _);try done. ssa. apply/allP=> x xIn. move/mapP : xIn=>[] //=.  ssa. subst. eauto. 
destruct l;try done. ssa. 
Qed.


Definition leaf e := if e is EEnd then true else if e is EVar _ then true else false. 
Lemma muve_leaf : forall e, econtractive2 e -> muve e -> leaf (full_eunf e).
Proof.
elim;try done.  intros. rewrite full_eunf_subst.
ssa. 
have : leaf (full_eunf e). eauto. intros. rewrite full_unf_com. 
apply eguarded_full_unf in H2.  
destruct (full_eunf e);try done. simpl in *.  
destruct n. simpl. done. done. 
ssa. destruct n. simpl. exfalso. apply/negP. apply/H0. done. 
simpl. done. 
Qed.

Fixpoint gType_fv2 e :=
  match e with
  | GVar j => [:: j]
  | GEnd => nil
  | GMsg _ _ g0 => gType_fv2 g0
  | GBranch _ gs => flatten (map gType_fv2 gs)
  | GRec g0 => map predn (filter (fun n => n != 0) (gType_fv2 g0))
  end.

Definition gclosed g := forall n, n \notin gType_fv2 g.

Lemma gType_fv2_ren : forall g sigma, (gType_fv2 g ⟨g sigma⟩) = map sigma (gType_fv2 g). 
Proof. 
elim;rewrite //=;intros. 
rewrite -!map_comp. rewrite H.
rewrite filter_map /=. clear H. asimpl. 
elim : (gType_fv2 g). done. ssa. 
destruct (eqVneq a 0). subst. simpl. ssa. 
simpl. destruct a. done. simpl. f_equal. done. 
rewrite -!map_comp. rewrite map_flatten. rewrite -!map_comp. 
f_equal. apply/eq_in_map=> x xIn. simpl. auto. 
Qed.

Lemma gType_fv2_subst : forall g sigma, (gType_fv2 g [g sigma]) = flatten (map (sigma >> gType_fv2) (gType_fv2 g)). 
Proof. 
elim;rewrite //=;intros. 
rewrite cats0. asimpl. done. 
rewrite H. rewrite -!map_comp. 
asimpl. rewrite filter_flatten.
rewrite -!map_comp. rewrite !map_flatten.
rewrite -map_comp.
rewrite /comp. asimpl. clear H.
elim : ( gType_fv2 g);try done. ssa. 
destruct (eqVneq a 0). simpl. subst. simpl. done. 
simpl. destruct a. done. simpl.
f_equal. asimpl. rewrite gType_fv2_ren. 
rewrite filter_map /=. rewrite -map_comp.
clear i.  clear H. 
elim : ( gType_fv2 (sigma a));try done. ssa. 
f_equal. done. done.  

rewrite -map_comp. 
rewrite !map_flatten.  rewrite -!map_comp. 
rewrite /comp. asimpl. 
elim : l H. done. ssa. simpl.
rewrite flatten_cat. f_equal. auto. apply/H. auto. 
Qed.


Lemma has_varP : forall g n, n \in gType_fv2 g -> has_var n g. 
Proof. 
elim=>//=;intros;auto. rewrite inE in H. rewrite (eqP H). done. 
con. move : H0. move/mapP=>[]. intros. subst. rewrite mem_filter in p. ssa. 
destruct x;try done. simpl. 
move/H : H1. intros. apply/has_var_subst. eauto. simpl. con. 
move/flattenP : H0=>[] x. move/mapP=>[]. intros. subst. econstructor. 
apply/inP. eauto. eauto. 
Qed.

(*Cool Trick, when going from coinductive to negation of some structurally recursive boolean,
 intermediate step is to show boolean implies inductive unfolding judgment,
 it's negation is introduced into the context and the proof can be by induction on that.
 The technique informally says from the coinductive Rolling judgment and a proof
 that we will observe a variable in finite time, we can reach a contradiction,
 so there can be no free variables.
*)
Lemma Rolling_no_fv : forall g, Rolling g -> (forall n, n \notin gType_fv2 g).
Proof. 
intros. apply/negP. move/has_varP=>HH. elim : HH H;intros. 
punfold H. inv H. inv H0. punfold H1. punfold H2. 
punfold H1. inv H1. rewrite full_unf_subst in H2. apply/H0. 
pfold. con. done. 
Qed.


Fixpoint endpoint_fv2 e :=
  match e with
  | EVar j => [:: j]
  | EEnd => nil
  | EMsg _ _ _ g0 => endpoint_fv2 g0
  | EBranch _ _ gs => flatten (map endpoint_fv2 gs)
  | ERec g0 => map predn (filter (fun n => n != 0) (endpoint_fv2 g0))
  end.

Definition eclosed e := forall n, n \notin endpoint_fv2 e.

Lemma endpoint_fv2_ren : forall g sigma, (endpoint_fv2 g ⟨e sigma⟩) = map sigma (endpoint_fv2 g). 
Proof. 
elim;rewrite //=;intros. 
rewrite -!map_comp. rewrite H.
rewrite filter_map /=. clear H. asimpl. 
elim : (endpoint_fv2 e). done. ssa. 
destruct (eqVneq a 0). subst. simpl. ssa. 
simpl. destruct a. done. simpl. f_equal. done. 
rewrite -!map_comp. rewrite map_flatten. rewrite -!map_comp. 
f_equal. apply/eq_in_map=> x xIn. simpl. auto. 
Qed.

Lemma endpoint_fv2_subst : forall g sigma, (endpoint_fv2 g [e sigma]) = flatten (map (sigma >> endpoint_fv2) (endpoint_fv2 g)). 
Proof. 
elim;rewrite //=;intros. 
rewrite cats0. asimpl. done. 
rewrite H. rewrite -!map_comp. 
asimpl. Search _ ((filter _ (flatten _))). rewrite filter_flatten.
rewrite -!map_comp. rewrite !map_flatten.
rewrite -map_comp.
rewrite /comp. asimpl. clear H.
elim : ( endpoint_fv2 e);try done. ssa. 
destruct (eqVneq a 0). simpl. subst. simpl. done. 
simpl. destruct a. done. simpl.
f_equal. asimpl. rewrite endpoint_fv2_ren. 
rewrite filter_map /=. rewrite -map_comp.
clear i.  clear H. 
elim : ( endpoint_fv2 (sigma a));try done. ssa. 
f_equal. done. done.  

rewrite -map_comp. 
rewrite !map_flatten.  rewrite -!map_comp. 
rewrite /comp. asimpl. 
elim : l H. done. ssa. simpl.
rewrite flatten_cat. f_equal. auto. apply/H. auto. 
Qed.




Lemma endpoint_fv2_eunf : forall g n, (n \in endpoint_fv2 g) = (n \in endpoint_fv2 (eunf g)).  
Proof. 
case=>//=. intros. rewrite endpoint_fv2_subst. 
apply/eq_iff. split. move/mapP=>[] x /=. rewrite mem_filter. ssa. subst. 
apply/flattenP. destruct x;try done. simpl. 
have : ((ERec e .: EVar) >> endpoint_fv2) = 
([seq i.-1 | i <- endpoint_fv2 e & i != 0] .: fun n => [::n]).
asimpl. simpl. f_equal. move=>->.
exists ([::x]). 
apply/mapP. exists x.+1. ssa. simpl. done. done. 
move/flattenP=>[] x. move/mapP=>[] x0. intros. subst. destruct x0;try done.  
move : q0. asimpl. simpl. rewrite inE. move/eqP. intros. subst. apply/mapP. exists x0.+1=>//=. 
rewrite mem_filter. ssa. 
Qed.

Lemma endpoint_fv2_full_eunf : forall g n, (n \in endpoint_fv2 g) = (n \in endpoint_fv2 (full_eunf g)).  
Proof. 
intros. rewrite /full_eunf. remember (emu_height g). clear Heqn0. elim : n0 g. done. 
intros. rewrite iterS. rewrite H. apply/endpoint_fv2_eunf. 
Qed.



Lemma fv_proj : forall g p n, n \in endpoint_fv2 (trans p g) -> n \in gType_fv2 g. 
Proof. 
elim=>//=;intros. 
move : H0. case_if. simpl. move/mapP=>[] . intros. subst. rewrite mem_filter in p0. ssa. 
destruct x;try done. simpl. apply/mapP. exists x.+1=>//=. rewrite mem_filter. ssa. eauto. 
done. 
move : H0. destruct (comp_dir _ _);try done. ssa. eauto.  
eauto. 
move : H0. destruct (comp_dir _ _);try done. ssa. move : H0. 
move/flattenP=> [] x. rewrite -!map_comp. move/mapP=>[]. intros. subst.  apply/flattenP. 
move : q0. rewrite /comp.  move/H. move/(_ p0)=>HH.  
exists (gType_fv2 x0)=>//=. apply/map_f. done. 
destruct l;try done. 
ssa. rewrite mem_cat. apply/orP. left. apply/H=>//=. eauto. 
Qed.

Lemma fv_proj_not : forall g p n, n \notin gType_fv2 g -> n \notin endpoint_fv2 (trans p g).
Proof. 
intros. apply/negP. move => HH. apply/negP. apply/H. apply/fv_proj. eauto. 
Qed. 



Lemma EQ_end_aux : forall p g, Rolling g -> ~~ inp p g -> full_eunf (trans p g) = EEnd.  
Proof. 
intros. apply inp_muve in H0. 
move : (@project_econtractive2 p g)=>HH. 
have : leaf (full_eunf (trans p g)).  apply/muve_leaf. eauto. done. 
intros. destruct (full_eunf (trans p g)) eqn:Heqn;try done. Check Rolling_no_fv.
move/Rolling_no_fv : H. move/(_ n). move/fv_proj_not.
move/(_ p). 
rewrite endpoint_fv2_full_eunf Heqn /= inE.  lia. 
Qed. 





Theorem EQ_end : forall p g, ~ part_of2 p g -> Rolling g ->
  EEnd << (ApplyF full_eunf full_eunf \o EQ2_gen) >> (trans p g).
Proof. 
intros. apply/EQ2_eunf. erewrite  EQ_end_aux. pfold. con. con. done. apply/negP. move => HH. apply H. 
apply/inp_iff. done. 
Qed. 


(*Switch from eguarded because we have a comm lemma on renaimg without strong assumption prevents doing the same in project_subst*)
Lemma project_ren : forall p g sigma, injective sigma ->  trans p g ⟨g sigma ⟩ = (trans p g) ⟨e sigma ⟩. 
Proof. 
move => p. elim;intros;asimpl.  
simpl. done. 
done. 
simpl. rewrite H. 
have : injective (0 .: sigma >> succn). auto. move/eguarded_ren_iff. 
move/(_ (trans p g) 0)=>/=. move/eq_iff=><-. case_if=>//=. auto. 
asimpl. simpl. destruct (comp_dir _ _);try done. simpl. rewrite H. done. done. 
auto. simpl. destruct (comp_dir _ _);try done. simpl. rewrite -!map_comp. 
f_equal. apply/eq_in_map=> x xIn. simpl. auto. 
rewrite -!map_comp. destruct l. done. simpl. rewrite H. auto. done. done. 
Qed. 


Lemma eguarded_sig2 : forall g sigma sigma' i, eguarded i g [e sigma] -> (forall n, eguarded i (sigma n) -> eguarded i (sigma' n)) -> eguarded i g [e sigma'].
Proof.
elim;rewrite /=;intros;try done.
apply H0. done.
asimpl. apply : H. eauto. move => n.  asimpl. simpl. intros. destruct n. done. simpl in *.
move : H. rewrite /funcomp. specialize H1 with n. move : H0. asimpl.
intros. rewrite -eguarded_ren_iff. move : H. rewrite -eguarded_ren_iff.  move/H1. done. 
done. done. 
Qed.


Lemma  eguarded_fv : forall g v, v \notin endpoint_fv2 g -> eguarded v g.
Proof.
elim;rewrite /=;try done;intros.
rewrite !inE in H. lia.
apply H. move : H0. intros. apply/negP=>HH'. apply/negP. apply H0. apply/mapP. exists v.+1. rewrite mem_filter. ssa. done. 
Qed.
 
Lemma project_subst  : forall p g sigma, trans p g [g sigma ] = (trans p g) [e sigma >> trans p ]. 
Proof. 
move => p. elim;intros;asimpl.  
simpl. done. 
done. 
simpl.  rewrite H. asimpl. simpl. 
symmetry.  case_if. 
have :  eguarded 0 (trans p g) [eEVar 0 .: sigma >> (⟨g ↑ ⟩ >> trans p)]. apply/eguarded_sig2. 
instantiate (1 := EVar). asimpl. done. case. done. simpl. intros. asimpl. rewrite project_ren //=. 
apply/eguarded_fv. rewrite endpoint_fv2_ren. 
apply/negP=>HH. move/mapP : HH. case. ssa. 
move=>->. simpl. f_equal. asimpl. simpl. f_equal. fext. case.  done. move => n. simpl. asimpl. 
rewrite project_ren //=.
have :  eguarded 0 (trans p g) [eEVar 0 .: sigma >> (⟨g ↑ ⟩ >> trans p)] = false. 
apply/negP=>HH. move : H0.  move/negP=>H2. apply H2. 
eapply (@eguarded_sig2 _ _ EVar)  in HH.  move : HH. asimpl. done. 
case. simpl. done. 
move => n. asimpl. simpl. done. 
move=>->. done. 
simpl. 
destruct (comp_dir _ _);try done. simpl. rewrite H. done. 
simpl. destruct (comp_dir _ _);try done. simpl. rewrite -!map_comp. 
f_equal. apply/eq_in_map=> x xIn. simpl. auto. 
rewrite -!map_comp. destruct l. done. simpl. rewrite H. auto. done. 
Qed.


(*We need guarded false implies funf = var here*)
(*full_unf_com also*)
Lemma proj_eq : forall p g, full_eunf (trans p g) = full_eunf (trans p (unf g)).  
Proof. 
intros. destruct g;try done;simpl;auto. 
case_if. simpl. rewrite full_eunf_subst.   rewrite project_subst. 
asimpl. simpl. rewrite H. f_equal. remember H. clear Heqe. cbn. 
rewrite project_subst. asimpl. rewrite /= H.
apply eguarded_unfv in H. 
rewrite full_unf_com. rewrite H. asimpl. done. 
case.  done. simpl.  done. 
Qed.

Theorem proj_eq_full : forall p g, full_eunf (trans p g) = full_eunf (trans p (full_unf g)).  
Proof. 
intros. 
rewrite /full_unf. remember (mu_height g). clear Heqn. 
elim : n g;try done. intros. rewrite iterS. rewrite -proj_eq. eauto. 
Qed.

Lemma project_project : forall p g e, Project g p e -> EQ2 e (trans p g). 
Proof. 
move => p. pcofix CIH. intros. 
apply part_of2_or_end in H0 as H0'. destruct H0'.
elim/part_of_all2_ind2 : H e H0;intros. 
punfold H1. inv H1. rewrite H0 in H2. 
inv H2;pc;try comp_disc. 
pfold. con. rewrite proj_eq_full H0 /= H5. cbn. rewrite -H7. con. eauto. 
apply/EQ2_eunfl. rewrite -H3. 
apply/paco2_mon. instantiate (1 := bot2);try done. 2 : { done. } 
have : ~ comp_dir p a by eauto. comp_disc. 
punfold H3. inv H3. rewrite H2 in H4. inv H4; try comp_disc;pc. 
apply/EQ2_eunf. rewrite proj_eq_full H2 /= H8. 
apply/EQ2_eunf2. apply/H1.   apply/Project_eunf. eauto. 
apply EQ2_eunfl. rewrite -H5. clear H5. 
apply/paco2_mon. apply/EQ_end. rewrite part_of2_iff H2 //=. 
rewrite Rolling_iff H2 //=. done. 

punfold H1. inv H1. rewrite H0 in H2. inv H2;pc;try comp_disc. 
pfold. con. rewrite -H5. rewrite proj_eq_full. rewrite H0 /= H6. cbn. con. rewrite size_map //=. 
move/ForallP : H8. clear H0 H6 H5 H2. 
elim : gs es H7. case=>//=.  
move => a0 l IH. case=>//=. move => a1 l0 [] Heq. intros. inv H8. pclearbot. simpl in *. con;eauto. 
apply/EQ2_eunfl. rewrite -H3. apply/paco2_mon. apply/EQ_end. 
rewrite part_of2_iff.  rewrite H0 //=. 
rewrite Rolling_iff H0 //=. done. 
punfold H3. inv H3. rewrite H2 in H4. inv H4; try comp_disc;pc. 
apply/EQ2_eunf. rewrite proj_eq_full H2 /=.  rewrite H7. 
destruct gs;try done. simpl. apply/EQ2_eunf2.  apply/H1. simpl. left. done. 
apply /H0. simpl. auto. 
have : In g1 (g1 :: gs). simpl. auto. 
move/H10. ssa. pclearbot. apply/Project_eunf. done. 
apply/EQ2_eunfl. rewrite -H5. apply/paco2_mon. apply/EQ_end.
rewrite part_of2_iff.  rewrite H2 //=. 
rewrite Rolling_iff H2 //=. done. Search _ (Project _ _ EEnd). 
apply Project_eunf2 in H0. rewrite H in H0. apply Project_not_part in H0 as H0'. 
apply/EQ2_eunfl. rewrite H. 
apply/paco2_mon. apply/EQ_end. done. apply/Unravelg2_Rol. apply/Project_gtree.   eauto. 
done. 
Qed.


Lemma Project_EQ2 : forall p g e0 e1, Project g p e0 -> EQ2 e0 e1 -> Project g p e1. 
Proof. 
move => p. 
pcofix CIH. intros. apply part_of2_or_end in H0 as H1'.  destruct H1'. 
elim/part_of_all2_ind2 : H e0 e1 H0 H1;intros. 
punfold H1. inv H1. rewrite H0 in H3. inv H3;try comp_disc;pclearbot. 
punfold H2. inv H2. rewrite -H8 in H4. inv H4. apply/Project_unfg. apply/Project_eunf. 
rewrite -H13. rewrite H0. pclearbot. pfold.  con=>//=. con=>//=. eauto. 
punfold H2. inv H2. rewrite -H4 in H6. apply/Project_eunf. inv H6. pfold. con. con. 
rewrite H0. done. rewrite H0. done. 
punfold H3. inv H3. rewrite H2 in H5. inv H5;try comp_disc;pclearbot. 
apply/Project_unfg. rewrite H2. pfold. con. con. comp_disc.  left. apply/H1. eauto.
pfold. con. rewrite !full_eunf_idemp. punfold H4.  inv H4. done. done. 
punfold H4. inv H4. rewrite -H6 in H8. apply/Project_eunf. inv H8. 
pfold. con. con. rewrite H2. eauto. rewrite H2. eauto. 
punfold H1. inv H1. rewrite H0 in H3. 
inv H3; try comp_disc;pc. punfold H2. inv H2. rewrite -H6 in H4. 
apply/Project_eunf. apply/Project_unfg. rewrite H0. inv H4. pfold. con. con=>//=. lia. 
apply/ForallP.  move/ForallP : H9. clear H13 H6 H4 H0 H3. elim : gs es es1 H8 H11 H14.  
case=>/=. case=>//=. move => a0 l. case=>//=. 
move => a0 l IH. case=>//=. move => a1 l0 [] //=. 
move => a2 l1. move => [] Heq0 [] Heq1. intros. inv H14. inv H9. pclearbot. simpl in *. 
con;eauto. 
punfold H2. inv H2.  rewrite -H4 in H6. pfold. con. inv H6. con. rewrite H0. done. 
rewrite H0. done. 
punfold H3. inv H3. rewrite H2 in H5. punfold H4. inv H4. 
inv H5;try comp_disc;pc.
apply Project_unfg.  rewrite H2. pfold. con. econstructor=>//=. eauto. 
intros. ssa. left. apply/H1;eauto.  move/H12 : H7. ssa. pclearbot. eauto. 
pfold. con. rewrite !full_eunf_idemp. done. 
rewrite -H7 in H6. apply/Project_eunf. inv H6. pfold. con. con. 
rewrite H2. eauto. 
rewrite H2. eauto. 
punfold H1. inv H1. rewrite H in H2. pfold. con. inv H2. 
punfold H0. inv H0. rewrite H in H4. 
apply/project_gen_mon. eauto. move => x0 x1 [] //=. 
intros. left. apply/paco2_mon. eauto. done. 
Qed.


Lemma project_complete : forall g p e, Project g p e -> exists e', EQ2 e e' /\ project g p = Some e'.
Proof. intros. 
exists (trans p g). ssa. apply project_project=>//=. 
rewrite /project. eapply Project_EQ2 in H.  2 : apply/project_project;eauto.  move/projectb_iff : H=>->//=. 
Qed. 


Lemma EQ2_EQ : forall e0 e1, EQ2 e0 e1 -> paco2 EQ_gen bot2 (etocoind e0) (etocoind e1).
Proof. 
pcofix CIH. intros.  punfold H0. inv H0. 
rewrite etocoind_full_eunf. rewrite (etocoind_full_eunf e1). inv H;seq. pfold. con. 
pfold. con. pc. eauto. 
pfold. con. clear H1 H2.  apply/Forall_ForallC. rewrite !size_map //=. elim : es0 es1 H3 H4. case=>//=.
move=> a l IH []//=. move => a0 l0 [] Heq. intros. inv H4. pclearbot. simpl in *. con;eauto. 
Qed.




Lemma CProj_Unravel : forall p g gc ec, Unravelg2 g gc ->  CProject gc p ec -> paco2 EQ_gen bot2 ec (etocoind (trans p g)). 
Proof. 
move => p. pcofix CIH. 
intros. apply part_of_or_end in H1 as H1'. destruct H1'.
move/ICpart_of_all2_iff : H=>g0.  
have : part_of_all2 p g. apply/g0. done. 
clear g0=>HH. 
elim/part_of_all2_ind2 : HH gc ec H1 H0;intros. 
- rewrite etocoind_full_eunf. rewrite proj_eq_full H0 /=.  destruct (comp_dir p a) eqn:Heqn;try done. cbn. 
  punfold H2. inv H2. rewrite H0 in H3. inv H3. punfold H1. inv H1;try comp_disc;pc. 
  rewrite Heqn in H9. inv H9. pfold. seq. con=>//=. eauto. 
  have : ~ comp_dir p a by eauto. comp_disc. 

- rewrite etocoind_full_eunf. rewrite proj_eq_full H2 /=.  destruct (comp_dir p a) eqn:Heqn;try done.
  punfold H4. inv H4. rewrite H2 in H5. inv H5;pc. punfold H3. inv H3;pc;try comp_disc. 
  rewrite -etocoind_full_eunf.   apply/H1; eauto. 
  rewrite -etocoind_full_eunf.   apply/H1; eauto. pfold. con;eauto. 

- rewrite etocoind_full_eunf. rewrite proj_eq_full H0 /=.  destruct (comp_dir p a) eqn:Heqn;try done. cbn. 
  punfold H2. inv H2. rewrite H0 in H3. inv H3. punfold H1. inv H1;try comp_disc;pc. injt. 
  rewrite Heqn in H7. inv H7. pfold. seq. con.  
  rewrite -map_comp. clear H3 H2 H1  H7 H0. apply/Forall_ForallC. rewrite size_map//=. lia. 
  move/ForallP : H11. elim : gs ecs es H6 H9 H8. case=>//=. case=>//=.
  move => a0 l IH.   case=>//=. move => a1 l0 [] //=. move => a2 l1 [] Heq [] Heq2. intros. 
  inv H8. inv H11. pclearbot. simpl in *. con;eauto. 
  have : ~ comp_dir p a by eauto. comp_disc. 

- rewrite etocoind_full_eunf. rewrite proj_eq_full H2 /=.  destruct (comp_dir p a) eqn:Heqn;try done.
  punfold H4. inv H4. rewrite H2 in H5. inv H5;pc. punfold H3. inv H3;pc;try comp_disc. injt.
  destruct gs;try done. destruct ecs;try done. simpl. 
  rewrite -etocoind_full_eunf. destruct ecs;try done. inv H10.  pclearbot. simpl in *. 
  apply/H1. simpl. eauto. apply/H0.  simpl. eauto. 2 : eauto. 
  have : g2 = g2 \/ In g2 ecs. eauto. move/H13. ssa. pclearbot. done. 

  destruct gs;try done. destruct ecs;try done. simpl. seq. pfold. con.
  rewrite -etocoind_full_eunf. simpl.
  inv H10. destruct ecs;try done. destruct H11;try done. destruct ecs;try done.  simpl in *. inv H9.  
  simpl in *.
  apply/H1. simpl. eauto. apply/H0.  simpl. eauto. 2 : eauto. pfold. con. 
  move => HH. apply H6. econstructor 4.  2 : eauto. con.  done. 
  punfold H7. inv H7. injt. inv H14. pclearbot. done.  

-  subst.  apply CProject_not_part in H1. have : ECEnd = etocoind EEnd. seq. done. 
  move=>->. apply/paco2_mon. apply/EQ2_EQ. apply/project_project. pfold. con. con.
  rewrite -part_of2_iff. 
  rewrite ICpart_of_iff. eauto. eauto. 
  rewrite -Rolling_iff. 
  apply/Unravel_Rolling.  eauto. done.
Qed.




Lemma inotin : forall g i sigma, (forall n, i !=  sigma n) -> i \notin endpoint_fv2 g ⟨e sigma ⟩.
Proof.
elim;rewrite /=;try done;intros. rewrite !inE. specialize H with n. lia.
apply/negP. move/mapP. case. ssa. subst. rewrite mem_filter in p. ssa. 
destruct x;try done. ssa. apply/negP. apply/H. 2 : eauto. asimpl. intros.
destruct n. done. ssa. asimpl. move: (H0 n).  lia. 
apply/negP. move/flattenP. case. move=> x. rewrite -map_comp. move/mapP.  case. intros. subst. 
apply/negP. apply/H. eauto. eauto. done. 
Qed.

Lemma econtractive2_ren : forall g sigma, injective sigma -> (forall n, n <= sigma n) ->  econtractive2  g -> econtractive2 g ⟨e sigma ⟩.
Proof.
elim;intros;simpl;try done. 
asimpl. split_and. have : 0 = ( 0 .: sigma >> succn) 0. done. intros. rewrite {1}x.
apply eguarded_ren. auto. ssa. apply/H=>//=. auto. intros. destruct n. simpl. done. ssa. asimpl. move : (H1 n). lia. ssa. ssa. 
rewrite all_map. apply/allP. intro. intros. simpl. apply H. done.  done. done.  simpl in H2. apply (allP H2). done.
Qed.


Lemma econtractive2_subst : forall g sigma,econtractive2 g -> (forall n, econtractive2 (sigma n)) -> econtractive2 g [e sigma].
Proof. 
elim;rewrite /=;intros;try done. 
asimpl. split_and. 
apply/eguarded_sig2.
instantiate (1 := (EVar 0 .: EVar  >>  ⟨e ↑ ⟩)).  asimpl. done.
case. done. simpl. intros. apply/eguarded_fv. asimpl. apply/inotin. done.
apply H. done.  intros. destruct n.  done. simpl. asimpl.  apply/econtractive2_ren. done. done. done.
apply H. done.  intros. done. 
rewrite all_map. apply/allP. intro. intros. simpl. apply H. done. apply (allP H0). done. done.
Qed.





(*Lemma emu_height_subst : forall g0 sigma, (forall n, 0 < emu_height (sigma n) -> eguarded n g0) -> econtractive2 g0 -> emu_height (g0[e sigma]) = emu_height g0.
Proof. 
elim; try solve [by rewrite /=];intros.
asimpl. move : (H n). destruct (emu_height (sigma n)) eqn:Heqn. done. have : 0 < n0.+1 by lia. move => + HH. move/HH=>//=. lia. 
simpl. f_equal. asimpl. apply H. case. rewrite //=. move=> n/=. move => HH. apply/H0. move : HH. asimpl. rewrite emu_height_ren //=. ssa. 
Qed.*)








Lemma econtractive_unf : forall g , econtractive2 g -> econtractive2 (eunf g). 
Proof.
intros. rewrite /eunf. destruct g;try done. apply/econtractive2_subst. ssa. case;done. 
Qed.

Lemma econtractive_iter_unf : forall k g , econtractive2 g -> econtractive2 (iter k eunf g). 
Proof.
elim;try done. intros. simpl. apply/econtractive_unf. ssa. 
Qed.

Lemma econtractive_full_eunf : forall g , econtractive2 g -> econtractive2 (full_eunf g). 
Proof. 
intros. rewrite /full_eunf. apply/econtractive_iter_unf. done. 
Qed.

Lemma emu_height_subst_contractive : forall g0 sigma, (forall n, 0 < emu_height (sigma n) -> eguarded n g0) -> econtractive2 g0 -> emu_height (g0[e sigma]) = emu_height g0.
Proof. 
elim; try solve [by rewrite /=];intros.
asimpl. move : (H n). destruct (emu_height (sigma n)) eqn:Heqn. done. have : 0 < n0.+1 by lia. move => + HH. move/HH=>//=. lia. 
simpl. f_equal. asimpl. apply H. case. rewrite //=. move=> n/=. move => HH. apply/H0. move : HH. asimpl. rewrite emu_height_ren //=. ssa. 
Qed.

Lemma emu_height_unf_contractive : forall g , econtractive2 g -> (emu_height g).-1 = emu_height (eunf g).
Proof.
move => g. rewrite /=. case : g; try solve [intros;rewrite /=;done].
intros. rewrite /=. ssa. erewrite emu_height_subst_contractive. done. eauto. case. done. done. done. 
Qed.

Lemma emu_height_iter_unf : forall k g , econtractive2 g -> (emu_height g) - k = (emu_height (iter k eunf g)). 
Proof.
elim;intros. rewrite /=. lia.
rewrite /=. have : emu_height g - n.+1 = (emu_height g - n).-1 by lia. move=>->. 
erewrite H. rewrite emu_height_unf_contractive //=.  apply/econtractive_iter_unf.  done. done. 
Qed.

Lemma iter_eunf_not_rec : forall g k, econtractive2 g -> emu_height g <= k -> forall g', iter k eunf g <> ERec g'.
Proof.
intros. simpl in *. apply (emu_height_iter_unf k) in H. move : H. 
have : emu_height g - k  = 0 by lia. move=>->. intros. destruct (iter k eunf g);try done.
Qed.

Lemma full_eunf_not_rec : forall g, econtractive2 g -> forall g', full_eunf g <> ERec g'.
Proof.
intros. apply/iter_eunf_not_rec. done. done. 
Qed.

Lemma to_Rollinge : forall e, (forall n, n \notin endpoint_fv2 e) -> econtractive2 e -> Rollinge e. 
Proof. 
pcofix CIH. 
intros. pfold. con. remember H1 as Hcont. clear HeqHcont. 
apply econtractive_full_eunf in H1.
have : forall n : nat_eqType, n \notin endpoint_fv2 (full_eunf e). 
intros. rewrite -endpoint_fv2_full_eunf. done. clear H0=>H0.
destruct (full_eunf e) eqn:Heqn. 
move : (H0 n). ssa. lia. con. 
con. right. apply/CIH. ssa. ssa. 
con. 
ssa. 
apply/ForallP=> x xIn. right. apply/CIH.
intros. apply/negP=> HH. apply (negP (H0 n)). apply/flattenP. exists (endpoint_fv2 x)=>//=. 
apply/map_f. apply/inP. done. 
apply (allP H1). apply/inP. done.
move : (@ full_eunf_not_rec e  Hcont e0) =>Heq. 
exfalso. apply/Heq. done. 
Qed.

(*Lemma 11 in the paper*)
Locate Unravele.
Print Unravele. 
Lemma Unraveling_of_trans : forall g p, gclosed g ->  paco2 (UnfUnravele \o Unravele2_gen) bot2 (trans p g) (etocoind (trans p g)).
Proof. 
intros. apply/Rolling_Unravele. apply/to_Rollinge. intros. apply/fv_proj_not=>//=.
apply/project_econtractive2.
Qed.

(*Lemma Rolling_proj : forall p g, Rolling g -> Rollinge (trans p g). 
Proof. 
intros. apply/to_Rollinge. intros. apply/negP. move/fv_proj=>HH. 
move/Rolling_no_fv : H. move/(_ n). rewrite HH //=.   
apply/project_econtractive2. 
Qed.*)

Lemma CProject_EQ : forall p g e0 e1, CProject g p e0 -> paco2 EQ_gen bot2 e0 e1 -> CProject g p e1. 
Proof. 
move => p. 
pcofix CIH. intros. apply part_of_or_end in H0 as H1'.  destruct H1'. 
elim/part_of_all_ind2 : H e0 e1 H0 H1;intros. 
punfold H0. inv H0;try comp_disc;pc.  punfold H1. inv H1;pc.  pfold. con=>//=. eauto. 
have : ~ comp_dir p a. eauto. comp_disc. 

punfold H2. inv H2; try comp_disc;pc. pfold. con=>//=. left.  apply/H1;eauto.  
pfold. con=>//=. comp_disc. left. apply/H1. 2 : eauto. pfold. con. eauto. eauto. 

punfold H0. inv H0;try comp_disc;pc.  punfold H1. inv H1. 
pfold. destruct (comp_dir p a) eqn:Heqn. apply coerce_forall in H9.  
destruct H9. ssa. subst. con=>//=.  inv H4. comp_disc.  lia. 
eauto. 
apply/ForallP.  move/ForallP :H7. move : H6.  inv H4. 
clear Heqn H4 H1 H0. 
elim : gs0 es x H5 H2. case=>//=. case=>//=. 
move => a0 l IH. case=>//=. move => a1 l0. case=>//=. 
move => a2 l1 [] Heq [] Heq1. intros. inv H6. inv H7. pclearbot. simpl in *. 
con;eauto. 
done. 

punfold H1. inv H1. pfold. con.  eauto. eauto. 
punfold H2. inv H2; try comp_disc;pc.  injt. 
pfold. econstructor. done. eauto. intros.  ssa. left. apply/H1;eauto.  
move/H9 : H4. ssa. pclearbot. eauto. 
punfold H3. inv H3. pfold. con. eauto. done. 
punfold H1. subst. 
punfold H0. inv H0;pc. pfold. con=>//=. right. eauto. 
pfold. econstructor;eauto. ssa. move/H3 : H4. ssa. 
move/H3 : H4. ssa. pclearbot. right. apply/CIH. eauto. pfold. done. 
inv H1. pfold. con. done. done. 
Qed.


Lemma project_complete2 : forall gc p ec g, CProject gc p ec -> Unravelg2 g gc -> exists e, Unravele2 e ec  /\ project g p = Some e. 
Proof. 
intros. exists (trans p g). ssa. 
apply/Unravele_iff.
suff : exists ec', (trans p g) << Unravele_gen >> ec'. case. 
intros. have :  paco2 EQ_gen bot2 ec (etocoind (trans p g)). apply/CProj_Unravel. eauto. done. 
intros. apply/Unravele_iff.  apply/Unravele_eq. apply/EQ_sym. eauto.  
apply/Rolling_Unravele. 
apply/Rolling_proj. apply/Unravel_Rolling. eauto.
exists (etocoind (trans p g)).
apply/Unravele_iff. apply/Rolling_Unravele. apply/Rolling_proj. 
apply Unravel_Rolling in H0. done. 
rewrite /project. case_if. done. 
exfalso. have : ~  projectb g p (trans p g) .  destruct ( projectb g p (trans p g) );try done. 
intros. apply / x. clear H1. 
apply/projectb_iff.
apply/ICProject_iff. exists gc. exists (etocoind (trans p g)). ssa.
apply/Rolling_Unravele. apply/Rolling_proj. apply/Unravel_Rolling. eauto.
apply/CProject_EQ. eauto. apply/CProj_Unravel. eauto. done.
Qed.






