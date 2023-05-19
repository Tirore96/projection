
From mathcomp Require Import all_ssreflect zify.

From IndTypes Require Export elimination.
Require Import Paco.paco.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition unf g := if g is GRec g' then g' [g g.:var]  else g.


Lemma mu_height_ren : forall g sigma, mu_height g ⟨g sigma ⟩  = mu_height g.
Proof.
elim;rewrite /=;try done;intros.
f_equal. apply : H. 
Qed.

Lemma mu_height_subst : forall g0 sigma, (forall n, ~~ guarded n g0 -> mu_height (sigma n) = 0) ->  mu_height (g0[g sigma]) = mu_height g0.
Proof. 
elim; try solve [by rewrite /=];intros.
asimpl. move : (H n). destruct (mu_height (sigma n)) eqn:Heqn. done. have : 0 < n0.+1 by lia. move => + HH. simpl. 
simpl in HH. lia. 
simpl. f_equal. asimpl. apply H. case. done.  simpl. intros. asimpl. rewrite mu_height_ren. apply/H0. done. 
Qed.


Lemma mu_height_unf : forall g , guarded 0 g -> (mu_height g) = mu_height (g [g GRec g .: GVar]).
Proof.
move => g. rewrite /=. case : g; try solve [intros;rewrite /=;done].
intros. rewrite /=. destruct n. done. done. ssa. erewrite mu_height_subst. done. case. done. 
intros. simpl. asimpl. destruct n. lia.  simpl. done. 
Qed.

Lemma mu_height_unf2 : forall g sigma i, ~~ guarded i g -> (mu_height g) + mu_height (sigma i) = mu_height (g [g sigma]).
Proof. 
elim;rewrite //=;intros. have : n = i by lia.  intros. subst. lia. 
asimpl. erewrite <- H. 2 : { eauto. } simpl. asimpl. rewrite mu_height_ren. lia. 
Qed.


Lemma guarded_test : forall e sigma i,  ~~ guarded i e -> iter (mu_height e) unf e [ sigma ] = sigma i. 
Proof. 
elim;rewrite //=;intros. 
have : n = i. lia.  move=>->. done.  asimpl. rewrite -iterS iterSr. simpl. asimpl. erewrite H. 
2 : { eauto. } simpl. done. 
Qed.

Definition full_unf g := (iter (mu_height g) unf g).

(*Even non contractive terms have the property that full unfolding equals full unfolding plus 1. This is what we need in projection lemma
 so we don't have to derive contractiveness of e from projection derivation*)
Lemma full_unf_subst : forall e, full_unf (GRec e) = full_unf (e [g GRec e .: GVar]). 
Proof. 
intros. rewrite /full_unf. 
intros. simpl.  rewrite -iterS iterSr. simpl. 
destruct (guarded 0 e) eqn:Heqn.  rewrite mu_height_unf. done. done. 
 erewrite guarded_test.  2 : { lia. } 
simpl. 
erewrite <-mu_height_unf2. 2 : { lia.  } simpl. 
rewrite addnC.  
rewrite iterD. erewrite guarded_test. 2 : { lia.  } simpl. rewrite -iterS iterSr /=. 
erewrite guarded_test. 2 : { lia. } done. 
Qed.


Lemma full_unf2 : forall n e, full_unf (iter n unf e) = full_unf e. 
Proof. 
elim. done. 
intros. rewrite iterS. 
destruct (if (iter n unf e) is GRec _ then true else false) eqn:Heqn. 
destruct ((iter n unf e))eqn:Heqn2;try done. simpl. 
rewrite -(H e) Heqn2. rewrite full_unf_subst. done. 
have : unf (iter n unf e) = iter n unf e. destruct ((iter n unf e));try done. 
move=>->. rewrite H. done. 
Qed.

Lemma full_unf_idemp : idemp full_unf. 
Proof. 
intros. rewrite /idemp. intros. rewrite {2}/full_unf. rewrite full_unf2. done. 
Qed.


CoInductive gcType :=
 | GCEnd
 | GCMsg : action -> value -> gcType -> gcType
 | GCBranch : action -> coseq gcType -> gcType.

Lemma gc_match : forall g, g = match g with | GCEnd => GCEnd | GCMsg a u g0 => GCMsg a u g0 |  GCBranch a gs => GCBranch a gs end. 
Proof. case;auto. Qed.

Definition gtocoind' (f : gType -> gcType)  g :=
match full_unf g with 
| GMsg a u g0 =>  GCMsg a u (f g0) 
| GBranch a gs => GCBranch a (comap f (to_coseq gs))
| _  => GCEnd
end.

CoFixpoint gtocoind g := gtocoind' gtocoind g. 

Lemma gtocoind'_eq g : gtocoind' gtocoind g = match full_unf g with 
| GMsg a u g0 =>  GCMsg a u (gtocoind g0) 
| GBranch a gs => GCBranch a (map gtocoind gs)
| _  => GCEnd
end.
Proof. 
rewrite /gtocoind'. destruct (full_unf g);try done. 
f_equal. elim : l. simpl. rewrite !utils.coeq comap_eq //=. 
intros. rewrite utils.coeq. rewrite utils.comap_eqs /=. rewrite utils.coeq.  f_equal. done. 
Qed.

Lemma gtocoind_eq g : gtocoind g = gtocoind' gtocoind g. 
Proof. 
intros. rewrite /gtocoind'.  rewrite (gc_match (gtocoind g)). 
destruct g;try done;simpl. 
rewrite /gtocoind'. 
destruct (full_unf (GRec g));try done. 
Qed.

Let gtocoinds_eqs := (gtocoind'_eq, gtocoind_eq). 

Lemma full_unf_end  : full_unf GEnd = GEnd.  
Proof. done. Qed.

Lemma full_unf_msg d u e0 : full_unf (GMsg d u e0) = GMsg d u e0.
Proof. done. Qed.

Lemma full_unf_branch d es : full_unf (GBranch d es) = (GBranch d es).  
Proof. done. Qed.

Let unf_eqs := (full_unf_end, full_unf_msg, full_unf_branch). 


Let eqs := (utils.comap_eqs,gtocoinds_eqs, unf_eqs, utils.coeq). 

Inductive gUnravel_gen (R : gType -> gcType  -> Prop) : gType -> gcType  -> Prop :=
 | gUnravel_gen_msg g0 gc0 a u : R g0 gc0 -> gUnravel_gen R (GMsg a u g0) (GCMsg a u gc0)
 | gUnravel_gen_branch (gs : seq gType) (gcs : seq gcType) a : size gs = size gcs -> Forall (fun p => R p.1 p.2) (zip gs gcs) -> gUnravel_gen R (GBranch a gs) (GCBranch a gcs) (*restrict gcType to be an inductive list in disguse, only coerced from inductive to coinductive to let gtocoind pass productivity test of Coq*)
 | gUnravel_gen_rec g gc : gUnravel_gen R (g [g GRec g .: GVar]) gc  -> gUnravel_gen R (GRec g) gc (*guarded*)
 | gUnravel_gen_end : gUnravel_gen R GEnd GCEnd.

Lemma gUnravel_gen_mon : monotone2 gUnravel_gen.
Proof. move => x0 x1. intros. induction IN;try done. con;eauto. 
con;eauto. apply/List.Forall_forall. intros. 
move/List.Forall_forall : H0. eauto. con. done. con. 
Qed. 

Notation gUnravel e0 e1 := (paco2 gUnravel_gen bot2 e0 e1). 
Notation gUnravels g := (gUnravel g (gtocoind g)).


Hint Resolve gUnravel_gen_mon : paco. 

Variant gUnravel2_gen (R : gType -> gcType  -> Prop) : gType -> gcType  -> Prop :=
 | gUnravel2_gen_msg e0 ec d u :  R e0 ec -> gUnravel2_gen R  (GMsg d u e0) (GCMsg d u ec)
 | gUnravel2_gen_branch (es : seq gType) ( ecs : seq gcType)  d : size es = size ecs ->  Forall (R_pair R) (zip es ecs) -> gUnravel2_gen R (GBranch d es)  (GCBranch d ecs)
 | gUnravel2_gen_end :   gUnravel2_gen R GEnd  GCEnd.

Lemma gUnravel2_gen_mon : monotone2 gUnravel2_gen. 
Proof. move => x0 x1. intros. induction IN;try done. con;eauto. 
con;eauto. apply/List.Forall_forall. intros. 
move/List.Forall_forall : H0. eauto. con. 
Qed. 

Hint Resolve gUnravel2_gen_mon : paco. 
Notation UnfgUnravel := (ApplyF full_unf ssrfun.id). 
Notation gUnravel2 := (fun g gc =>  paco2 (UnfgUnravel \o gUnravel2_gen) bot2 g gc).

Variant gInvPred_gen (R : gType ->  Prop) : gType   -> Prop :=
 | rol_gen_msg e0  d u :  R e0 -> gInvPred_gen R  (GMsg d u e0) 
 | rol_gen_branch (es : seq gType)  d :  Forall R es -> gInvPred_gen R (GBranch d es) 
 | rol_gen_end :   gInvPred_gen R GEnd .

Lemma gInvPred_gen_mon : monotone1 gInvPred_gen. 
Proof. move => x0 x1. intros. induction IN;try done. con;eauto. 
con;eauto. apply/List.Forall_forall. intros. eauto. 
move/List.Forall_forall : H. eauto. con. 
Qed. 


Hint Resolve gInvPred_gen_mon : paco. 


Notation gInvPred := (paco1 (ApplyF1 full_unf \o gInvPred_gen) bot1).

Lemma Unravel_gInvPred : forall g gc, gUnravel2 g gc -> gInvPred g. 
Proof. 
pcofix CIH. intros. punfold H0. inv H0. pfold. con. 
inv H;eauto;pclearbot. con. eauto. 
con. clear H H0 H1.
elim : es ecs H2 H3. case. auto. auto. 
move => a l IH []. done. simpl. intros. inv H2. inv H3. 
con. simpl in *. pclearbot.   eauto. eauto. 
con. 
Qed.


Lemma gtocoind_full_unf : forall g, gtocoind g = gtocoind (full_unf g). 
Proof. 
intros. 
rewrite !eqs full_unf_idemp //=. 
Qed.


Lemma gInvPred_Unravel : forall g ,  gInvPred g -> gUnravel2 g (gtocoind g).
Proof. 
pcofix CIH. intros. punfold H0. inv H0. pfold.
rewrite gtocoind_full_unf.  con. 
inv H;eauto;pclearbot;rewrite !eqs.  
rewrite -gtocoind'_eq -gtocoind_eq. con. eauto. 
con. rewrite size_map //=. 
clear H H1 H0. elim : es H2. simpl.  auto. 
simpl. intros. inv H2. pclearbot. con. eauto. eauto. 
con. 
Qed.

Lemma gInvPred_iff : forall g ,  gInvPred g <-> gUnravel2 g (gtocoind g).
Proof. 
intros. split. move/gInvPred_Unravel=>//=. 
move/Unravel_gInvPred=>//=. 
Qed.


Lemma gInvPred_unf_iff : forall g, gInvPred g <-> gInvPred (full_unf g). 
Proof. 
intros. split. intros. punfold H. inv H. pfold. con. rewrite full_unf_idemp //=. 
intros. pfold. con. punfold H. inv H. rewrite full_unf_idemp in H0. done. 
Qed.




Lemma gUnravel_unf4 :  forall e ec (R: gType -> gcType -> Prop), paco2 gUnravel_gen R (unf e) ec -> paco2 gUnravel_gen R e ec.
Proof.
intros.  destruct e;try done. pfold. constructor. simpl in H. punfold H. 
Qed.

Lemma gUnravel_unf5 :  forall n e ec (R: gType -> gcType -> Prop), paco2 gUnravel_gen R (iter n unf e) ec -> paco2 gUnravel_gen R e ec.
Proof.
elim. done. intros. simpl in H0. apply gUnravel_unf4 in H0. auto. 
Qed.

Lemma gUnravel_unf6 :  forall e ec (R: gType -> gcType -> Prop), paco2 gUnravel_gen R (full_unf e) ec -> paco2 gUnravel_gen R e ec.
Proof. 
intros. rewrite /full_unf in H. apply/gUnravel_unf5.  eauto. 
Qed.


Lemma gUnravel_iff : forall e ec, gUnravel e ec <->  gUnravel2 e ec. 
Proof. intros. split. 
move : e ec. pcofix CIH. 
intros. punfold H0.  induction H0. pclearbot. pfold.
constructor. rewrite /full_unf /=.  constructor. eauto. 
pfold. constructor. rewrite /full_unf /=. constructor. done. 
induction H0;auto. constructor. pclearbot. eauto. eauto.  
pfold. constructor. rewrite full_unf_subst. 
punfold IHgUnravel_gen. inv IHgUnravel_gen. done.
pfold. constructor. rewrite /full_unf. constructor.
intros. 
move : e ec H.  pcofix CIH. intros. punfold H0. inv H0. 
inv H. apply/gUnravel_unf6. rewrite -H1. pfold. constructor. 
right. apply/CIH. pclearbot. done. 
apply/gUnravel_unf6. rewrite -H1. pfold. constructor. done. 
induction H3;auto. pclearbot. eauto. 
apply/gUnravel_unf6. rewrite -H2. pfold. constructor. 
Qed.

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

Lemma gtocoind_rec g : (gtocoind (GRec g)) = gtocoind (g [g GRec g .: GVar]). 
Proof. rewrite !eqs full_unf_subst //=. Qed.

Lemma unravelg_exist : forall e,  gUnravel2 e (gtocoind e) <-> exists ec, gUnravel2 e  ec.
Proof. 
intros. split. 
intros. exists (gtocoind e).  done.
case. move : e. 
intros. 
move : x e p. pcofix CIH. 
move => x e Hu. punfold Hu. inv Hu. 
pfold. con. rewrite gtocoind_full_unf.
 inv H;rewrite 3!eqs;try con;eauto;pclearbot. eauto. rewrite size_map. done. 
clear H Hu H0. 
elim :es ecs H1 H2. case;try done.  ssa. move => a l IH [] //=.  ssa. 
con. inv H2.  pclearbot. ssa. right. eauto. inv H2. ssa. eapply IH. eauto. done. 
Qed. 



Fixpoint enumg e :=
e::
match e with 
| GRec e0 => map (fun e0 => e0 [g e .: GVar]) (enumg e0)
| GMsg d v e0 => enumg e0
| GBranch d es => flatten (map enumg es)
| GEnd => nil
| GVar n => nil
end.

Definition nextg e := 
match e with 
| GMsg _ _ e0 => (e0::nil)
| GBranch _ es => es 
| _ => nil
end.

Definition nextg_unf e :=nextg (full_unf e). 

Lemma selfe : forall e, e \in enumg e. 
Proof. intros. destruct e;rewrite //=. 
Qed. 

Lemma unf_subst : forall e sigma, (if e is GVar _ then false else true) ->  unf (e [g sigma]) = (unf e)[g sigma].
Proof. 
case;rewrite //=;intros. 
asimpl. f_equal. 
Qed.




Lemma enumg_closed_unf : forall e, unf_closed (enumg e) unf.
Proof. 
rewrite /unf_closed. 
elim;rewrite //=;intros. 
- rewrite inE in H. rewrite (eqP H). done. 
- rewrite inE in H. rewrite (eqP H). done. 
- rewrite inE in H0. destruct (orP H0). rewrite (eqP H1) /=. 
  rewrite inE. apply/orP. right. apply/map_f/selfe. 
  move : H1. move/mapP=>[]/=. intros. subst. rewrite inE. apply/orP. right.
  destruct (if x is GVar _ then false else true) eqn:Heqn.
  rewrite unf_subst. apply/map_f/H/p. eauto. 
  destruct x;try done. simpl.  destruct n. simpl. apply/map_f. apply/selfe. 
  simpl. have : GVar n = (GVar n.+1) [g GRec g .: GVar]. simpl. done. 
  move=>->. apply/map_f. done. 
- rewrite inE in H0. destruct (orP H0). rewrite (eqP H1). rewrite /= !inE eqxx //=. 
  rewrite inE. rewrite H. rewrite orbC //=. done. 
- rewrite inE in H0. destruct (orP H0). rewrite (eqP H1) inE eqxx //=. 
  rewrite inE. apply/orP. right. apply/flattenP. destruct (flattenP H1). exists x. done. 
  destruct (mapP H2). subst. apply/H. done. done. 
Qed.


Lemma enumg_closed_full_unf : forall e, unf_closed (enumg e) full_unf.    
Proof. 
rewrite /unf_closed. 
intros. rewrite /full_unf. remember (mu_height a). clear Heqn. 
elim : n. done. intros. simpl. apply/enumg_closed_unf.  done. 
Qed.

Lemma next_subst : forall e sigma, (if e is GVar _ then false else true) ->  nextg (e [g sigma]) = map (fun e0 => e0 [g sigma]) (nextg e).
Proof. 
destruct e;try done. 
Qed.

Lemma enumg_closed_nextg : forall e, next_closed (enumg e) nextg.  
Proof. 
rewrite /next_closed. 
elim;rewrite //=;intros. 
rewrite inE in H. rewrite (eqP H) //= in H0.  
rewrite inE in H. rewrite (eqP H) //= in H0.  
rewrite inE in H0. destruct (orP H0). 
rewrite (eqP H2) //= in H1. 
move : H2. move/mapP=>[] //=. intros. subst. simpl.
destruct (if x is GVar _ then false else true) eqn:Heqn. 
 rewrite next_subst //= in H1.  
rewrite inE. apply/orP. right. 
destruct (mapP H1). subst. apply/map_f. apply/H. 2 : {  eauto. } 
eauto. 
destruct x;try done. simpl. destruct n. simpl. done. done.  
rewrite inE in H0. destruct (orP H0). rewrite (eqP H2) /= in H1. rewrite inE in H1.  rewrite (eqP H1) inE selfe. 
lia. rewrite inE. erewrite H. lia. eauto. done. 
rewrite inE in H0. destruct (orP H0). rewrite (eqP H2) /= in H1. rewrite inE. apply/orP. right.
apply/flattenP. exists (enumg a'). apply/mapP.  exists a'. done. done. apply/selfe. 
rewrite inE. apply/orP. right. destruct (flattenP H2). 
destruct (mapP H3). subst. apply/flattenP. exists (enumg x0). done.
apply/H. done. eauto. done. 
Qed.


(*Lemma 21 in the paper*)
Lemma enumg_closed_nextg_unf : forall e, next_closed (enumg e) nextg_unf.  
Proof. 
rewrite /next_closed. intros. rewrite /nextg_unf in H0. apply/enumg_closed_nextg. 
2 : { eauto. } rewrite /full_unf. 
apply/enumg_closed_full_unf. done. 
Qed.


Lemma enumg_ren : forall e sigma, enumg e ⟨g sigma⟩ = map (fun e0 => e0 ⟨g sigma⟩) (enumg e).
Proof. 
elim;rewrite //=;intros. 
asimpl. f_equal. rewrite H.  rewrite -!map_comp. rewrite /comp. apply/eq_in_map => x xIn. 
asimpl. done. 
f_equal. done. f_equal. rewrite -map_comp. rewrite !map_flatten. 
rewrite -map_comp. f_equal.  rewrite /comp. apply/eq_in_map=> x xIn.
apply/H.  done. 
Qed.


Definition is_gvar e := if e is GVar _ then true else false.
 
Lemma enumg_subst : forall e e' sigma (S : seq gType), (forall n e0, ~~ is_gvar (sigma n) -> e0 \in enumg (sigma n) -> e0 \in S) -> e' \in enumg e [g sigma] -> e' \in map (fun e0 =>  e0 [g sigma]) (enumg e) \/ e' \in S. 
Proof. 
elim;rewrite //=;intros. 
destruct (is_gvar (sigma n)) eqn:Heqn. destruct (sigma n);try done. simpl in H0. rewrite inE in H0. rewrite (eqP H0). 
auto. right. apply/H. lia. done. 
rewrite inE in H0. rewrite (eqP H0). auto.
rewrite inE in H1.  destruct (orP H1). 
rewrite (eqP H2). rewrite inE. left. rewrite eqxx. lia. 
rewrite -!map_comp. 
rewrite /comp. 
have : map (fun x => x [g GRec g .: GVar] [g sigma]) (enumg g) =  map (fun x =>  x [gGRec g [gGVar 0 .: sigma >> ⟨g ↑ ⟩] .: sigma]) (enumg g). 
apply/eq_in_map. move=> x xIn. asimpl. done. move=>->. 
move : H2. move/mapP=>[]. intros. 
subst. 
intros.
asimpl. 
eapply H in p. 
destruct p. destruct (mapP H2). subst. asimpl. left. rewrite inE. apply/orP. right. apply/map_f. done. 
right. 
2 : { intros. move : H2 H3. destruct n. asimpl. done. asimpl. rewrite enumg_ren. intros. 
  destruct (mapP H3). subst. apply H0 in H4. instantiate (1 := map (fun e0 => e0 ⟨g succn ⟩) S).
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
destruct (mapP H3). subst. apply/flattenP. exists ([seq e0 [gsigma] | e0 <- enumg x0]). apply/map_f. done. 
apply/map_f. 
done. 
right.  
eauto. done. done. 
Qed.



Lemma enumg_subst_unf : forall e e', e' \in enumg (unf e)  -> e' \in enumg e.  
Proof. 
intros. 
destruct e;try done. 
move : H. simpl. move/enumg_subst=>HH. 
move : (HH (enumg (GRec e)))=>HH'.
edestruct HH'. case. 
simpl. intros. done. done. 
rewrite inE. rewrite H. lia.
simpl in H. done.  
Qed.

Lemma enumg_subst_iter_unf : forall k e e', e' \in enumg (iter k unf e)  -> e' \in enumg e.  
Proof. 
elim. done. 
intros. apply/H. apply/enumg_subst_unf. rewrite -iterS. done. 
Qed.

Lemma enumg_subst_nextg : forall e e' e'', e' \in nextg e -> e'' \in enumg e'  -> e'' \in enumg e.  
Proof. 
case;intros;try done.  
simpl in H. 
rewrite inE in H.  simpl. move : H. move/eqP=>HH. subst. rewrite inE H0 //=. lia. 
simpl in H. simpl. rewrite inE. apply/orP. right. apply/flattenP. exists (enumg e'). 
apply/map_f. done. done. 
Qed.

Lemma enumg_subst_nextg_unf : forall e e' e'', e' \in nextg_unf e -> e'' \in enumg e'  -> e'' \in enumg e.  
Proof. 
intros. rewrite /nextg_unf in H.  eapply enumg_subst_nextg in H. apply/enumg_subst_iter_unf. eauto. 
done. 
Qed.

Definition enumg_size e := size (undup (enumg e)). 

Definition outg e := 
match e with 
| GMsg d u g => Some (d, inr u)
| GBranch d gs => Some (d, inl (size gs))
| _ => None
end.

Definition gmeasure (e : gType) (visited : seq ( gType)) := 
size (rep_rem visited (undup (enumg e))). 





Definition is_grec e := if e is GRec _ then true else false. 

Require Import Program. 
From Equations Require Import Equations. 


Equations sat1 (A : Set ) (visited : seq  gType)  (P : gType -> seq A ->  A) (b : gType -> A)   (e : gType): A by wf (gmeasure e visited) := 
 sat1  visited P b e  with (dec (e \in visited)) => {
  sat1  _ _ _ _ (in_left) := b e;
  sat1 visited P b e _ :=  (P e (foldInMap (nextg_unf e) (fun e0 _ => sat1 (e::visited) P b e0)))
 }. 
Next Obligation. 
apply/ltP. 
simpl. rewrite /gmeasure /=.
(*enum e0 \ e::visited < enum e \ visited *)
destruct (e \in ((enumg e0))) eqn:Heqn.
- apply/size_strict_sub. (*e \in enum e0*)
 * apply/rem_uniq/rep_rem_uniq/undup_uniq. (*uniqueness not interesting*)
 * intros. destruct (eqVneq x e). (* enum e0 \ e::visited <= enum e \ visited *) (*x \in left -> x \in right*)
  **  subst. rewrite -mem_rep_iff.  rewrite mem_undup. (*x = e and \e \notin visited so x \in enum e \ visited*)
      apply/selfe. rewrite e1 //=.
  ** apply mem_rem2 in H;eauto. (*x != e*)
     have : x \notin visited. apply/negP=>HH. eapply rep_rem_uniq2 in HH. 2 : apply/(@undup_uniq _ (enumg e0)).
     rewrite H //= in HH. move => Heqn2.
     move : H. rewrite -!mem_rep_iff;eauto. (*x \notin visited so x \in enum e0 -> x \in enum e by main lemma*)
     rewrite  !mem_undup. intros. apply/enumg_subst_nextg_unf.  
     apply/inP. eauto. done. 
 * instantiate (1 := e).  apply/negP=>HH. rewrite mem_rem_uniqF in HH. done. (*e \notin enum e0 \ e::visited*)
   apply/rep_rem_uniq/undup_uniq. 
 * rewrite -mem_rep_iff.  rewrite mem_undup. apply/selfe.  (*e \in enum e*)
   rewrite e1 //=. 
- have :  e \notin rep_rem visited (undup (enumg e0)). 
  apply/negP=>HH. move : Heqn. move/negP=>H2. apply/H2. 
  apply/mem_rep_iff.  apply/negP. clear H2. eauto. apply/rep_rem2. rewrite e1. 
  done. 2 :  eauto.  intros. rewrite mem_undup in H. done. move => HH'. 

  rewrite rem_id //=. (*e \notin enum e0, suff to show enum e0 \ visited < enum e \ visited *)
  apply/size_strict_sub;eauto.   
  * apply/rep_rem_uniq. apply/undup_uniq. (*uniquenes not interesting*)
  * intros. have : x \notin visited. apply/negP=>HH. eapply rep_rem_uniq2 in HH. 2 : apply/(@undup_uniq _ (enumg e0)).
    rewrite H //= in HH. move => Heqn2. (*x \notin visited*)
    move : H. rewrite -!mem_rep_iff. rewrite  !mem_undup. intros. 
    apply/enumg_subst_nextg_unf.  apply/inP. eauto. done. rewrite Heqn2. (*suff to show x \in enum e0 -> x \in enum e by main lemma*)
    done. rewrite Heqn2. done.
  * rewrite -mem_rep_iff. rewrite mem_undup. apply/selfe. rewrite e1 //=. (*e \in enum e \ visited*)
Defined. 

Check gInvPred_gen. 

Definition UnravelPred g (l : seq bool) := 
match full_unf g with 
| GRec _ | GVar _ => false | _ =>  all id l end. 

Lemma sat1_sound_aux : forall e l   (R : gType ->  Prop) , sat1  l UnravelPred (fun _ => true) e ->  (forall x, x \in l -> R x) ->
upaco1 (ApplyF1 full_unf  \o gInvPred_gen) R e. 
Proof.
intros. 
funelim (sat1  l UnravelPred (fun _ => true) e). 
right. apply/H0. done. 
rewrite -Heqcall in H0.
left. pcofix CIH.
pfold. constructor. 
rewrite /UnravelPred in H0.
destruct (full_unf e) eqn:Heqn; try solve [ con | done]. 
con. 
apply/H. rewrite /nextg_unf Heqn /=. auto. 
ssa. rewrite foldInMapP in H0. apply (allP H0). rewrite /nextg_unf Heqn /=. done. 
intros. rewrite inE in H2. destruct (orP H2). rewrite (eqP H3). done. 
auto. 

con. 
have : forall e0 : gType,
      In e0 l ->  upaco1 (ApplyF1 full_unf  \o gInvPred_gen) R e0. 
intros. apply H. rewrite /nextg_unf Heqn. simpl. auto. 
ssa. rewrite foldInMapP in H0.  apply (allP H0). rewrite /nextg_unf Heqn /=. 
apply/map_f. apply/inP.  done. 
intros.
rewrite inE in H3.  destruct (orP H3). rewrite (eqP H4). done. auto. 
move => HH0.
clear Heqcall H0 Heqn.
elim : l HH0.  intros. simpl. auto. 
simpl. ssa. 
Qed.

Lemma sat1_sound : forall e, sat1 nil UnravelPred (fun _ => true) e -> gInvPred e. 
Proof. 
intros. apply (@sat1_sound_aux _ _ bot1) in H. inv H. done. done. done. 
Qed.



Lemma sat1_complete: forall e l, gInvPred e -> sat1 l UnravelPred (fun _ => true) e.  
Proof. 
intros. funelim (sat1 l  UnravelPred (fun _ => true) e). 
done. 
rewrite -Heqcall foldInMapP. ssa. 
punfold H0. inv H0.
rewrite /nextg_unf. 
rewrite /UnravelPred. 
inv H1;try done;simpl;rewrite /id; ssa.
apply : H. rewrite /nextg_unf -H2 /=. auto.
pclearbot. eauto. 
apply/allP => x. move/mapP=>[]. intros. 
subst. move : p. move/nthP. move/(_ GEnd)=>[]. intros. subst. 
apply/H. rewrite /nextg_unf -H2 /=. apply/inP. apply/mem_nth=>//=. 
move/ForallP : H3. intros. have : In (nth GEnd es x) es. apply/inP/mem_nth. done. 
move/H3. case=>//=.
Qed. 


(*Lemma 23 in the paper*)
Lemma dec_gUnravels : forall g, gUnravels g <-> sat1 nil UnravelPred (fun _ => true) g.
Proof. intros.  
split;intros. 
apply/sat1_complete/gInvPred_iff/gUnravel_iff. done. 
apply/gUnravel_iff/gInvPred_iff. apply/sat1_sound. done. 
Qed.


Inductive gInvPred2_gen (R : gType ->  Prop) : gType   -> Prop :=
 | rol2_gen_msg e0  d u :  R e0 -> gInvPred2_gen R  (GMsg d u e0) 
 | rol2_gen_branch (es : seq gType)  d :  Forall R es -> gInvPred2_gen R (GBranch d es) 
 | rol2_gen_end :   gInvPred2_gen R GEnd
 | rol2_gen_var n : gInvPred2_gen R (GVar n).


Lemma gInvPred2_gen_mon : monotone1 gInvPred2_gen. 
Proof. move => x0 x1. intros. induction IN;try done. con;eauto. 
con;eauto. apply/List.Forall_forall. intros. eauto. 
move/List.Forall_forall : H. eauto. con. con. 
Qed. 


Hint Resolve gInvPred2_gen_mon : paco. 


Notation gInvPred2 := (paco1 ( ApplyF1 full_unf \o gInvPred2_gen) bot1).






Fixpoint gType_fv e :=
  match e with
  | GVar j => [:: j]
  | GEnd => nil
  | GMsg _ _ g0 => gType_fv g0
  | GBranch _ gs => flatten (map gType_fv gs)
  | GRec g0 => map predn (filter (fun n => n != 0) (gType_fv g0))
  end.

Definition gclosed g := forall n, n \notin gType_fv g.

Lemma gType_fv_ren : forall g sigma, (gType_fv g ⟨g sigma⟩) = map sigma (gType_fv g). 
Proof. 
elim;rewrite //=;intros. 
rewrite -!map_comp. rewrite H.
rewrite filter_map /=. clear H. asimpl. 
elim : (gType_fv g). done. ssa. 
destruct (eqVneq a 0). subst. simpl. ssa. 
simpl. destruct a. done. simpl. f_equal. done. 
rewrite -!map_comp. rewrite map_flatten. rewrite -!map_comp. 
f_equal. apply/eq_in_map=> x xIn. simpl. auto. 
Qed.

Lemma gType_fv_subst : forall g sigma, (gType_fv g [g sigma]) = flatten (map (sigma >> gType_fv) (gType_fv g)). 
Proof. 
elim;rewrite //=;intros. 
rewrite cats0. asimpl. done. 
rewrite H. rewrite -!map_comp. 
asimpl. rewrite filter_flatten.
rewrite -!map_comp. rewrite !map_flatten.
rewrite -map_comp.
rewrite /comp. asimpl. clear H.
elim : ( gType_fv g);try done. ssa. 
destruct (eqVneq a 0). simpl. subst. simpl. done. 
simpl. destruct a. done. simpl.
f_equal. asimpl. rewrite gType_fv_ren. 
rewrite filter_map /=. rewrite -map_comp.
clear i.  clear H. 
elim : ( gType_fv (sigma a));try done. ssa. 
f_equal. done. done.  

rewrite -map_comp. 
rewrite !map_flatten.  rewrite -!map_comp. 
rewrite /comp. asimpl. 
elim : l H. done. ssa. simpl.
rewrite flatten_cat. f_equal. auto. apply/H. auto. 
Qed.


(*Intermediate judgment that gives us induction principle to show gInvPred_no_fv*)
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

Lemma has_varP : forall g n, n \in gType_fv g -> has_var n g. 
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
 The technique informally says from the coinductive gInvPred judgment and a proof
 that we will observe a variable in finite time, we can reach a contradiction,
 so there can be no free variables.
*)
Lemma gInvPred_no_fv : forall g, gInvPred g -> (forall n, n \notin gType_fv g).
Proof. 
intros. apply/negP. move/has_varP=>HH. elim : HH H;intros. 
punfold H. inv H. inv H0. punfold H1. inv H1. inv H2. pclearbot. eauto. 
punfold H2. inv H2. inv H3. apply/H1. move/ForallP : H5. move/(_ _ H). case=>//=.
punfold H1. inv H1. rewrite full_unf_subst in H2. apply/H0. 
pfold. con. done. 
Qed.


Lemma not_imp : forall g, ~ gInvPred2 g -> ~ gInvPred2_gen (upaco1 (ApplyF1 full_unf \o gInvPred2_gen) bot1) (full_unf g).
Proof. intros. intro. apply/H. pfold.  con. done. 
Qed. 


Inductive gInvPred3 : gType   -> Prop :=
 | rol3_gen_msg g g' a u :  full_unf g = GMsg a u g' -> gInvPred3 g' -> gInvPred3 g 
 | rol3_gen_branch g (gs : seq gType) g' a :  full_unf g = GBranch a gs -> g' \in gs -> gInvPred3 g' -> gInvPred3 g 
 | rol3_gen_rec g g' :   full_unf g = GRec g' -> gInvPred3 g.


Lemma gInv_idemp : forall g, gInvPred3 (full_unf g) -> gInvPred3 g. 
Proof. 
intros. inv H. econstructor. rewrite full_unf_idemp in H0. eauto. done.  
rewrite full_unf_idemp in H0. econstructor 2.  eauto. eauto. done. 
rewrite full_unf_idemp in H0. econstructor 3. eauto. 
Qed. 

Lemma gInv_idemp2 : forall g, gInvPred3 g -> gInvPred3 (full_unf g). 
Proof. 
intros. inv H. rewrite H0. econstructor. cbn.  eauto. done. 
econstructor 2. rewrite full_unf_idemp. eauto. eauto. eauto. 
econstructor 3. rewrite full_unf_idemp. eauto. 
Qed. 

Lemma guarded_ren : forall g n sigma, injective sigma ->  guarded n g -> guarded (sigma n) (g ⟨g sigma ⟩).
Proof. 
elim=>//=;intros. apply/eqP. move => HH.  apply H in HH. lia. 
move : H1. asimpl. intros.
have : injective (0 .: sigma >> succn). eauto.  
move/H. move/(_ n.+1).  asimpl. eauto. 
Qed. 

Lemma guarded_subst : forall g n sigma , (forall n0, guarded n0 g = false  -> guarded n (sigma n0)) -> guarded n (g [g sigma]). 
Proof. 
elim=>//=;intros. apply/H. lia. 
move : H0.  asimpl. intros. 

apply/H.  ssa. 
destruct n0;try done. asimpl. apply/guarded_ren. done. eauto. 
Qed. 


Lemma guarded_eunf  : forall g n, guarded n g -> guarded n (unf g).
Proof. 
case=>//=;intros.
apply/guarded_subst. 
ssa. destruct n0;try done. simpl. destruct (eqVneq n0 n). subst. lia. done. 
Qed.

Lemma iter_unf_guarded  : forall n0 n g, guarded n g ->  iter n0 unf g <> GVar n.
Proof. 
elim;intros.
simpl in H. subst. simpl. destruct g;try done. simpl in H. move=> HH. inv HH. lia.
rewrite iterSr.  apply H. apply/guarded_eunf. done. 
Qed.


Lemma full_unf_com2 : forall g sigma,  (forall n : nat_eqType, ~~ guarded n g -> mu_height (sigma n) = 0) -> full_unf g [g sigma] = (full_unf g) [g sigma ]. 
Proof. 
intros. rewrite /full_unf. rewrite mu_height_subst. 
remember (mu_height g). 
clear Heqn. 
elim : n g H. simpl. done. 
intros. simpl. rewrite H //=.
destruct (is_gvar (iter n unf g)) eqn:Heqn.  

destruct (iter n unf g) eqn:Heqn2;try done. asimpl. simpl. 


have : mu_height (sigma n0) = 0. 
apply/H0. apply/negP=>HH. apply (@iter_unf_guarded n) in HH. rewrite Heqn2 in HH. done. 
destruct (sigma n0);try done. 
rewrite unf_subst //=. destruct (iter n unf g);try done. 
eauto. 
Qed.


Lemma guarded_uniq : forall g n0 n1, guarded n0 g = false -> guarded n1 g = false -> n0 = n1.
Proof. 
elim=>//=. 
intros. lia. 
intros. suff : n0.+1 = n1.+1.  lia. apply/H=>//=. 
Qed.

Lemma guarded_ren2 : forall g n sigma, guarded (sigma n) (g ⟨g sigma ⟩) -> guarded n g.
Proof. 
elim=>//=;intros. apply/eqP. move => HH.  apply/negP. apply/H. apply/eqP. f_equal. done. 
apply/H.
instantiate (1 := (0 .: sigma >> succn)). asimpl. done. 
Qed. 

Lemma guarded_subst2 : forall g n n0 sigma ,  guarded n (g [g sigma]) ->  guarded n (sigma n0) = false -> guarded n0 g. 
Proof. 
elim=>//=;intros. destruct (eqVneq n n1);try done. subst. rewrite H0 in H. done. 
move/H : H0. asimpl. move/(_ n0.+1). asimpl.
move => HH. apply HH. apply/negP=> HH2. apply/negP. move : H1. move/negP/negP. eauto. 
apply guarded_ren2 in HH2. eauto. 
Qed. 

Lemma guarded_unfv : forall g n, guarded n g = false -> full_unf g = GVar n. 
Proof. 
intros. rewrite /full_unf. remember (mu_height g). 
move : n0 g Heqn0 H.  
elim=>//=. case=>//=. intros. f_equal=>//=. lia. 
intros. 
destruct g;try done. simpl in Heqn0.
rewrite -iterS iterSr /=. rewrite H. done. 
rewrite mu_height_subst. inv Heqn0=>//=. 
case. simpl. intros. simpl in H0. have : n.+1 = 0. apply/guarded_uniq. lia. lia. 
done. done. 
simpl in *. apply/negP=> HH. apply/negP. move/negP/negP : H0. eauto. 
eapply guarded_subst2 in HH. eauto. asimpl. simpl. lia. 
Qed.


Lemma gInv_struct0 : forall g sigma,  (forall n, mu_height (sigma n.+1) = 0) ->  gInvPred3 g -> gInvPred3 (g[g sigma]). 
Proof. 
intros. elim : H0 H. intros. apply/gInv_idemp. rewrite full_unf_com2. rewrite H. ssa. econstructor. ssa. 
apply/H1. done. intros. destruct n. have : guarded 0 g0 = false. lia. 
move/guarded_unfv. move=> HH2.  rewrite HH2 in H. done. done. 
intros. econstructor 2.  rewrite full_unf_com2. rewrite H. asimpl. eauto. 
intros. destruct n. have : guarded 0 g0 = false. lia. move/guarded_unfv.  move => HH. 
rewrite H in HH.  done.  done. apply/map_f.  eauto.  apply/H2.  done. 
intros. econstructor 3. rewrite full_unf_com2. rewrite H. asimpl.  eauto. 
intros. destruct n.  have : guarded 0 g0 = false. lia. move/guarded_unfv. move => HH. intros. rewrite HH in H. done. 
done.
Qed. 
Lemma gInv_struct : forall g,  gInvPred3 g -> gInvPred3 (GRec g). 
Proof. intros. apply/gInv_idemp. rewrite full_unf_subst. 
destruct (guarded 0 g) eqn:Heqn. 
rewrite full_unf_com2. apply/gInv_struct0. 
ssa. apply/gInv_idemp2.  done. 
intros. destruct n. rewrite Heqn in H0. done. done. 
apply guarded_unfv in Heqn.
apply gInv_idemp2 in H. rewrite Heqn in H. inv H. done. done. done. 
Qed. 

Inductive Bad3 : gType -> Prop := 
 | Bad31 g : guarded 0 g = false  -> Bad3 (GRec g)
 | Bad32 g : Bad3 g -> Bad3 (GRec g).



Lemma bad_ren : forall g sigma, Bad3 g -> Bad3 (g ⟨g sigma ⟩).   
Proof. 
intros. elim : H sigma;intros .
simpl. con. apply/negP=>HH. move/negP : H. intros. apply/H. 
apply/guarded_ren2.  move : HH. asimpl.  intros. 
instantiate (1 := 0 .: sigma >> succn). 
eauto. simpl. 
simpl. constructor 2.  auto.
Qed. 

Lemma bad_subst : forall g sigma, Bad3 g -> Bad3 (g [g sigma]).   
Proof. 
intros. elim : H sigma;intros .
simpl. con. apply/negP=>HH. move/negP : H. intros. apply/H. 
apply/guarded_subst2.  eauto. simpl. done. 
simpl. constructor 2.  auto.
Qed. 

Lemma guarded_bad : forall g n sigma, guarded n g = false -> Bad3 (sigma n) -> Bad3 g [g sigma].
Proof. 
elim;intros. ssa. have : n = n0 by lia. move=>->. done. 
ssa. ssa. 
constructor 2. apply/H.  eauto. simpl. destruct n. asimpl.  
ssa. apply/bad_ren.  done. asimpl.  apply/bad_ren. done. 
ssa. ssa. 
Qed. 

Lemma bad_guarded : forall g, Bad3 g -> Bad3 (unf g).  
Proof.
intros. elim : H;intros. 
simpl. 
destruct g0;try done. 
ssa. 
have : n = 0 by lia. move=>->. ssa. con. ssa. 
ssa. constructor 2.  
have: Bad3 (GRec (GRec g0)) ⟨g succn ⟩.
simpl. con.  ssa. asimpl. 
apply/negP=> HH. move/negP : H. intros. apply/H. apply/guarded_ren2.
instantiate (1 := 0 .: (1 .: succn >> (succn >> succn))). 
asimpl. done. 
intros. apply/guarded_bad.   eauto. ssa. 
 simpl. inv H. 
ssa. con. apply/negP=>HH. move/negP : H1. 
intros. apply/H1. apply/guarded_subst2.  eauto. simpl. done. 
asimpl. constructor 2. apply/bad_subst.  done. 
Qed. 

Lemma bad_guarded_full : forall g, Bad3 g -> Bad3 (full_unf g).  
Proof. 
intros. rewrite /full_unf. remember (mu_height g). clear Heqn.
elim : n g H. ssa. intros. rewrite iterS.  apply/bad_guarded. 
apply/H.  done. 
Qed. 

Lemma bad_rec : forall g, Bad3 g -> is_grec g. 
Proof. 
intros. inv H. ssa. ssa. 
Qed. 

Lemma cont_bad3 : forall g, guarded 0 g = false -> Bad3 (GRec g). 
Proof. 
elim;ssa. have : n = 0 by lia. move=>->. con. done. 
con. 
ssa. 
Qed. 

Lemma not_cont : forall g, ~~ gcontractive g -> gInvPred3 g. 
Proof. 
elim;try done.  
intros. ssa.  rewrite negb_and in H0. destruct (orP H0). 
 have :  is_grec (full_unf (GRec g)).
rewrite full_unf_subst.
have : guarded 0 g = false. lia.
move/cont_bad3. 
move/bad_guarded_full. rewrite full_unf_subst. 
move/bad_rec. done. 
intros. destruct (full_unf (GRec g)) eqn:Heqn;try done. 
econstructor 3. eauto. 

apply H in H1. apply/gInv_struct.  done. 
ssa. econstructor. cbn.  done. auto. 
ssa. elim : l H H0. ssa. ssa.

rewrite negb_and in H1. destruct (orP H1). econstructor 2. 
cbn.  eauto. rewrite inE. apply/orP.  left. apply/eqP.  eauto. apply/H0.
done. done. 
have : gInvPred3 (GBranch a l). apply/H. 
intros. apply/H0. rewrite inE H3.  lia. done. done. 
intros. inv x. move : H3. cbn. done. inv H3. 
econstructor 2. cbn.  eauto. rewrite inE. apply/orP. right. eauto. done. 
move : H3. cbn. done. 
Qed. 
Print gInvPred3. Search _ gInvPred3. 

Lemma gInvPred_contractive3 : forall g, gInvPred2 g -> gInvPred3 g -> False.  
Proof. intros. move : H. elim : H0;intros.  
apply/H1. punfold H2.  inv H2. rewrite H in H3. inv H3. pclearbot. done. 
apply/H2. punfold H3. inv H3. rewrite H in H4. inv H4. move/ForallP : H6. 
move/inP: H0.  intros. move/H6: H0.  case;try done. 
punfold H0. inv H0. rewrite H in H1. inv H1. 
Qed. 

Lemma gInvPred_contractive : forall g, gInvPred2 g -> gcontractive g.
Proof. 
intros. destruct (gcontractive g) eqn :Heqn. done. 
have : ~~ gcontractive g. lia. move/not_cont.  intros. 
exfalso. apply/gInvPred_contractive3.  eauto. eauto. 
Qed. 

Lemma gInvPred12 : forall g, gInvPred g -> gInvPred2 g. 
Proof. 
pcofix CIH. intros. punfold H0. inv H0. pfold. con. inv H. 
con. pclearbot.  right. eauto. 
con. elim : H2. 
done. ssa. con. pclearbot. eauto. eauto. 
con. 
Qed. 

Lemma gcontractive_ren : forall g sigma, injective sigma -> (forall n, n <= sigma n) ->  gcontractive  g -> gcontractive g ⟨g sigma ⟩.
Proof.
elim;intros;simpl;try done. 
asimpl. split_and. have : 0 = ( 0 .: sigma >> succn) 0. done. intros. rewrite {1}x.
apply guarded_ren. auto. ssa. apply/H=>//=. auto. intros. destruct n. simpl. done. ssa. asimpl. move : (H1 n). lia. ssa. ssa. 
rewrite all_map. apply/allP. intro. intros. simpl. apply H. done.  done. done.  simpl in H2. apply (allP H2). done.
Qed.

Lemma guarded_ren_iff : forall g n sigma, injective sigma ->  guarded n g <-> guarded (sigma n) (g ⟨g sigma ⟩).
Proof. intros. split;intros. apply/guarded_ren;eauto. apply/guarded_ren2. eauto. 
Qed. 


Lemma guarded_sig2 : forall g sigma sigma' i, guarded i g [g sigma] -> (forall n, guarded i (sigma n) -> guarded i (sigma' n)) -> guarded i g [g sigma'].
Proof. 
elim;rewrite /=;intros;try done.
apply H0. done.
asimpl. apply : H. eauto. move => n.  asimpl. simpl. intros. destruct n. done. simpl in *.
move : H. rewrite /funcomp. specialize H1 with n. move : H0. asimpl.
intros. rewrite -guarded_ren_iff. move : H. rewrite -guarded_ren_iff.  move/H1. done. 
done. done. 
Qed.

Lemma  guarded_fv : forall g v, v \notin gType_fv g -> guarded v g.
Proof.
elim;rewrite /=;try done;intros.
rewrite !inE in H. lia.
apply H. move : H0. intros. apply/negP=>HH'. apply/negP. apply H0. apply/mapP. exists v.+1. rewrite mem_filter. ssa. done. 
Qed.

Lemma inoting : forall g i sigma, (forall n, i !=  sigma n) -> i \notin gType_fv g ⟨g sigma ⟩.
Proof.
elim;rewrite /=;try done;intros. rewrite !inE. specialize H with n. lia.
apply/negP. move/mapP. case. ssa. subst. rewrite mem_filter in p. ssa. 
destruct x;try done. ssa. apply/negP. apply/H. 2 : eauto. asimpl. intros.
destruct n. done. ssa. asimpl. move: (H0 n).  lia. 
apply/negP. move/flattenP. case. move=> x. rewrite -map_comp. move/mapP.  case. intros. subst. 
apply/negP. apply/H. eauto. eauto. done. 
Qed.


Lemma gcontractive_subst : forall g sigma, gcontractive g -> (forall n, gcontractive (sigma n)) -> gcontractive g [g sigma].
Proof. 
elim;rewrite /=;intros;try done. 
asimpl. split_and. 
apply/guarded_sig2.
instantiate (1 := (GVar 0 .: GVar  >>  ⟨g ↑ ⟩)).  asimpl. done.
case. done. simpl. intros. apply/guarded_fv. asimpl. apply/inoting. done.
apply H. done.  intros. destruct n.  done. simpl. asimpl.  apply/gcontractive_ren. done. done. done.
apply H. done.  intros. done. 
rewrite all_map. apply/allP. intro. intros. simpl. apply H. done. apply (allP H0). done. done.
Qed.


Lemma gcontractive_unf : forall g , gcontractive g -> gcontractive (unf g). 
Proof.
intros. rewrite /unf. destruct g;try done. apply/gcontractive_subst. ssa. case;done. 
Qed.

Lemma gcontractive_iter_unf : forall k g , gcontractive g -> gcontractive (iter k unf g). 
Proof.
elim;try done. intros. simpl. apply/gcontractive_unf. ssa. 
Qed.

Lemma gcontractive_full_eunf : forall g , gcontractive g -> gcontractive (full_unf g). 
Proof. 
intros. rewrite /full_unf. apply/gcontractive_iter_unf. done. 
Qed.

Lemma gType_fv_unf : forall g n, (n \in gType_fv g) = (n \in gType_fv (unf g)).  
Proof. 
case=>//=. intros. rewrite gType_fv_subst. 
apply/eq_iff. split. move/mapP=>[] x /=. rewrite mem_filter. ssa. subst. 
apply/flattenP. destruct x;try done. simpl. 
have : ((GRec g .: GVar) >> gType_fv) = 
([seq i.-1 | i <- gType_fv g & i != 0] .: fun n => [::n]).
asimpl. simpl. f_equal. move=>->.
exists ([::x]). 
apply/mapP. exists x.+1. ssa. simpl. done. done. 
move/flattenP=>[] x. move/mapP=>[] x0. intros. subst. destruct x0;try done.  
move : q0. asimpl. simpl. rewrite inE. move/eqP. intros. subst. apply/mapP. exists x0.+1=>//=. 
rewrite mem_filter. ssa. 
Qed.

Lemma gType_fv_full_unf : forall g n, (n \in gType_fv g) = (n \in gType_fv (full_unf g)).  
Proof. 
intros. rewrite /full_unf. remember (mu_height g). clear Heqn0. elim : n0 g. done. 
intros. rewrite iterS. rewrite H. apply/gType_fv_unf. 
Qed.

Lemma mu_height_subst_contractive : forall g0 sigma, (forall n, 0 < mu_height (sigma n) -> guarded n g0) -> gcontractive g0 -> mu_height (g0[g sigma]) = mu_height g0.
Proof. 
elim; try solve [by rewrite /=];intros.
asimpl. move : (H n). destruct (mu_height (sigma n)) eqn:Heqn. done. have : 0 < n0.+1 by lia. move => + HH. move/HH=>//=. lia. 
simpl. f_equal. asimpl. apply H. case. rewrite //=. move=> n/=. move => HH. apply/H0. move : HH. asimpl. rewrite mu_height_ren //=. ssa. 
Qed.

Lemma mu_height_unf_contractive : forall g , gcontractive g -> (mu_height g).-1 = mu_height (unf g).
Proof.
move => g. rewrite /=. case : g; try solve [intros;rewrite /=;done].
intros. rewrite /=. ssa. erewrite mu_height_subst_contractive. done. eauto. case. done. done. done. 
Qed.

Lemma mu_height_iter_unf : forall k g , gcontractive g -> (mu_height g) - k = (mu_height (iter k unf g)). 
Proof.
elim;intros. rewrite /=. lia.
rewrite /=. have : mu_height g - n.+1 = (mu_height g - n).-1 by lia. move=>->. 
erewrite H. rewrite mu_height_unf_contractive //=.  apply/gcontractive_iter_unf.  done. done. 
Qed.

Lemma iter_unf_not_rec : forall g k, gcontractive g -> mu_height g <= k -> forall g', iter k unf g <> GRec g'.
Proof.
intros. simpl in *. apply (mu_height_iter_unf k) in H. move : H. 
have : mu_height g - k  = 0 by lia. move=>->. intros. destruct (iter k unf g);try done.
Qed.

Lemma full_unf_not_rec : forall g, gcontractive g -> forall g', full_unf g <> GRec g'.
Proof.
intros. apply/iter_unf_not_rec. done. done. 
Qed.

Lemma to_gInvPred : forall e, (forall n, n \notin gType_fv e) -> gcontractive e -> gInvPred e. 
Proof. 
pcofix CIH. 
intros. pfold. con. remember H1 as Hcont. clear HeqHcont. 
apply gcontractive_full_eunf in H1.
have : forall n : nat_eqType, n \notin gType_fv (full_unf e). 
intros. rewrite -gType_fv_full_unf. done. clear H0=>H0.
destruct (full_unf e) eqn:Heqn. 
move : (H0 n). ssa. lia. con. 
move : (@full_unf_not_rec e  Hcont g) =>Heq. rewrite Heqn in Heq. done. 
(*exfalso. apply/Heq. done.*)
con. right. apply/CIH. ssa. ssa. 
con. 
ssa. 
apply/ForallP=> x xIn. right. apply/CIH.
intros. apply/negP=> HH. apply (negP (H0 n)). apply/flattenP. exists (gType_fv x)=>//=. 
apply/map_f. apply/inP. done. 
apply (allP H1). apply/inP. done.
Qed.

(*Lemma 11 in the paper*)
Lemma unravelling_of_trans : forall g, gclosed g -> gcontractive g -> gInvPred g.   
Proof. 
intros. apply/to_gInvPred;done. 
Qed.

(*Proposition 4 from the paper*)
Lemma proposition_4 : forall g, (exists gc, gUnravel2 g gc) <-> gclosed g /\ gcontractive g. 
Proof. intros. split;intros. split.   rewrite /gclosed.  apply/gInvPred_no_fv. destruct H.  apply/Unravel_gInvPred. eauto.
destruct H. apply/gInvPred_contractive/gInvPred12/Unravel_gInvPred. eauto. ssa. 
exists (gtocoind g). apply/gInvPred_iff. apply/unravelling_of_trans;eauto. 
Qed. 





