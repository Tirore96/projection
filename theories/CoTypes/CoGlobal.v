
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
 The technique informally says from the coinductive gInvPred judgment and a proof
 that we will observe a variable in finite time, we can reach a contradiction,
 so there can be no free variables.
*)
Lemma gInvPred_no_fv : forall g, gInvPred g -> (forall n, n \notin gType_fv2 g).
Proof. 
intros. apply/negP. move/has_varP=>HH. elim : HH H;intros. 
punfold H. inv H. inv H0. punfold H1. inv H1. inv H2. pclearbot. eauto. 
punfold H2. inv H2. inv H3. apply/H1. move/ForallP : H5. move/(_ _ H). case=>//=.
punfold H1. inv H1. rewrite full_unf_subst in H2. apply/H0. 
pfold. con. done. 
Qed.

(*Proposition 4 from the paper*)
Lemma proposition_4 : forall g gc, gUnravel2 g gc -> gclosed g. 
Proof. intros. rewrite /gclosed.  apply/gInvPred_no_fv. apply/Unravel_gInvPred. eauto.
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


Equations next_rec (A : Set ) (visited : seq  gType)  (P : gType -> seq A ->  A) (b : gType -> A)   (e : gType): A by wf (gmeasure e visited) := 
 next_rec  visited P b e  with (dec (e \in visited)) => {
  next_rec  _ _ _ _ (in_left) := b e;
  next_rec visited P b e _ :=  (P e (foldInMap (nextg_unf e) (fun e0 _ => next_rec (e::visited) P b e0)))
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



Definition has_treeP g (l : seq bool) := 
match full_unf g with 
| GRec _ | GVar _ => false | _ =>  all id l end. 


(*We need gtocoind because exist statement for coinductive type doesn't give us coinduction hypothesis*)
Lemma next_rec_sound_aux : forall e l   (R : gType -> gcType -> Prop) , next_rec  l has_treeP (fun _ => true) e ->  (forall x, x \in l -> R x (gtocoind x)) ->
upaco2 (ApplyF full_unf ssrfun.id  \o gUnravel2_gen) R e (gtocoind e). 
Proof.
intros. 
funelim (next_rec  l has_treeP (fun _ => true) e). 
right. apply/H0. done. 
rewrite -Heqcall in H0.
left. pcofix CIH.
pfold. constructor. rewrite 2!eqs. 
rewrite /has_treeP in H0.
destruct (full_unf e) eqn:Heqn; try solve [ con | done]. 
con. 
apply/H. rewrite /nextg_unf Heqn /=. auto. 
ssa. rewrite foldInMapP in H0. apply (allP H0). rewrite /nextg_unf Heqn /=. done. 
intros. rewrite inE in H2. destruct (orP H2). rewrite (eqP H3). done. 
auto. 

con. rewrite size_map //=. 
have : forall e0 : gType,
      In e0 l ->  upaco2 (ApplyF full_unf ssrfun.id \o gUnravel2_gen) R e0 (gtocoind e0). 
intros. apply H. rewrite /nextg_unf Heqn. simpl. auto. 
ssa. rewrite foldInMapP in H0.  apply (allP H0). rewrite /nextg_unf Heqn /=. 
apply/map_f. apply/inP.  done. 
intros.
rewrite inE in H3.  destruct (orP H3). rewrite (eqP H4). done. auto. 
move => HH0.
clear Heqcall H0 Heqn.
elim : l HH0.  intros. simpl. auto. 
simpl. ssa. con. simpl. eauto. auto. 
Qed.

Lemma next_rec_sound : forall e, next_rec nil has_treeP (fun _ => true) e ->
gUnravel2 e (gtocoind e). 
Proof. 
intros. suff : upaco2 (ApplyF full_unf ssrfun.id  \o gUnravel2_gen) bot2 e (gtocoind e). case.  done. done. 
apply/next_rec_sound_aux. eauto. pclearbot. done. 
Qed.






Lemma next_rec_complete_aux: forall e ec l, gUnravel2 e ec -> next_rec l has_treeP (fun _ => true) e.  
Proof. 
intros. funelim (next_rec l  has_treeP (fun _ => true) e). 
done. 
rewrite -Heqcall foldInMapP. ssa. 
punfold H0. inv H0.
rewrite /nextg_unf. 
rewrite /has_treeP. 
inv H1;try done;simpl;rewrite /id; ssa.
apply : H. rewrite /nextg_unf -H2 /=. auto.
pclearbot. eauto. 
apply/allP => x. move/mapP=>[]. intros. 
subst. move : p. move/nthP. move/(_ GEnd)=>[]. intros. subst. 
apply/H. rewrite /nextg_unf -H2 /=. apply/inP. apply/mem_nth=>//=. 
apply coerce_forall2 in H4;eauto. 
eapply index_ForallIC in H4. pclearbot. apply /H4. eauto. 
Unshelve. repeat constructor. 
Qed. 

Lemma next_recP : forall e, next_rec nil has_treeP (fun _ => true) e <->  gUnravel e (gtocoind e). 
Proof. intros.  split;intros. apply/gUnravel_iff. apply/next_rec_sound. done. 
erewrite gUnravel_iff in H. 
apply/next_rec_complete_aux. eauto. 
Qed.



