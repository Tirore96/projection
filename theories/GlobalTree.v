
From mathcomp Require Import all_ssreflect zify.

From Proj Require Import Syntax Elimination Utils.
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

Variant FinSeq_gen (R : gcType ->  Prop) : gcType   -> Prop :=
 | fin_seq_msg e0  d u :  R e0 -> FinSeq_gen R  (GCMsg d u e0) 
 | fin_seq_branch (es : seq gcType)  d :  Forall R es -> FinSeq_gen R (GCBranch d es) 
 | fin_seq_end :   FinSeq_gen R GCEnd .

Lemma FinSeq_gen_mon : monotone1 FinSeq_gen. 
Proof. 
move => x0 x1. intros. induction IN;try done. con. eauto. con. apply/List.Forall_forall. eauto. 
intros. move/List.Forall_forall : H. eauto. 
con. 
Qed.


Hint Resolve FinSeq_gen_mon : paco. 

Notation Finite := (paco1 FinSeq_gen bot1).
Lemma Finite_msg : forall a u g0,  Finite (GCMsg a u g0) -> Finite g0. 
Proof. 
intros. punfold H. inv H. pclearbot=>//=.
Qed.







Lemma Finite_branch : forall a g (gs : seq gcType),  Finite (GCBranch a gs) -> In g gs -> Finite g. 
Proof. 
intros. punfold H. inv H. injt. 
forallApp H2 H0=> [] //=[] //=. 
Qed.

Hint Resolve  Finite_msg  Finite_branch. 


Lemma Finite_coerce : forall a gs, Finite (GCBranch a gs) -> exists (gs' : seq gcType), gs = gs'. 
Proof. 
intros. punfold H. inv H. exists es. done. 
Qed.


Lemma gc_match : forall g, g = match g with | GCEnd => GCEnd | GCMsg a u g0 => GCMsg a u g0 |  GCBranch a gs => GCBranch a gs end. 
Proof. case;auto. Qed.

Definition g_to_c' (f : gType -> gcType)  g :=
match full_unf g with 
| GMsg a u g0 =>  GCMsg a u (f g0) 
| GBranch a gs => GCBranch a (comap f (to_coseq gs))
| _  => GCEnd
end.

CoFixpoint g_to_c g := g_to_c' g_to_c g. 

Lemma g_to_c'_eq g : g_to_c' g_to_c g = match full_unf g with 
| GMsg a u g0 =>  GCMsg a u (g_to_c g0) 
| GBranch a gs => GCBranch a (map g_to_c gs)
| _  => GCEnd
end.
Proof. 
rewrite /g_to_c'. destruct (full_unf g);try done. 
f_equal. elim : l. simpl. rewrite !Utils.coeq comap_eq //=. 
intros. rewrite Utils.coeq. rewrite Utils.comap_eqs /=. rewrite Utils.coeq.  f_equal. done. 
Qed.

Lemma g_to_c_eq g : g_to_c g = g_to_c' g_to_c g. 
Proof. 
intros. rewrite /g_to_c'.  rewrite (gc_match (g_to_c g)). 
destruct g;try done;simpl. 
rewrite /g_to_c'. 
destruct (full_unf (GRec g));try done. 
Qed.

Let g_to_cs_eqs := (g_to_c'_eq, g_to_c_eq). 

Lemma full_unf_end  : full_unf GEnd = GEnd.  
Proof. done. Qed.

Lemma full_unf_msg d u e0 : full_unf (GMsg d u e0) = GMsg d u e0.
Proof. done. Qed.

Lemma full_unf_branch d es : full_unf (GBranch d es) = (GBranch d es).  
Proof. done. Qed.

Let unf_eqs := (full_unf_end, full_unf_msg, full_unf_branch). 


Let eqs := (Utils.comap_eqs,g_to_cs_eqs, unf_eqs, Utils.coeq). 

(*Inducti ve GQ_gen  (R : gcType -> gcType -> Prop) : gcType -> gcType -> Prop := 
 | gq_end : GQ_gen R GCEnd GCEnd
 | gq_msg g0 g1 a u : R g0 g1 -> GQ_gen R (GCMsg a u g0) (GCMsg a u g1)
 | gq_branch gs0 gs1 a : paco2 (forall_gen R) bot2 gs0 gs1 -> GQ_gen R (GCBranch a gs0) (GCBranch a gs1).


Lemma GQ_gen_mon : monotone2 GQ_gen. 
Proof. 
move => x y R. intros. move : IN. fix IH 1. case. 
constructor.
intros. constructor.  apply/LE. done. 
move => es0 es1 d c. intros. constructor. apply/forall_gen_mon2. eauto. eauto. done. 
Qed.

Hint Resolve GQ_gen_mon : paco.

Lemma GQ_refl : forall g r,  g <<(r) GQ_gen  >>  g. 
Proof. 
pcofix CIH. case. pfold. constructor. 
intros. pfold. constructor. right. done. 
intros. pfold. constructor. 
apply/forall_gen_refl. auto. (*Compositional*)
Qed.

Hint Resolve GQ_refl.*)

Inductive Unravelg_gen (R : gType -> gcType  -> Prop) : gType -> gcType  -> Prop :=
 | Unravelg_gen_msg g0 gc0 a u : R g0 gc0 -> Unravelg_gen R (GMsg a u g0) (GCMsg a u gc0)
 | Unravelg_gen_branch (gs : seq gType) (gcs : seq gcType) a : size gs = size gcs -> Forall (fun p => R p.1 p.2) (zip gs gcs) -> Unravelg_gen R (GBranch a gs) (GCBranch a gcs) (*restrict gcType to be an inductive list in disguse, only coerced from inductive to coinductive to let g_to_c pass productivity test of Coq*)
 | Unravelg_gen_rec g gc : Unravelg_gen R (g [g GRec g .: GVar]) gc  -> Unravelg_gen R (GRec g) gc (*guarded*)
 | Unravelg_gen_end : Unravelg_gen R GEnd GCEnd.

Lemma Unravelg_gen_mon : monotone2 Unravelg_gen.
Proof. move => x0 x1. intros. induction IN;try done. con;eauto. 
con;eauto. apply/List.Forall_forall. intros. 
move/List.Forall_forall : H0. eauto. con. done. con. 
Qed. 


Definition Unravelg e0 e1 := paco2 Unravelg_gen bot2 e0 e1. 




Hint Resolve Unravelg_gen_mon : paco. 
(*{A B : Type} (P : A -> B -> Prop) : A * B -> Prop := fun p => P p.1 p.2. *)


(*
Lemma Unravelg_uniq : forall e ec0 ec1, e << Unravelg_gen >> ec0 ->  e  << Unravelg_gen >> ec1 -> ec0 << GQ_gen >> ec1. 
Proof. 
pcofix CIH. 
move => e ec0 ec1 HH. punfold HH. induction HH. pclearbot.
move => HH2. punfold HH2. inversion HH2;subst.  
pfold. constructor. right. apply/CIH. eauto. pclearbot. done. 
move => HH2. punfold HH2. inversion HH2;subst. 
pfold. constructor. clear HH2. apply/Forall_ForallC. lia.
 
move : gs gcs gcs0 H H0 H3 H5. 
elim. case;last done.  case;last done.  simpl. auto. 
move => a0 l IH. case;first done. move => a1 l0. case;first done. 
intros. simpl in *. inv H. inv H3. inv H0.  inv H5. pclearbot. simpl in *.
constructor. rewrite /R_pair /=. eauto. eauto. 
move => HH2. punfold HH2. inversion HH2. subst. 
 apply/IHHH. pfold. done. 
move => HH2. punfold HH2. inversion HH2. pfold. constructor. 
Qed.*)

Variant Unravelg2_gen (R : gType -> gcType  -> Prop) : gType -> gcType  -> Prop :=
 | Unravelg2_gen_msg e0 ec d u :  R e0 ec -> Unravelg2_gen R  (GMsg d u e0) (GCMsg d u ec)
 | Unravelg2_gen_branch (es : seq gType) ( ecs : seq gcType)  d : size es = size ecs ->  Forall (R_pair R) (zip es ecs) -> Unravelg2_gen R (GBranch d es)  (GCBranch d ecs)
 | Unravelg2_gen_end :   Unravelg2_gen R GEnd  GCEnd.

Lemma Unravelg2_gen_mon : monotone2 Unravelg2_gen. 
Proof. move => x0 x1. intros. induction IN;try done. con;eauto. 
con;eauto. apply/List.Forall_forall. intros. 
move/List.Forall_forall : H0. eauto. con. 
Qed. 

Hint Resolve Unravelg2_gen_mon : paco. 

Variant Rolling_gen (R : gType ->  Prop) : gType   -> Prop :=
 | rol_gen_msg e0  d u :  R e0 -> Rolling_gen R  (GMsg d u e0) 
 | rol_gen_branch (es : seq gType)  d :  Forall R es -> Rolling_gen R (GBranch d es) 
 | rol_gen_end :   Rolling_gen R GEnd .

Lemma Rolling_gen_mon : monotone1 Rolling_gen. 
Proof. move => x0 x1. intros. induction IN;try done. con;eauto. 
con;eauto. apply/List.Forall_forall. intros. eauto. 
move/List.Forall_forall : H. eauto. con. 
Qed. 


Hint Resolve Rolling_gen_mon : paco. 

Notation UnfUnravelg := (ApplyF full_unf ssrfun.id). 

Notation Rolling := (paco1 (ApplyF1 full_unf \o Rolling_gen) bot1).
Lemma Unravel_Rolling : forall g gc, paco2 (UnfUnravelg \o Unravelg2_gen) bot2 g gc -> Rolling g. 
Proof. 
pcofix CIH. intros. punfold H0. inv H0. pfold. con. 
inv H;eauto;pclearbot. con. eauto. 
con. clear H H0 H1.
elim : es ecs H2 H3. case. auto. auto. 
move => a l IH []. done. simpl. intros. inv H2. inv H3. 
con. simpl in *. pclearbot.   eauto. eauto. 
con. 
Qed.


Lemma g_to_c_full_unf : forall g, g_to_c g = g_to_c (full_unf g). 
Proof. 
intros. 
rewrite !eqs full_unf_idemp //=. 
Qed.


Lemma Rolling_Unravel : forall g ,  Rolling g -> paco2 (UnfUnravelg \o Unravelg2_gen) bot2 g (g_to_c g).
Proof. 
pcofix CIH. intros. punfold H0. inv H0. pfold.
rewrite g_to_c_full_unf.  con. 
inv H;eauto;pclearbot;rewrite !eqs.  
rewrite -g_to_c'_eq -g_to_c_eq. con. eauto. 
con. rewrite size_map //=. 
clear H H1 H0. elim : es H2. simpl.  auto. 
simpl. intros. inv H2. pclearbot. con. eauto. eauto. 
con. 
Qed.

Lemma Rolling_iff : forall g ,  Rolling g <-> paco2 (UnfUnravelg \o Unravelg2_gen) bot2 g (g_to_c g).
Proof. 
intros. split. move/Rolling_Unravel=>//=. 
move/Unravel_Rolling=>//=. 
Qed.









Lemma Unravelg_unf  : forall (F : (gType -> gcType -> Prop) -> (gType-> gcType -> Prop)) a b r, monotone2 F ->  paco2 (UnfUnravelg \o F) r  a b <->  paco2 (UnfUnravelg \o F) r  (full_unf a) b.
Proof. 
intros. 
split. 
intros. punfold H0. inv H0. pfold. constructor. rewrite full_unf_idemp. done. 
intros. punfold H0.  pfold. rewrite /comp. rewrite /comp in H0. inv H0. 
rewrite full_unf_idemp in H1. constructor. done. 
Qed.



Lemma Unravelg_unf4 :  forall e ec (R: gType -> gcType -> Prop), paco2 Unravelg_gen R (unf e) ec -> paco2 Unravelg_gen R e ec.
Proof.
intros.  destruct e;try done. pfold. constructor. simpl in H. punfold H. 
Qed.

Lemma Unravelg_unf5 :  forall n e ec (R: gType -> gcType -> Prop), paco2 Unravelg_gen R (iter n unf e) ec -> paco2 Unravelg_gen R e ec.
Proof.
elim. done. intros. simpl in H0. apply Unravelg_unf4 in H0. auto. 
Qed.

Lemma Unravelg_unf6 :  forall e ec (R: gType -> gcType -> Prop), paco2 Unravelg_gen R (full_unf e) ec -> paco2 Unravelg_gen R e ec.
Proof. 
intros. rewrite /full_unf in H. apply/Unravelg_unf5.  eauto. 
Qed.


Lemma Unravelg_iff : forall e ec, e << Unravelg_gen >> ec <->  e << (ApplyF full_unf ssrfun.id  \o Unravelg2_gen)  >> ec. 
Proof. intros. split. 
move : e ec. pcofix CIH. 
intros. punfold H0.  induction H0. pclearbot. pfold.
constructor. rewrite /full_unf /=.  constructor. eauto. 
pfold. constructor. rewrite /full_unf /=. constructor. done. 
induction H0;auto. constructor. pclearbot. eauto. eauto.  
(*pclearbot. 
brewr
move : gs gcs H. elim;intros. 
rewrite coeq in H. rewrite coeq. 
uis H. 
rewrite coeq in H0. rewrite coeq. uis H0. eauto.  
left. apply/H. done. *)
pfold. constructor. rewrite full_unf_subst. 
punfold IHUnravelg_gen. inv IHUnravelg_gen. done.
pfold. constructor. rewrite /full_unf. constructor.
intros. 
move : e ec H.  pcofix CIH. intros. punfold H0. inv H0. 
inv H. apply/Unravelg_unf6. rewrite -H1. pfold. constructor. 
right. apply/CIH. pclearbot. done. 
apply/Unravelg_unf6. rewrite -H1. pfold. constructor. done. 
induction H3;auto. pclearbot. eauto. 
apply/Unravelg_unf6. rewrite -H2. pfold. constructor. 
Qed.

(*Lemma Unravel_eq : forall g gc0 gc1, gc0 << GQ_gen >> gc1 ->  g << (ApplyF full_unf ssrfun.id \o Unravelg2_gen) >> gc0 ->  g  << (ApplyF full_unf ssrfun.id \o  Unravelg2_gen) >> gc1.
Proof.
pcofix CIH. 
intros. punfold H1. pfold.   constructor. inv H1. induction H;pclearbot. uis H0.
Locate id. Print id. 
constructor.  eauto. 
uis H0. apply coerce_forall in H6. destruct H6. ssa. 
rewrite -H4. 
constructor. lia. clear H4 H0 H1.
elim : es ecs x H H3 H2 H5. case;last done. case;last done. 
simpl. auto. 
move => a l IH [];first done. 
move => a0 l0 [];first done. intros. simpl in *. 
inv H. inv H3.  inv H2.  inv H5. pclearbot. simpl in *. constructor. 
simpl. eauto. eauto. 
uis H0. constructor.
Qed.*)


(*Lemma GQ_sym : forall g0 g1, paco2 GQ_gen bot2 g0 g1 -> paco2 GQ_gen bot2 g1 g0. 
Proof. 
pcofix CIH. intros. punfold H0. inversion H0;subst.  
pfold. constructor. 
pfold. constructor. right.  apply/CIH. pclearbot. auto. 
pfold. constructor. clear H0. move : gs1 gs0 H. pcofix CIH2.
intros. punfold H0. inversion H0. pfold. constructor. 
subst. pfold. constructor. right. apply/CIH. pclearbot. auto. 
right. apply/CIH2. pclearbot. auto. 
Qed.*)


Lemma g_to_c_rec g : (g_to_c (GRec g)) = g_to_c (g [g GRec g .: GVar]). 
Proof. rewrite !eqs full_unf_subst //=. Qed.


(*Later perhaps do it with gpaco*)

(*Lemma cofix_comap  : forall aa, ((cofix comap  aa := 
match aa with 
| nil  => conil 
| cons a aa' => cocons (g_to_c a) (comap aa')
end) aa) = g_to_cs aa. 
Proof. 
elim. done. intros. rewrite eqs /=. 
rewrite (coseq_match  (_ (_::_))). f_equal.  
Qed.*)

Lemma unravelg_exist : forall g,  g << Unravelg_gen >> (g_to_c g) <-> exists gc, g << Unravelg_gen >>  gc.
Proof. 
intros. split. 
intros. exists (g_to_c g).  done.
case. move : g. 
intros. 
move : x g p. pcofix CIH. 
move => x g Hu. punfold Hu. induction Hu.
pfold. rewrite 3!eqs. constructor. pclearbot. eauto. 
rewrite 3!eqs. pc. rewrite size_map //=. 
elim : gs gcs H H0. case. simpl. auto. done. 
move => a0 l IH []. done. simpl in *. ssa. inv H0.  
simpl in *. pclearbot. constructor; eauto. 
pfold. constructor. 
rewrite g_to_c_rec. 
punfold IHHu. 
rewrite (gc_match (g_to_c _)) /=. pc. 
Qed.


(*Lemma GQ_trans : forall g0 g1 g2,  paco2 GQ_gen bot2 g0 g1 -> paco2 GQ_gen bot2 g1 g2 -> paco2 GQ_gen bot2 g0 g2. 
Proof. 
pcofix CIH. 
intros. punfold H0. punfold H1. inversion H0;subst;inversion H1;subst. 
pfold. constructor. 
pfold. constructor. right. pclearbot. apply/CIH. eauto. eauto. 
pfold. constructor. clear H0 H1. 
move : gs0 gs1 gs3 H H5. pcofix CIH2. 
intros. punfold H0. punfold H5. inversion H0;inversion H5;subst. 
pfold. constructor. 
done. 
done. 
pfold. inversion H7.  subst. constructor. right. pclearbot. apply/CIH. eauto. eauto. 
right. apply/CIH2.  pclearbot. eauto. pclearbot. eauto. 
Qed.*)







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

(*Notation next_path := (fun e => e::(unf e)::(nextg e)).*)




(*Section FiniteG.
Variable (g : gType). 

Definition gFinType := adhoc_seq_sub_finType (enumg g). 
From mathcomp Require Import fingraph. 

Definition gnext_fin : forall (g0 : gFinType), seq gFinType. 
Proof. 
intros. destruct g0. move : ssvalP.  move/enumg_closed_nextg_unf=>HH.  
elim : (nextg_unf ssval) HH. intros. apply nil. 
intros. apply cons. econstructor.  apply/HH. rewrite inE. apply/orP. left. 
eauto. apply/X. intros. apply/HH. rewrite inE. rewrite H. lia. 
Defined. 
End FiniteG. *)



(*Definition gnext_fin (g : gFinType) : seq gFinType  := nil. 
(*match full_unf g with 
| GMsg _ _ g0 => [:: g0]
| GBranch _ gs => gs
| _ => nil
end. *)

Definition gsub (g : gType) := seq_sub (enumg  g). 

Check (closed_mem (grel gnext_fin)). 
Check adhoc_seq_sub_choiceType. 
Check . 
*)

(*Lemma enumg_path : forall l e0 e1, path (grel next_path) e0 (l++[::e1]) -> e1 \in enumg e0. 
Proof. 
elim. intros. simpl in H. ssa. 
move : H0.  rewrite /next_path.
rewrite inE. move/orP=>[]. move/eqP=>->. apply/selfe. 
rewrite inE. move/orP=>[]. move/eqP=>->. apply/enumg_closed_unf/selfe. 
move/enumg_closed_nextg=>->. done. apply/selfe.
intros. ssa. move : H1 H2. 
rewrite inE. move/orP=>[]. move/eqP=>->. auto. 
rewrite inE. move/orP=>[]. move/eqP=>->. ssa. 
apply/enumg_subst_unf. apply/H. done. 
intros. apply/enumg_subst_nextg. eauto. apply/H. done. 
Qed.

Lemma nextg_subst : forall e sigma, ~~ is_gvar e ->  nextg e [gsigma] = map (fun e0 => e0 [g sigma]) (nextg e).
Proof. 
case;intros;try done.  
Qed.

Lemma path_subst : forall l e sigma, path (grel next_path) e l -> path (grel next_path) (e [g sigma]) (map (fun e0 => e0 [g sigma]) l). 
Proof. 
elim. done. 
intros. ssa.
destruct (is_gvar e) eqn:Heqn. destruct e;try done. simpl in *.
have : a = GVar n.  move : H1. rewrite !inE. move/orP=>[]; move/eqP=>->//=. 
move=>->. simpl. rewrite inE eqxx //=. 
rewrite inE in H1. move : H1. 
rewrite inE. move/orP=>[]. move/eqP=>->. done. 
rewrite inE. move/orP. case. move/eqP=>->. rewrite inE. apply/orP. right.
apply/orP.  left. rewrite unf_subst. done. destruct e;try done. 
intros. rewrite !inE. apply/orP. right. apply/orP. right. rewrite nextg_subst.
apply/map_f.  done. lia. 
Qed.

Lemma enumg_path2 : forall e0 e1, e1 \in enumg e0 -> exists l,  path (grel next_path) e0 (l++[::e1]). 
Proof. 
elim;rewrite //=;intros. 
exists nil. ssa. 
exists nil. ssa. 
move : H0. rewrite inE. 
move/orP=>[]. move/eqP=>->. exists nil.  ssa. 
move/mapP=>[]. intros. 
subst. 
apply H in p. destruct p. 
exists (map (fun e0 => e0 [g GRec g .: GVar]) (g::x0)).
ssa. 
have :  ([seq e0 [gGRec g .: GVar] | e0 <- x0] ++ [:: x [gGRec g .: GVar]])
 =  ([seq e0 [gGRec g .: GVar] | e0 <- x0++[::x]]). 
rewrite map_cat //=. move=>->. apply/path_subst. done. 
rewrite inE in H0. destruct (orP H0). rewrite (eqP H1). exists nil. ssa. 
apply H in H1. destruct H1. exists (g::x).  ssa. 
rewrite inE in H0. destruct (orP H0).  rewrite (eqP H1). exists nil. ssa. 
destruct (flattenP H1). destruct (mapP H2). subst. 
apply H in H3;auto. destruct H3. exists (x0::x). ssa. 
Qed.

Lemma enumg_pathP : forall e0 e1, e1 \in enumg e0 <-> exists l,  path (grel next_path) e0 (l++[::e1]). 
Proof. 
intros. split. apply/enumg_path2. 
case. intros. apply/enumg_path. eauto. 
Qed.*)


(*Lemma enumg_enumg : forall e0 e1 e2, e1 \in enumg e0 -> e2 \in enumg e1 -> e2 \in enumg e0. 
Proof. 
move => e0 e1 e2. rewrite !enumg_pathP. case. move => x Hp. case. 
intros. exists ((x ++ [::e1]) ++ x0). rewrite -catA. rewrite cat_path. ssa.
rewrite cats1. rewrite last_rcons. ssa. 
Qed.


Lemma test : forall e e',  e' \in nextg_unf e -> e \in enumg e' -> (forall e0, e0 \in enumg e' <-> e0 \in enumg e). 
Proof. 
intros. split;intros. 
- apply/enumg_subst_nextg_unf. eauto. done. 
- apply/enumg_enumg. 2 : { eauto. } done. 
Qed.*)

Definition enumg_size e := size (undup (enumg e)). 
(*Lemma enumg_measure : forall e e', e' \in nextg_unf e -> enumg_size e' <= enumg_size e.
Proof. 
intros. rewrite /enumg_size. apply/uniq_leq_size. apply/undup_uniq.   
move => x0 x1. move : x1.  rewrite !mem_undup.  intros. apply/enumg_subst_nextg_unf. eauto. done. 
Qed.*)


Definition outg e := 
match e with 
| GMsg d u g => Some (d, inr u)
| GBranch d gs => Some (d, inl (size gs))
| _ => None
end.

Definition gmeasure (e : gType) (visited : seq ( gType)) := 
size (rep_rem visited (undup (enumg e))). 





Definition is_grec e := if e is GRec _ then true else false. 

(*Lemma rep_rem2 : forall (A : eqType) (l l0 l1 : seq A) a, a \notin l -> (forall x, x \in l0 -> x \in l1) ->a \in rep_rem l l0  -> a \in rep_rem l l1.
Proof. 
move => A. elim. 
simpl. intros. auto.
simpl.  ssa. rewrite inE negb_or in H0.  ssa. 
apply/mem_rem. done. apply/H.  done. eauto. apply/mem_rem2. eauto. done. 
Qed.

Lemma rep_rem_uniq : forall (A : eqType) (l l' : seq A), uniq l' -> uniq (rep_rem l l').
Proof. 
move => A.
elim.  done. 
intros. simpl. rewrite rem_uniq. done. auto. 
Qed.

Lemma size_strict_sub : forall (A : eqType) (l l' : seq A) a, uniq l  -> (forall x, x \in l -> x \in l') -> a \notin l -> a \in l' -> size l < size l'. 
Proof. 
intros. 
have : size (a::l) <= size l'. 
apply/uniq_leq_size. ssa. move => x0 x1. 
rewrite inE in x1. destruct (orP x1). rewrite (eqP H3). done. auto. done. 
mQed.

Lemma rem_uniq2 : forall (A: eqType) (l'  : seq A) a x, uniq l' -> x <> a -> x \notin l' ->   x \notin rem a l'.
Proof.
move => A. 
elim. done. 
intros. ssa. case_if. 
rewrite inE negb_or in H2. ssa. 
rewrite inE negb_or. ssa. rewrite inE negb_or in H2. ssa. 
apply/H. ssa. 
done. rewrite inE negb_or in H2. ssa. 
Qed.


Lemma rep_rem_uniq2 : forall (A: eqType) (l l' : seq A) x, uniq l' ->  x \in l -> x \notin rep_rem l l'.
Proof. 
move => A. 
elim. done. 
intros. rewrite inE in H1.
destruct (eqVneq x a).   subst. 

simpl. rewrite mem_rem_uniqF. done. apply/rep_rem_uniq. done.
simpl. simpl in H1. apply/rem_uniq2. apply/rep_rem_uniq. done. apply/eqP. done.
auto.  
Qed.*)

Require Import Program. 
From Equations Require Import Equations. 



(*Unset Implicit Arguments. *)
Equations next_rec (A : Set ) (visited : seq  gType)  (P : gType -> seq A ->  A) (b : gType -> A)   (e : gType): A by wf (gmeasure e visited) := 
 next_rec  visited P b e  with (dec (e \in visited)) => {
  next_rec  _ _ _ _ (in_left) := b e;
(*  next_rec visited e _ :=  (~~ is_gvar (full_unf e)) && (~~ is_grec (full_unf e)) &&   (foldInAll (nextg_unf e) (fun e0 _ => next_rec (e::visited) e0))*)
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


(*We need e_to_ec because exist statement for coinductive type doesn't give os coinduction hypothesis*)



Definition has_treeP g (l : seq bool) := 
match full_unf g with 
| GRec _ | GVar _ => false | _ =>  all id l end. 



Lemma next_rec_sound_aux : forall e l   (R : gType -> gcType -> Prop) , next_rec  l has_treeP (fun _ => true) e ->  (forall x, x \in l -> R x (g_to_c x)) ->
upaco2 (ApplyF full_unf ssrfun.id  \o Unravelg2_gen) R e (g_to_c e). 
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
      In e0 l ->  upaco2 (ApplyF full_unf ssrfun.id \o Unravelg2_gen) R e0 (g_to_c e0). 
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
paco2 (ApplyF full_unf ssrfun.id  \o Unravelg2_gen) bot2 e (g_to_c e). 
Proof. 
intros. suff : upaco2 (ApplyF full_unf ssrfun.id  \o Unravelg2_gen) bot2 e (g_to_c e). case.  done. done. 
apply/next_rec_sound_aux. eauto. pclearbot. done. 
Qed.






Lemma next_rec_complete_aux: forall e ec l, paco2 (ApplyF full_unf ssrfun.id \o Unravelg2_gen) bot2 e ec -> next_rec l has_treeP (fun _ => true) e.  
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

Lemma next_recP : forall e, next_rec nil has_treeP (fun _ => true) e <->  paco2 Unravelg_gen bot2 e (g_to_c e). 
Proof. intros.  split;intros. apply/Unravelg_iff. apply/next_rec_sound. done. 
erewrite Unravelg_iff in H. 
apply/next_rec_complete_aux. eauto. 
Qed.


(*Fixpoint findSome (A : Type) (l : seq (option A)) := 
match l with 
| a::l' => if a is Some _ then Some 0 else omap (fun n => n.+1) (findSome l')
| nil => None
end. 

Lemma findSomeHas : forall (A : Type) (l : seq (option A)),has isSome l = findSome l. 
Proof. 
move => A. elim. done. 
simpl. intros. destruct a;try done. simpl. 
rewrite H. destruct (findSome l);done. 
Qed.

Lemma findSomeNone : forall (A : Type) (l : seq (option A)), findSome l = None <-> all (fun b => ~~ (isSome b)) l.
Proof.
intros. split. 
elim : l. 
simpl. intros. done. simpl.  intros. destruct a;try done. 
ssa. destruct (findSome l) eqn:Heqn. done. auto. 
elim : l. done. simpl. intros. ssa. destruct a;try done. 
apply H in H2. destruct (findSome l). done. done. 
Qed.

Lemma findSomenth : forall (A : Type) (l : seq (option A)) n, findSome l = Some n -> isSome (nth None l n) /\ n < size l. 
Proof. 
move => A. elim. done. simpl. intros. 
destruct a;try done. inv H0. simpl. ssa. 
destruct (findSome l) eqn:Heqn. simpl in H0. inv H0.
have : Some n0 = Some n0 by auto. move/H. ssa. 
done. 
Qed.

Lemma findSomenth2 : forall (A : eqType) (l : seq (option A)) a, a \in l -> a  -> findSome l. 
Proof. 
move => A. elim. done. simpl. intros. 
destruct a;try done. rewrite inE in H0. destruct (orP H0). rewrite (eqP H2) in H1. done. 
auto.
apply H in H2;auto. destruct (findSome l). done. done. 
Qed.


Lemma findSomeSome : forall (A : Type) (l : seq (option A)), (exists a, findSome l = Some a) <-> has (fun b => (isSome b)) l.
Proof.
intros. split. 
case. elim : l. 
simpl. intros. done. simpl.  intros. destruct a;try done. 
ssa. destruct (findSome l) eqn:Heqn. simpl in p. apply/H. eauto. done. 
elim : l. done. simpl. intros. destruct a;try done. 
simpl in H0. exists 0. done. simpl in H0. 
apply H in H0. destruct H0. exists x.+1. rewrite H0. done. 
Qed.


Definition ptcp_loc p g (l : seq (option nat)) := 
match full_unf g with 
| GRec _ | GVar _ => None 
| GMsg a _ _ | GBranch a _ => if comp_dir p a then Some 0 else  findSome l 
| _ =>  findSome l end. 

Lemma ptcp_loc_eq : forall p g (l : seq (option nat)), ptcp_loc p g l =
match full_unf g with 
| GRec _ | GVar _ => None 
| GMsg a _ _ | GBranch a _ => if comp_dir p a then Some 0 else  findSome l 
| _ =>  findSome l end. 
Proof. rewrite /ptcp_loc //=. 
Qed. *)


