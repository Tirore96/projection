From mathcomp Require Import all_ssreflect zify.
From CoTypes Require Export coGlobal coLocal.
Require Import Paco.paco.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


Inductive part_of (p : ptcp) : gcType -> Prop :=
| po_msg a u g0 : comp_dir p a -> part_of p (GCMsg a u g0)
| po_msg2 a u g0 : part_of p g0 -> part_of p (GCMsg a u g0)
| po_branch a gs : comp_dir p a -> part_of p (GCBranch a gs)
| po_branch2 a g (gs : seq gcType) : In g gs -> part_of p g ->   part_of p (GCBranch a gs).
Hint Constructors part_of.

Lemma part_of_ind2
     : forall (p : ptcp) (P : gcType -> Prop),
       (forall (a : action) (u : value) (g0 : gcType), comp_dir p a -> P (GCMsg a u g0)) ->
       (forall (a : action) (u : value) (g0 : gcType), ~ comp_dir p a -> part_of p g0 -> P g0 -> P (GCMsg a u g0)) ->
       (forall (a : action) (gs : coseq gcType), comp_dir p a -> P (GCBranch a gs)) ->
       (forall (a : action) (g : gcType) (gs : seq gcType), ~ comp_dir p a -> In g gs -> part_of p g -> P g -> P (GCBranch a gs)) ->
       forall g : gcType, part_of p g -> P g.
Proof. 
intros. eapply part_of_ind;eauto. 
intros. destruct (comp_dir p a) eqn:Heqn. apply H. rewrite Heqn. done. 
apply H0. rewrite Heqn. done. done. done. 
intros. destruct (comp_dir p a) eqn:Heqn. apply H1. rewrite Heqn. done. 
eapply H2. rewrite Heqn. done. eauto. eauto. done. 
Qed.


Lemma not_part_msg : forall p a v g, ~ part_of p (GCMsg a v g) -> ~ part_of p g.
Proof.  
intros. intro.  apply/H. eauto. 
Qed.

Lemma not_part_msg2 : forall p a v g, ~ part_of p (GCMsg a v g) -> ~ comp_dir p a.
Proof.  
intros. intro.  apply/H. eauto. 
Qed.

Lemma not_part_branch : forall p a g (gs : seq gcType), ~ part_of p (GCBranch a gs) -> In g gs -> ~ part_of p g.
Proof.  
intros. intro.  apply/H. eauto. 
Qed.

Lemma not_part_branch2 : forall p a (gs : seq gcType), ~ part_of p (GCBranch a gs) -> ~ comp_dir p a.  
Proof.  
intros. intro.  apply/H. eauto. 
Qed.

Hint Resolve not_part_msg not_part_msg2  not_part_branch  not_part_branch2. 


Inductive part_of_all (p : ptcp) : gcType -> Prop   :=
| poac_msg a u g0 : comp_dir p a -> part_of_all p (GCMsg a u g0)
| poac_msg2 a u g0 :  part_of_all p g0 -> part_of_all p (GCMsg a u g0)
| poac_branch a gs : comp_dir p a -> part_of_all p (GCBranch a gs)
| poac_branch2 a (gs : seq gcType)  :  (forall g, In g gs -> part_of_all p g) ->  part_of_all p (GCBranch a gs). (*May not be vacously true, require their to be at least one element in g, now part_of_all -> part_of and also part_of_all and ~ part_of cannot coincide*)
Hint Constructors part_of_all.

Lemma none_not : forall (A : Type) (a : option A), a = None <-> ~ a. 
Proof. 
intros. split;destruct a;done.  
Qed.

Lemma part_of_all_ind2
     : forall (p : ptcp) (P : gcType -> Prop),
       (forall (a : action) (u : value) (g0 : gcType), comp_dir p a -> P (GCMsg a u g0)) ->
       (forall (a : action) (u : value) (g0 : gcType), ~ comp_dir p a -> part_of_all p g0 -> P g0 -> P (GCMsg a u g0)) ->
       (forall (a : action) (gs : coseq gcType), comp_dir p a -> P (GCBranch a gs)) ->
       (forall (a : action) (gs : seq gcType),  ~ comp_dir p a ->  (forall g, In g gs -> part_of_all p g)   ->  (forall g, In g gs -> part_of_all p g -> P g) ->  P (GCBranch a gs)) ->
       forall g : gcType, part_of_all p g -> P g.
Proof. 
intros. move : g H3. fix IH 2. intros. destruct H3. 
apply/H. done. 
destruct (comp_dir p a) eqn:Heqn. apply/H. rewrite Heqn. done. 
apply/H0. apply/none_not. done. done. apply/IH. done. 
apply/H1. done. destruct (comp_dir p a) eqn:Heqn. 
apply/H1. rewrite Heqn. done. apply/H2. apply/none_not. done. 
intros. apply/H3. done. intros. apply/IH. apply/H3. done. Qed.

(*Using (forall x , In x .... generates a stronger induction principle*)






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

Inductive cproject_gen (p : ptcp) (R : gcType ->  ecType -> Prop) : gcType -> ecType -> Prop :=
 | cproject_msg_s g0 a e0 u d : comp_dir p a = Some d ->
                                  R g0 e0 -> cproject_gen p R (GCMsg a u g0) (ECMsg d (action_ch a) u e0)
 | cproject_msg_n g0 a e0 u : comp_dir p a = None ->
                                 R g0 e0 -> part_of_all p g0 ->  cproject_gen p R (GCMsg a u g0) e0(*assumption has to build something*)
 | cproject_gen_branch_f (gs : seq gcType) (es : seq ecType) a d :  comp_dir p a = Some d -> size gs = size es ->
                                        (forall p, In p (zip gs es) ->  R p.1 p.2 ) -> cproject_gen p R (GCBranch a gs) (ECBranch d (action_ch a) es)
 | cproject_gen_branch_o g (gs : seq gcType)  a e : comp_dir p a = None -> In g gs ->  (*We need list to be non -empty otherweise it projects to anything*)
                                    (forall g', In g' gs ->  part_of_all p g' /\  R g' e) ->  cproject_gen p R (GCBranch a gs) e
 | cproject_gen_end g : ~ part_of p g -> Finite g -> cproject_gen p R g ECEnd. (*Finite predicate ensures coinductive lists in the global type are finite*)
Hint Constructors cproject_gen. 


Lemma cproject_gen_mon p: monotone2 (cproject_gen p). 
Proof.
move => x0 x1. intros. induction IN;try done.
con;eauto. con;eauto. con;eauto. econstructor;eauto.  
intros. ssa. move/H1 : H2.  ssa. apply/LE. move/H1 : H2. ssa. con. 
done. done. 
Qed.

Hint Resolve cproject_gen_mon : paco. 


Definition CProject g p e := paco2 (cproject_gen p) bot2 g e. 

Lemma part_of_or_end : forall p g e r, paco2 (cproject_gen p) r g e -> part_of_all p g \/ e = ECEnd. 
Proof. 
intros. punfold H. inv H;eauto.  
left. con.  rewrite H0. eauto. 
left. con. comp_disc. 
left. econstructor 4. eauto.
intros. move/H2 : H3. ssa. 
Qed.



Lemma CProject_not_part : forall g p, paco2 (cproject_gen p) bot2 g ECEnd  ->  ~  part_of p g. 
Proof. intros. intro. 
elim/part_of_ind2 : H0 H;intros. punfold H0. inv H0;try comp_disc. 
apply/H1. punfold H2.  
punfold H2. 
inv H2;try comp_disc. pclearbot. eauto. 
have : ~ part_of p g0 by eauto. done. 
punfold H0. inv H0. comp_disc. 
have :~  comp_dir p a. eauto. comp_disc. 
punfold H3. inv H3. injt. apply H2.  move/H9 : H0. ssa. pclearbot. done. 
have : ~ part_of p g0. eauto. done.
Qed.
