Require Export IndTypes.unscoped.
From mathcomp Require Import all_ssreflect zify.
From deriving Require Import deriving. 

Inductive ptcp  : Set :=
  | Ptcp : nat   -> ptcp .
Definition nat_of_ptcp (p : ptcp) := let: Ptcp n := p in n.
Canonical ptctp_newType := Eval hnf in [newType for nat_of_ptcp]. 
Definition ptcp_eqMixin := [eqMixin of ptcp by <:]. 
Canonical ptcp_eqType := Eval hnf in EqType ptcp ptcp_eqMixin.
Definition ptcp_choiceMixin := [choiceMixin of ptcp by <:].
Canonical ptcp_ChoiceType := Eval hnf in ChoiceType ptcp ptcp_choiceMixin.
Definition ptcp_countMixin := [countMixin of ptcp by <:].
Canonical ptcp_countType := CountType ptcp ptcp_countMixin.


Inductive ch  : Set :=
  | Ch : nat   -> ch .

Definition nat_of_ch (c : ch) := let: Ch n := c in n.
Canonical ch_newType := Eval hnf in [newType for nat_of_ch].
Definition ch_eqMixin := [eqMixin of ch by <:]. 
Canonical ch_eqType := Eval hnf in EqType ch ch_eqMixin. 
Definition ch_choiceMixin := [choiceMixin of ch by <:].
Canonical ch_ChoiceType := Eval hnf in ChoiceType ch ch_choiceMixin.
Definition ch_countMixin := [countMixin of ch by <:].
Canonical ch_countType := CountType ch ch_countMixin.


Inductive action  : Set := Action of ptcp & ptcp & ch.

Definition prod_of_action (a : action) := let '(Action p0 p1 c) := a in (p0,p1,c). 
Definition action_indDef := [indDef for action_rect].
Canonical action_indType := IndType action action_indDef.
Definition action_eqMixin := [derive eqMixin for action].
Canonical action_eqType := EqType action action_eqMixin.
Definition action_choiceMixin := [derive choiceMixin for action].
Canonical action_choiceType := ChoiceType action action_choiceMixin.
Definition action_countMixin := [derive countMixin for action].
Canonical action_countType := CountType action action_countMixin.

Definition ptcp_from (a : action) := let : Action p0 _ _ := a in p0.
Definition ptcp_to (a : action) := let : Action _ p1 _ := a in p1.
Definition action_ch (a : action) := let : Action _ _ c := a in c.


Inductive dir := Sd | Rd.

Definition dir_eq (d0 d1 : dir) := 
match d0,d1 with 
| Sd,Sd => true 
| Rd,Rd => true
| _,_ => false 
end.

Check Equality.axiom.

Lemma dir_axiom : Equality.axiom dir_eq. 
Proof.
rewrite /Equality.axiom. move => [] []; rewrite /=;try done;auto. constructor. done. constructor. done. intros. 
constructor.  done. constructor. done.
Qed.

Definition dir_mixin := EqMixin  dir_axiom.
Canonical dir_eqType := EqType dir dir_mixin.


Unset Elimination Schemes. 
Inductive gType  : Set :=
  | GVar : nat -> gType  
  | GEnd : gType  
  | GRec : gType -> gType  
  | GMsg : action -> value -> gType -> gType  
  | GBranch : action -> seq gType -> gType  
 with value  : Set  :=
  | VSeqSort : seq mysort -> value  
  | VLT : lType -> ptcp  -> value  
 with mysort  : Set :=
  | SBool : mysort
  | SNat : mysort  
  | SGType : gType -> mysort (*maybe more sorts?*)
 with lType  : Set :=
  | EVar : nat -> lType  
  | EEnd : lType  
  | EMsg : dir -> ch -> value -> lType -> lType  
  | EBranch  : dir -> ch  -> seq lType -> lType  
  | ERec : lType -> lType . 
Set Elimination Schemes.

Section lType.


Lemma congr_EEnd  : EEnd  = EEnd  .
Proof. congruence. Qed.

Lemma congr_ERec  { s0 : lType   } { t0 : lType   } (H1 : s0 = t0) : ERec  s0 = ERec  t0 .
Proof. congruence. Qed.

Lemma congr_EMsg  { s0 : dir   } { s1 : ch   } { s2 : value   } { s3 : lType   } { t0 : dir   } { t1 : ch   } { t2 : value   } { t3 : lType   } (H1 : s0 = t0) (H2 : s1 = t1) (H3 : s2 = t2) (H4 : s3 = t3) : EMsg  s0 s1 s2 s3 = EMsg  t0 t1 t2 t3 .
Proof. congruence. Qed.

Lemma congr_EBranch  { s0 : dir   } { s1 : ch   } { s2 : list (lType  ) } { t0 : dir   } { t1 : ch   } { t2 : list (lType  ) } (H1 : s0 = t0) (H2 : s1 = t1) (H3 : s2 = t2) : EBranch  s0 s1 s2 = EBranch  t0 t1 t2 .
Proof. congruence. Qed.

Definition upRen_lType_lType   (xi : ( fin ) -> fin) : ( fin ) -> fin :=
  (up_ren) xi.

Fixpoint ren_lType   (xilType : ( fin ) -> fin) (s : lType ) : lType  :=
    match s return lType  with
    | EVar  s => (EVar ) (xilType s)
    | EEnd   => EEnd 
    | ERec  s0 => ERec  ((ren_lType (upRen_lType_lType xilType)) s0)
    | EMsg  s0 s1 s2 s3 => EMsg  ((fun x => x) s0) ((fun x => x) s1) ((fun x => x) s2) ((ren_lType xilType) s3)
    | EBranch  s0 s1 s2 => EBranch  ((fun x => x) s0) ((fun x => x) s1) ((map (ren_lType xilType)) s2)
    end.

Definition up_lType_lType   (sigma : ( fin ) -> lType ) : ( fin ) -> lType  :=
  (scons) ((EVar ) (var_zero)) ((funcomp) (ren_lType (shift)) sigma).

Fixpoint subst_lType   (sigmalType : ( fin ) -> lType ) (s : lType ) : lType  :=
    match s return lType  with
    | EVar  s => sigmalType s
    | EEnd   => EEnd 
    | ERec  s0 => ERec  ((subst_lType (up_lType_lType sigmalType)) s0)
    | EMsg  s0 s1 s2 s3 => EMsg  ((fun x => x) s0) ((fun x => x) s1) ((fun x => x) s2) ((subst_lType sigmalType) s3)
    | EBranch  s0 s1 s2 => EBranch  ((fun x => x) s0) ((fun x => x) s1) ((map (subst_lType sigmalType)) s2)
    end.




Definition upId_lType_lType  (sigma : ( fin ) -> lType ) (Eq : forall x, sigma x = (EVar ) x) : forall x, (up_lType_lType sigma) x = (EVar ) x :=
  fun n => match n with
  | S fin_n => (ap) (ren_lType (shift)) (Eq fin_n)
  | 0  => Logic.eq_refl
  end.


Fixpoint idSubst_lType  (sigmalType : ( fin ) -> lType ) (EqlType : forall x, sigmalType x = (EVar ) x) (s : lType ) : subst_lType sigmalType s = s :=
    match s return subst_lType sigmalType s = s with
    | EVar  s => EqlType s
    | EEnd   => congr_EEnd 
    | ERec  s0 => congr_ERec ((@idSubst_lType (up_lType_lType sigmalType) (@upId_lType_lType (_) EqlType)) s0)
    | EMsg  s0 s1 s2 s3 => congr_EMsg ((fun x => (Logic.eq_refl) x) s0) ((fun x => (Logic.eq_refl) x) s1) ((fun x => (Logic.eq_refl) x) s2) ((@idSubst_lType sigmalType  EqlType) s3)
    | EBranch  s0 s1 s2 => congr_EBranch ((fun x => (Logic.eq_refl) x) s0) ((fun x => (Logic.eq_refl) x) s1) ((list_id (@idSubst_lType sigmalType EqlType)) s2)
    end.



Definition upExtRen_lType_lType   (xi : ( fin ) -> fin) (zeta : ( fin ) -> fin) (Eq : forall x, xi x = zeta x) : forall x, (upRen_lType_lType xi) x = (upRen_lType_lType zeta) x :=
  fun n => match n with
  | S fin_n => (ap) (shift) (Eq fin_n)
  | 0  => Logic.eq_refl
  end.


Fixpoint extRen_lType   (xilType : ( fin ) -> fin) (zetalType : ( fin ) -> fin) (EqlType : forall x, xilType x = zetalType x) (s : lType ) : ren_lType xilType s = ren_lType zetalType s :=
    match s return ren_lType xilType s = ren_lType zetalType s with
    | EVar  s => (ap) (EVar ) (EqlType s)
    | EEnd   => congr_EEnd 
    | ERec  s0 => congr_ERec ((@extRen_lType (upRen_lType_lType xilType) (upRen_lType_lType zetalType) (@upExtRen_lType_lType (_) (_) EqlType)) s0)
    | EMsg  s0 s1 s2 s3 => congr_EMsg ((fun x => (Logic.eq_refl) x) s0) ((fun x => (Logic.eq_refl) x) s1) ((fun x => (Logic.eq_refl) x) s2) ((@extRen_lType xilType zetalType EqlType) s3)
    | EBranch  s0 s1 s2 => congr_EBranch ((fun x => (Logic.eq_refl) x) s0) ((fun x => (Logic.eq_refl) x) s1) ((list_ext (@extRen_lType xilType zetalType EqlType)) s2)
    end.

Definition upExt_lType_lType   (sigma : ( fin ) -> lType ) (tau : ( fin ) -> lType ) (Eq : forall x, sigma x = tau x) : forall x, (up_lType_lType sigma) x = (up_lType_lType tau) x :=
  fun n => match n with
  | S fin_n => (ap) (ren_lType (shift)) (Eq fin_n)
  | 0  => Logic.eq_refl
  end.

Fixpoint ext_lType   (sigmalType : ( fin ) -> lType ) (taulType : ( fin ) -> lType ) (EqlType : forall x, sigmalType x = taulType x) (s : lType ) : subst_lType sigmalType s = subst_lType taulType s :=
    match s return subst_lType sigmalType s = subst_lType taulType s with
    | EVar  s => EqlType s
    | EEnd   => congr_EEnd 
    | ERec  s0 => congr_ERec ((ext_lType (up_lType_lType sigmalType) (up_lType_lType taulType) (upExt_lType_lType (_) (_) EqlType)) s0)
    | EMsg  s0 s1 s2 s3 => congr_EMsg ((fun x => (Logic.eq_refl) x) s0) ((fun x => (Logic.eq_refl) x) s1) ((fun x => (Logic.eq_refl) x) s2) ((ext_lType sigmalType taulType EqlType) s3)
    | EBranch  s0 s1 s2 => congr_EBranch ((fun x => (Logic.eq_refl) x) s0) ((fun x => (Logic.eq_refl) x) s1) ((list_ext (ext_lType sigmalType taulType EqlType)) s2)
    end.

Definition up_ren_ren_lType_lType    (xi : ( fin ) -> fin) (tau : ( fin ) -> fin) (theta : ( fin ) -> fin) (Eq : forall x, ((funcomp) tau xi) x = theta x) : forall x, ((funcomp) (upRen_lType_lType tau) (upRen_lType_lType xi)) x = (upRen_lType_lType theta) x :=
  up_ren_ren xi tau theta Eq.

Fixpoint compRenRen_lType    (xilType : ( fin ) -> fin) (zetalType : ( fin ) -> fin) (rholType : ( fin ) -> fin) (EqlType : forall x, ((funcomp) zetalType xilType) x = rholType x) (s : lType ) : ren_lType zetalType (ren_lType xilType s) = ren_lType rholType s :=
    match s return ren_lType zetalType (ren_lType xilType s) = ren_lType rholType s with
    | EVar  s => (ap) (EVar ) (EqlType s)
    | EEnd   => congr_EEnd 
    | ERec  s0 => congr_ERec ((compRenRen_lType (upRen_lType_lType xilType) (upRen_lType_lType zetalType) (upRen_lType_lType rholType) (up_ren_ren (_) (_) (_) EqlType)) s0)
    | EMsg  s0 s1 s2 s3 => congr_EMsg ((fun x => (Logic.eq_refl) x) s0) ((fun x => (Logic.eq_refl) x) s1) ((fun x => (Logic.eq_refl) x) s2) ((compRenRen_lType xilType zetalType rholType EqlType) s3)
    | EBranch  s0 s1 s2 => congr_EBranch ((fun x => (Logic.eq_refl) x) s0) ((fun x => (Logic.eq_refl) x) s1) ((list_comp (compRenRen_lType xilType zetalType rholType EqlType)) s2)
    end.

Definition up_ren_subst_lType_lType    (xi : ( fin ) -> fin) (tau : ( fin ) -> lType ) (theta : ( fin ) -> lType ) (Eq : forall x, ((funcomp) tau xi) x = theta x) : forall x, ((funcomp) (up_lType_lType tau) (upRen_lType_lType xi)) x = (up_lType_lType theta) x :=
  fun n => match n with
  | S fin_n => (ap) (ren_lType (shift)) (Eq fin_n)
  | 0  => Logic.eq_refl
  end.

Fixpoint compRenSubst_lType    (xilType : ( fin ) -> fin) (taulType : ( fin ) -> lType ) (thetalType : ( fin ) -> lType ) (EqlType : forall x, ((funcomp) taulType xilType) x = thetalType x) (s : lType ) : subst_lType taulType (ren_lType xilType s) = subst_lType thetalType s :=
    match s return subst_lType taulType (ren_lType xilType s) = subst_lType thetalType s with
    | EVar  s => EqlType s
    | EEnd   => congr_EEnd 
    | ERec  s0 => congr_ERec ((compRenSubst_lType (upRen_lType_lType xilType) (up_lType_lType taulType) (up_lType_lType thetalType) (up_ren_subst_lType_lType (_) (_) (_) EqlType)) s0)
    | EMsg  s0 s1 s2 s3 => congr_EMsg ((fun x => (Logic.eq_refl) x) s0) ((fun x => (Logic.eq_refl) x) s1) ((fun x => (Logic.eq_refl) x) s2) ((compRenSubst_lType xilType taulType thetalType EqlType) s3)
    | EBranch  s0 s1 s2 => congr_EBranch ((fun x => (Logic.eq_refl) x) s0) ((fun x => (Logic.eq_refl) x) s1) ((list_comp (compRenSubst_lType xilType taulType thetalType EqlType)) s2)
    end.

Check compRenRen_lType. Check Logic.eq_sym. Check eq_sym.
Definition up_subst_ren_lType_lType    (sigma : ( fin ) -> lType ) (zetalType : ( fin ) -> fin) (theta : ( fin ) -> lType ) (Eq : forall x, ((funcomp) (ren_lType zetalType) sigma) x = theta x) : 
forall x, ((funcomp) (ren_lType (upRen_lType_lType zetalType)) (up_lType_lType sigma)) x = (up_lType_lType theta) x :=
  fun n => match n with
  | S fin_n => (eq_trans) (compRenRen_lType (shift) (upRen_lType_lType zetalType) ((funcomp) (shift) zetalType) (fun x => Logic.eq_refl) (sigma fin_n)) 
              ((eq_trans) ((Logic.eq_sym) (compRenRen_lType zetalType (shift) ((funcomp) (shift) zetalType) (fun x => Logic.eq_refl) (sigma fin_n))) 
                          ((ap) (ren_lType (shift)) (Eq fin_n)))
  | 0  => Logic.eq_refl
  end.

Fixpoint compSubstRen_lType    (sigmalType : ( fin ) -> lType ) (zetalType : ( fin ) -> fin) (thetalType : ( fin ) -> lType ) (EqlType : forall x, ((funcomp) (ren_lType zetalType) sigmalType) x = thetalType x) (s : lType ) : ren_lType zetalType (subst_lType sigmalType s) = subst_lType thetalType s :=
    match s return ren_lType zetalType (subst_lType sigmalType s) = subst_lType thetalType s with
    | EVar  s => EqlType s
    | EEnd   => congr_EEnd 
    | ERec  s0 => congr_ERec ((compSubstRen_lType (up_lType_lType sigmalType) (upRen_lType_lType zetalType) (up_lType_lType thetalType) (up_subst_ren_lType_lType (_) (_) (_) EqlType)) s0)
    | EMsg  s0 s1 s2 s3 => congr_EMsg ((fun x => (Logic.eq_refl) x) s0) ((fun x => (Logic.eq_refl) x) s1) ((fun x => (Logic.eq_refl) x) s2) ((compSubstRen_lType sigmalType zetalType thetalType EqlType) s3)
    | EBranch  s0 s1 s2 => congr_EBranch ((fun x => (Logic.eq_refl) x) s0) ((fun x => (Logic.eq_refl) x) s1) ((list_comp (compSubstRen_lType sigmalType zetalType thetalType EqlType)) s2)
    end.

Definition up_subst_subst_lType_lType    (sigma : ( fin ) -> lType ) (taulType : ( fin ) -> lType ) (theta : ( fin ) -> lType ) (Eq : forall x, ((funcomp) (subst_lType taulType) sigma) x = theta x) : forall x, ((funcomp) (subst_lType (up_lType_lType taulType)) (up_lType_lType sigma)) x = (up_lType_lType theta) x :=
  fun n => match n with
  | S fin_n => (eq_trans) (compRenSubst_lType (shift) (up_lType_lType taulType) ((funcomp) (up_lType_lType taulType) (shift)) (fun x => Logic.eq_refl) (sigma fin_n)) ((eq_trans) ((Logic.eq_sym) (compSubstRen_lType taulType (shift) ((funcomp) (ren_lType (shift)) taulType) (fun x => Logic.eq_refl) (sigma fin_n))) ((ap) (ren_lType (shift)) (Eq fin_n)))
  | 0  => Logic.eq_refl
  end.

Fixpoint compSubstSubst_lType    (sigmalType : ( fin ) -> lType ) (taulType : ( fin ) -> lType ) (thetalType : ( fin ) -> lType ) (EqlType : forall x, ((funcomp) (subst_lType taulType) sigmalType) x = thetalType x) (s : lType ) : subst_lType taulType (subst_lType sigmalType s) = subst_lType thetalType s :=
    match s return subst_lType taulType (subst_lType sigmalType s) = subst_lType thetalType s with
    | EVar  s => EqlType s
    | EEnd   => congr_EEnd 
    | ERec  s0 => congr_ERec ((compSubstSubst_lType (up_lType_lType sigmalType) (up_lType_lType taulType) (up_lType_lType thetalType) (up_subst_subst_lType_lType (_) (_) (_) EqlType)) s0)
    | EMsg  s0 s1 s2 s3 => congr_EMsg ((fun x => (Logic.eq_refl) x) s0) ((fun x => (Logic.eq_refl) x) s1) ((fun x => (Logic.eq_refl) x) s2) ((compSubstSubst_lType sigmalType taulType thetalType EqlType) s3)
    | EBranch  s0 s1 s2 => congr_EBranch ((fun x => (Logic.eq_refl) x) s0) ((fun x => (Logic.eq_refl) x) s1) ((list_comp (compSubstSubst_lType sigmalType taulType thetalType EqlType)) s2)
    end.

Definition rinstInst_up_lType_lType   (xi : ( fin ) -> fin) (sigma : ( fin ) -> lType ) (Eq : forall x, ((funcomp) (EVar ) xi) x = sigma x) : forall x, ((funcomp) (EVar ) (upRen_lType_lType xi)) x = (up_lType_lType sigma) x :=
  fun n => match n with
  | S fin_n => (ap) (ren_lType (shift)) (Eq fin_n)
  | 0  => Logic.eq_refl
  end.

Fixpoint rinst_inst_lType   (xilType : ( fin ) -> fin) (sigmalType : ( fin ) -> lType ) (EqlType : forall x, ((funcomp) (EVar ) xilType) x = sigmalType x) (s : lType ) : ren_lType xilType s = subst_lType sigmalType s :=
    match s return ren_lType xilType s = subst_lType sigmalType s with
    | EVar  s => EqlType s
    | EEnd   => congr_EEnd 
    | ERec  s0 => congr_ERec ((rinst_inst_lType (upRen_lType_lType xilType) (up_lType_lType sigmalType) (rinstInst_up_lType_lType (_) (_) EqlType)) s0)
    | EMsg  s0 s1 s2 s3 => congr_EMsg ((fun x => (Logic.eq_refl) x) s0) ((fun x => (Logic.eq_refl) x) s1) ((fun x => (Logic.eq_refl) x) s2) ((rinst_inst_lType xilType sigmalType EqlType) s3)
    | EBranch  s0 s1 s2 => congr_EBranch ((fun x => (Logic.eq_refl) x) s0) ((fun x => (Logic.eq_refl) x) s1) ((list_ext (rinst_inst_lType xilType sigmalType EqlType)) s2)
    end.

Lemma rinstInst_lType   (xilType : ( fin ) -> fin) : ren_lType xilType = subst_lType ((funcomp) (EVar ) xilType) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => rinst_inst_lType xilType (_) (fun n => Logic.eq_refl) x)). Qed.

Lemma instId_lType  : subst_lType (EVar ) = id .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => idSubst_lType (EVar ) (fun n => Logic.eq_refl) ((id) x))). Qed.

Lemma rinstId_lType  : @ren_lType   (id) = id .
Proof. exact ((eq_trans) (rinstInst_lType ((id) (_))) instId_lType). Qed.

Lemma varL_lType   (sigmalType : ( fin ) -> lType ) : (funcomp) (subst_lType sigmalType) (EVar ) = sigmalType .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => Logic.eq_refl)). Qed.

Lemma varLRen_lType   (xilType : ( fin ) -> fin) : (funcomp) (ren_lType xilType) (EVar ) = (funcomp) (EVar ) xilType .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => Logic.eq_refl)). Qed.

Lemma compComp_lType    (sigmalType : ( fin ) -> lType ) (taulType : ( fin ) -> lType ) (s : lType ) : subst_lType taulType (subst_lType sigmalType s) = subst_lType ((funcomp) (subst_lType taulType) sigmalType) s .
Proof. exact (compSubstSubst_lType sigmalType taulType (_) (fun n => Logic.eq_refl) s). Qed.

Lemma compComp'_lType    (sigmalType : ( fin ) -> lType ) (taulType : ( fin ) -> lType ) : (funcomp) (subst_lType taulType) (subst_lType sigmalType) = subst_lType ((funcomp) (subst_lType taulType) sigmalType) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => compComp_lType sigmalType taulType n)). Qed.

Lemma compRen_lType    (sigmalType : ( fin ) -> lType ) (zetalType : ( fin ) -> fin) (s : lType ) : ren_lType zetalType (subst_lType sigmalType s) = subst_lType ((funcomp) (ren_lType zetalType) sigmalType) s .
Proof. exact (compSubstRen_lType sigmalType zetalType (_) (fun n => Logic.eq_refl) s). Qed.

Lemma compRen'_lType    (sigmalType : ( fin ) -> lType ) (zetalType : ( fin ) -> fin) : (funcomp) (ren_lType zetalType) (subst_lType sigmalType) = subst_lType ((funcomp) (ren_lType zetalType) sigmalType) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => compRen_lType sigmalType zetalType n)). Qed.

Lemma renComp_lType    (xilType : ( fin ) -> fin) (taulType : ( fin ) -> lType ) (s : lType ) : subst_lType taulType (ren_lType xilType s) = subst_lType ((funcomp) taulType xilType) s .
Proof. exact (compRenSubst_lType xilType taulType (_) (fun n => Logic.eq_refl) s). Qed.

Lemma renComp'_lType    (xilType : ( fin ) -> fin) (taulType : ( fin ) -> lType ) : (funcomp) (subst_lType taulType) (ren_lType xilType) = subst_lType ((funcomp) taulType xilType) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => renComp_lType xilType taulType n)). Qed.

Lemma renRen_lType    (xilType : ( fin ) -> fin) (zetalType : ( fin ) -> fin) (s : lType ) : ren_lType zetalType (ren_lType xilType s) = ren_lType ((funcomp) zetalType xilType) s .
Proof. exact (compRenRen_lType xilType zetalType (_) (fun n => Logic.eq_refl) s). Qed.

Lemma renRen'_lType    (xilType : ( fin ) -> fin) (zetalType : ( fin ) -> fin) : (funcomp) (ren_lType zetalType) (ren_lType xilType) = ren_lType ((funcomp) zetalType xilType) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => renRen_lType xilType zetalType n)). Qed.

End lType.


Section gType.


Lemma congr_GEnd  : GEnd  = GEnd  .
Proof. congruence. Qed.

Lemma congr_GRec  { s0 : gType   } { t0 : gType   } (H1 : s0 = t0) : GRec  s0 = GRec  t0 .
Proof. congruence. Qed.

Lemma congr_GMsg  { s0 : action   } { s1 : value   } { s2 : gType   } { t0 : action   } { t1 : value   } { t2 : gType   } (H1 : s0 = t0) (H2 : s1 = t1) (H3 : s2 = t2) : GMsg  s0 s1 s2 = GMsg  t0 t1 t2 .
Proof. congruence. Qed.

Lemma congr_GBranch  { s0 : action   } { s1 : list (gType  ) } { t0 : action   } { t1 : list (gType  ) } (H1 : s0 = t0) (H2 : s1 = t1) : GBranch  s0 s1 = GBranch  t0 t1 .
Proof. congruence. Qed.

Definition upRen_gType_gType   (xi : ( fin ) -> fin) : ( fin ) -> fin :=
  (up_ren) xi.

Fixpoint ren_gType   (xigType : ( fin ) -> fin) (s : gType ) : gType  :=
    match s return gType  with
    | GVar  s => (GVar ) (xigType s)
    | GEnd   => GEnd 
    | GRec  s0 => GRec  ((ren_gType (upRen_gType_gType xigType)) s0)
    | GMsg  s0 s1 s2 => GMsg  ((fun x => x) s0) ((fun x => x) s1) ((ren_gType xigType) s2)
    | GBranch  s0 s1 => GBranch  ((fun x => x) s0) ((map (ren_gType xigType)) s1)
    end.

Definition up_gType_gType   (sigma : ( fin ) -> gType ) : ( fin ) -> gType  :=
  (scons) ((GVar ) (var_zero)) ((funcomp) (ren_gType (shift)) sigma).

Fixpoint subst_gType   (sigmagType : ( fin ) -> gType ) (s : gType ) : gType  :=
    match s return gType  with
    | GVar  s => sigmagType s
    | GEnd   => GEnd 
    | GRec  s0 => GRec  ((subst_gType (up_gType_gType sigmagType)) s0)
    | GMsg  s0 s1 s2 => GMsg  ((fun x => x) s0) ((fun x => x) s1) ((subst_gType sigmagType) s2)
    | GBranch  s0 s1 => GBranch  ((fun x => x) s0) ((map (subst_gType sigmagType)) s1)
    end.

Definition upId_gType_gType  (sigma : ( fin ) -> gType ) (Eq : forall x, sigma x = (GVar ) x) : forall x, (up_gType_gType sigma) x = (GVar ) x :=
  fun n => match n with
  | S fin_n => (ap) (ren_gType (shift)) (Eq fin_n)
  | 0  => Logic.eq_refl
  end.

Fixpoint idSubst_gType  (sigmagType : ( fin ) -> gType ) (EqgType : forall x, sigmagType x = (GVar ) x) (s : gType ) : subst_gType sigmagType s = s :=
    match s return subst_gType sigmagType s = s with
    | GVar  s => EqgType s
    | GEnd   => congr_GEnd 
    | GRec  s0 => congr_GRec ((idSubst_gType (up_gType_gType sigmagType) (upId_gType_gType (_) EqgType)) s0)
    | GMsg  s0 s1 s2 => congr_GMsg ((fun x => (Logic.eq_refl) x) s0) ((fun x => (Logic.eq_refl) x) s1) ((idSubst_gType sigmagType EqgType) s2)
    | GBranch  s0 s1 => congr_GBranch ((fun x => (Logic.eq_refl) x) s0) ((list_id (idSubst_gType sigmagType EqgType)) s1)
    end.

Definition upExtRen_gType_gType   (xi : ( fin ) -> fin) (zeta : ( fin ) -> fin) (Eq : forall x, xi x = zeta x) : forall x, (upRen_gType_gType xi) x = (upRen_gType_gType zeta) x :=
  fun n => match n with
  | S fin_n => (ap) (shift) (Eq fin_n)
  | 0  => Logic.eq_refl
  end.

Fixpoint extRen_gType   (xigType : ( fin ) -> fin) (zetagType : ( fin ) -> fin) (EqgType : forall x, xigType x = zetagType x) (s : gType ) : ren_gType xigType s = ren_gType zetagType s :=
    match s return ren_gType xigType s = ren_gType zetagType s with
    | GVar  s => (ap) (GVar ) (EqgType s)
    | GEnd   => congr_GEnd 
    | GRec  s0 => congr_GRec ((extRen_gType (upRen_gType_gType xigType) (upRen_gType_gType zetagType) (upExtRen_gType_gType (_) (_) EqgType)) s0)
    | GMsg  s0 s1 s2 => congr_GMsg ((fun x => (Logic.eq_refl) x) s0) ((fun x => (Logic.eq_refl) x) s1) ((extRen_gType xigType zetagType EqgType) s2)
    | GBranch  s0 s1 => congr_GBranch ((fun x => (Logic.eq_refl) x) s0) ((list_ext (extRen_gType xigType zetagType EqgType)) s1)
    end.

Definition upExt_gType_gType   (sigma : ( fin ) -> gType ) (tau : ( fin ) -> gType ) (Eq : forall x, sigma x = tau x) : forall x, (up_gType_gType sigma) x = (up_gType_gType tau) x :=
  fun n => match n with
  | S fin_n => (ap) (ren_gType (shift)) (Eq fin_n)
  | 0  => Logic.eq_refl
  end.

Fixpoint ext_gType   (sigmagType : ( fin ) -> gType ) (taugType : ( fin ) -> gType ) (EqgType : forall x, sigmagType x = taugType x) (s : gType ) : subst_gType sigmagType s = subst_gType taugType s :=
    match s return subst_gType sigmagType s = subst_gType taugType s with
    | GVar  s => EqgType s
    | GEnd   => congr_GEnd 
    | GRec  s0 => congr_GRec ((ext_gType (up_gType_gType sigmagType) (up_gType_gType taugType) (upExt_gType_gType (_) (_) EqgType)) s0)
    | GMsg  s0 s1 s2 => congr_GMsg ((fun x => (Logic.eq_refl) x) s0) ((fun x => (Logic.eq_refl) x) s1) ((ext_gType sigmagType taugType EqgType) s2)
    | GBranch  s0 s1 => congr_GBranch ((fun x => (Logic.eq_refl) x) s0) ((list_ext (ext_gType sigmagType taugType EqgType)) s1)
    end.

Definition up_ren_ren_gType_gType    (xi : ( fin ) -> fin) (tau : ( fin ) -> fin) (theta : ( fin ) -> fin) (Eq : forall x, ((funcomp) tau xi) x = theta x) : forall x, ((funcomp) (upRen_gType_gType tau) (upRen_gType_gType xi)) x = (upRen_gType_gType theta) x :=
  up_ren_ren xi tau theta Eq.

Fixpoint compRenRen_gType    (xigType : ( fin ) -> fin) (zetagType : ( fin ) -> fin) (rhogType : ( fin ) -> fin) (EqgType : forall x, ((funcomp) zetagType xigType) x = rhogType x) (s : gType ) : ren_gType zetagType (ren_gType xigType s) = ren_gType rhogType s :=
    match s return ren_gType zetagType (ren_gType xigType s) = ren_gType rhogType s with
    | GVar  s => (ap) (GVar ) (EqgType s)
    | GEnd   => congr_GEnd 
    | GRec  s0 => congr_GRec ((compRenRen_gType (upRen_gType_gType xigType) (upRen_gType_gType zetagType) (upRen_gType_gType rhogType) (up_ren_ren (_) (_) (_) EqgType)) s0)
    | GMsg  s0 s1 s2 => congr_GMsg ((fun x => (Logic.eq_refl) x) s0) ((fun x => (Logic.eq_refl) x) s1) ((compRenRen_gType xigType zetagType rhogType EqgType) s2)
    | GBranch  s0 s1 => congr_GBranch ((fun x => (Logic.eq_refl) x) s0) ((list_comp (compRenRen_gType xigType zetagType rhogType EqgType)) s1)
    end.

Definition up_ren_subst_gType_gType    (xi : ( fin ) -> fin) (tau : ( fin ) -> gType ) (theta : ( fin ) -> gType ) (Eq : forall x, ((funcomp) tau xi) x = theta x) : forall x, ((funcomp) (up_gType_gType tau) (upRen_gType_gType xi)) x = (up_gType_gType theta) x :=
  fun n => match n with
  | S fin_n => (ap) (ren_gType (shift)) (Eq fin_n)
  | 0  => Logic.eq_refl
  end.

Fixpoint compRenSubst_gType    (xigType : ( fin ) -> fin) (taugType : ( fin ) -> gType ) (thetagType : ( fin ) -> gType ) (EqgType : forall x, ((funcomp) taugType xigType) x = thetagType x) (s : gType ) : subst_gType taugType (ren_gType xigType s) = subst_gType thetagType s :=
    match s return subst_gType taugType (ren_gType xigType s) = subst_gType thetagType s with
    | GVar  s => EqgType s
    | GEnd   => congr_GEnd 
    | GRec  s0 => congr_GRec ((compRenSubst_gType (upRen_gType_gType xigType) (up_gType_gType taugType) (up_gType_gType thetagType) (up_ren_subst_gType_gType (_) (_) (_) EqgType)) s0)
    | GMsg  s0 s1 s2 => congr_GMsg ((fun x => (Logic.eq_refl) x) s0) ((fun x => (Logic.eq_refl) x) s1) ((compRenSubst_gType xigType taugType thetagType EqgType) s2)
    | GBranch  s0 s1 => congr_GBranch ((fun x => (Logic.eq_refl) x) s0) ((list_comp (compRenSubst_gType xigType taugType thetagType EqgType)) s1)
    end.

Definition up_subst_ren_gType_gType    (sigma : ( fin ) -> gType ) (zetagType : ( fin ) -> fin) (theta : ( fin ) -> gType ) (Eq : forall x, ((funcomp) (ren_gType zetagType) sigma) x = theta x) : forall x, ((funcomp) (ren_gType (upRen_gType_gType zetagType)) (up_gType_gType sigma)) x = (up_gType_gType theta) x :=
  fun n => match n with
  | S fin_n => (eq_trans) (compRenRen_gType (shift) (upRen_gType_gType zetagType) ((funcomp) (shift) zetagType) (fun x => Logic.eq_refl) (sigma fin_n)) ((eq_trans) ((Logic.eq_sym) (compRenRen_gType zetagType (shift) ((funcomp) (shift) zetagType) (fun x => Logic.eq_refl) (sigma fin_n))) ((ap) (ren_gType (shift)) (Eq fin_n)))
  | 0  => Logic.eq_refl
  end.

Fixpoint compSubstRen_gType    (sigmagType : ( fin ) -> gType ) (zetagType : ( fin ) -> fin) (thetagType : ( fin ) -> gType ) (EqgType : forall x, ((funcomp) (ren_gType zetagType) sigmagType) x = thetagType x) (s : gType ) : ren_gType zetagType (subst_gType sigmagType s) = subst_gType thetagType s :=
    match s return ren_gType zetagType (subst_gType sigmagType s) = subst_gType thetagType s with
    | GVar  s => EqgType s
    | GEnd   => congr_GEnd 
    | GRec  s0 => congr_GRec ((compSubstRen_gType (up_gType_gType sigmagType) (upRen_gType_gType zetagType) (up_gType_gType thetagType) (up_subst_ren_gType_gType (_) (_) (_) EqgType)) s0)
    | GMsg  s0 s1 s2 => congr_GMsg ((fun x => (Logic.eq_refl) x) s0) ((fun x => (Logic.eq_refl) x) s1) ((compSubstRen_gType sigmagType zetagType thetagType EqgType) s2)
    | GBranch  s0 s1 => congr_GBranch ((fun x => (Logic.eq_refl) x) s0) ((list_comp (compSubstRen_gType sigmagType zetagType thetagType EqgType)) s1)
    end.

Definition up_subst_subst_gType_gType    (sigma : ( fin ) -> gType ) (taugType : ( fin ) -> gType ) (theta : ( fin ) -> gType ) (Eq : forall x, ((funcomp) (subst_gType taugType) sigma) x = theta x) : forall x, ((funcomp) (subst_gType (up_gType_gType taugType)) (up_gType_gType sigma)) x = (up_gType_gType theta) x :=
  fun n => match n with
  | S fin_n => (eq_trans) (compRenSubst_gType (shift) (up_gType_gType taugType) ((funcomp) (up_gType_gType taugType) (shift)) (fun x => Logic.eq_refl) (sigma fin_n)) ((eq_trans) ((Logic.eq_sym) (compSubstRen_gType taugType (shift) ((funcomp) (ren_gType (shift)) taugType) (fun x => Logic.eq_refl) (sigma fin_n))) ((ap) (ren_gType (shift)) (Eq fin_n)))
  | 0  => Logic.eq_refl
  end.

Fixpoint compSubstSubst_gType    (sigmagType : ( fin ) -> gType ) (taugType : ( fin ) -> gType ) (thetagType : ( fin ) -> gType ) (EqgType : forall x, ((funcomp) (subst_gType taugType) sigmagType) x = thetagType x) (s : gType ) : subst_gType taugType (subst_gType sigmagType s) = subst_gType thetagType s :=
    match s return subst_gType taugType (subst_gType sigmagType s) = subst_gType thetagType s with
    | GVar  s => EqgType s
    | GEnd   => congr_GEnd 
    | GRec  s0 => congr_GRec ((compSubstSubst_gType (up_gType_gType sigmagType) (up_gType_gType taugType) (up_gType_gType thetagType) (up_subst_subst_gType_gType (_) (_) (_) EqgType)) s0)
    | GMsg  s0 s1 s2 => congr_GMsg ((fun x => (Logic.eq_refl) x) s0) ((fun x => (Logic.eq_refl) x) s1) ((compSubstSubst_gType sigmagType taugType thetagType EqgType) s2)
    | GBranch  s0 s1 => congr_GBranch ((fun x => (Logic.eq_refl) x) s0) ((list_comp (compSubstSubst_gType sigmagType taugType thetagType EqgType)) s1)
    end.

Definition rinstInst_up_gType_gType   (xi : ( fin ) -> fin) (sigma : ( fin ) -> gType ) (Eq : forall x, ((funcomp) (GVar ) xi) x = sigma x) : forall x, ((funcomp) (GVar ) (upRen_gType_gType xi)) x = (up_gType_gType sigma) x :=
  fun n => match n with
  | S fin_n => (ap) (ren_gType (shift)) (Eq fin_n)
  | 0  => Logic.eq_refl
  end.

Fixpoint rinst_inst_gType   (xigType : ( fin ) -> fin) (sigmagType : ( fin ) -> gType ) (EqgType : forall x, ((funcomp) (GVar ) xigType) x = sigmagType x) (s : gType ) : ren_gType xigType s = subst_gType sigmagType s :=
    match s return ren_gType xigType s = subst_gType sigmagType s with
    | GVar  s => EqgType s
    | GEnd   => congr_GEnd 
    | GRec  s0 => congr_GRec ((rinst_inst_gType (upRen_gType_gType xigType) (up_gType_gType sigmagType) (rinstInst_up_gType_gType (_) (_) EqgType)) s0)
    | GMsg  s0 s1 s2 => congr_GMsg ((fun x => (Logic.eq_refl) x) s0) ((fun x => (Logic.eq_refl) x) s1) ((rinst_inst_gType xigType sigmagType EqgType) s2)
    | GBranch  s0 s1 => congr_GBranch ((fun x => (Logic.eq_refl) x) s0) ((list_ext (rinst_inst_gType xigType sigmagType EqgType)) s1)
    end.

Lemma rinstInst_gType   (xigType : ( fin ) -> fin) : ren_gType xigType = subst_gType ((funcomp) (GVar ) xigType) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => rinst_inst_gType xigType (_) (fun n => Logic.eq_refl) x)). Qed.

Lemma instId_gType  : subst_gType (GVar ) = id .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => idSubst_gType (GVar ) (fun n => Logic.eq_refl) ((id) x))). Qed.

Lemma rinstId_gType  : @ren_gType   (id) = id .
Proof. exact ((eq_trans) (rinstInst_gType ((id) (_))) instId_gType). Qed.

Lemma varL_gType   (sigmagType : ( fin ) -> gType ) : (funcomp) (subst_gType sigmagType) (GVar ) = sigmagType .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => Logic.eq_refl)). Qed.

Lemma varLRen_gType   (xigType : ( fin ) -> fin) : (funcomp) (ren_gType xigType) (GVar ) = (funcomp) (GVar ) xigType .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => Logic.eq_refl)). Qed.

Lemma compComp_gType    (sigmagType : ( fin ) -> gType ) (taugType : ( fin ) -> gType ) (s : gType ) : subst_gType taugType (subst_gType sigmagType s) = subst_gType ((funcomp) (subst_gType taugType) sigmagType) s .
Proof. exact (compSubstSubst_gType sigmagType taugType (_) (fun n => Logic.eq_refl) s). Qed.

Lemma compComp'_gType    (sigmagType : ( fin ) -> gType ) (taugType : ( fin ) -> gType ) : (funcomp) (subst_gType taugType) (subst_gType sigmagType) = subst_gType ((funcomp) (subst_gType taugType) sigmagType) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => compComp_gType sigmagType taugType n)). Qed.

Lemma compRen_gType    (sigmagType : ( fin ) -> gType ) (zetagType : ( fin ) -> fin) (s : gType ) : ren_gType zetagType (subst_gType sigmagType s) = subst_gType ((funcomp) (ren_gType zetagType) sigmagType) s .
Proof. exact (compSubstRen_gType sigmagType zetagType (_) (fun n => Logic.eq_refl) s). Qed.

Lemma compRen'_gType    (sigmagType : ( fin ) -> gType ) (zetagType : ( fin ) -> fin) : (funcomp) (ren_gType zetagType) (subst_gType sigmagType) = subst_gType ((funcomp) (ren_gType zetagType) sigmagType) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => compRen_gType sigmagType zetagType n)). Qed.

Lemma renComp_gType    (xigType : ( fin ) -> fin) (taugType : ( fin ) -> gType ) (s : gType ) : subst_gType taugType (ren_gType xigType s) = subst_gType ((funcomp) taugType xigType) s .
Proof. exact (compRenSubst_gType xigType taugType (_) (fun n => Logic.eq_refl) s). Qed.

Lemma renComp'_gType    (xigType : ( fin ) -> fin) (taugType : ( fin ) -> gType ) : (funcomp) (subst_gType taugType) (ren_gType xigType) = subst_gType ((funcomp) taugType xigType) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => renComp_gType xigType taugType n)). Qed.

Lemma renRen_gType    (xigType : ( fin ) -> fin) (zetagType : ( fin ) -> fin) (s : gType ) : ren_gType zetagType (ren_gType xigType s) = ren_gType ((funcomp) zetagType xigType) s .
Proof. exact (compRenRen_gType xigType zetagType (_) (fun n => Logic.eq_refl) s). Qed.

Lemma renRen'_gType    (xigType : ( fin ) -> fin) (zetagType : ( fin ) -> fin) : (funcomp) (ren_gType zetagType) (ren_gType xigType) = ren_gType ((funcomp) zetagType xigType) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => renRen_gType xigType zetagType n)). Qed.

End gType.





















Global Instance Subst_lType   : Subst1 (( fin ) -> lType ) (lType ) (lType ) := @subst_lType   .

Global Instance Subst_gType   : Subst1 (( fin ) -> gType ) (gType ) (gType ) := @subst_gType   .

Global Instance Ren_lType   : Ren1 (( fin ) -> fin) (lType ) (lType ) := @ren_lType   .

Global Instance Ren_gType   : Ren1 (( fin ) -> fin) (gType ) (gType ) := @ren_gType   .

Global Instance VarInstance_lType  : Var (fin) (lType ) := @EVar  .

Notation "x '__lType'" := (EVar x) (at level 5, format "x __lType") : subst_scope.

Notation "x '__lType'" := (@ids (_) (_) VarInstance_lType x) (at level 5,  format "x __lType") : subst_scope.

Notation "'var'" := (EVar) ( at level 1) : subst_scope.

Global Instance VarInstance_gType  : Var (fin) (gType ) := @GVar  .

Notation "x '__gType'" := (GVar x) (at level 5, format "x __gType") : subst_scope.

Notation "x '__gType'" := (@ids (_) (_) VarInstance_gType x) (at level 5,  format "x __gType") : subst_scope.

Notation "'var'" := (GVar) ( at level 1) : subst_scope.

Class Up_lType X Y := up_lType : ( X ) -> Y.

Notation "↑__lType" := (up_lType)  : subst_scope.

Class Up_gType X Y := up_gType : ( X ) -> Y.

Notation "↑__gType" := (up_gType) : subst_scope.

Notation "↑__lType" := (up_lType_lType) : subst_scope.

Global Instance Up_lType_lType   : Up_lType (_) (_) := @up_lType_lType   .

Notation "↑__gType" := (up_gType_gType) : subst_scope.

Global Instance Up_gType_gType   : Up_gType (_) (_) := @up_gType_gType   .

Notation "s [e sigmalType ]" := (subst_lType sigmalType s) (at level 7, left associativity) : subst_scope.

Notation "[e sigmalType ]" := (subst_lType sigmalType) (at level 1, left associativity) : fscope.

Notation "s ⟨e xilType ⟩" := (ren_lType xilType s) (at level 7, left associativity) : subst_scope.

Notation "⟨e xilType ⟩" := (ren_lType xilType) (at level 1, left associativity) : fscope.

Notation "s [g sigmagType ]" := (subst_gType sigmagType s) (at level 7, left associativity) : subst_scope.

Notation "[g sigmagType ]" := (subst_gType sigmagType) (at level 1, left associativity) : fscope.

Notation "s ⟨g xigType ⟩" := (ren_gType xigType s) (at level 7, left associativity) : subst_scope.

Notation "⟨g xigType ⟩" := (ren_gType xigType) (at level 1, left associativity) : fscope.

Ltac auto_unfold := repeat unfold subst1,  subst2,  Subst1,  Subst2,  ids,  ren1,  ren2,  Ren1,  Ren2,  Subst_lType,  Subst_gType,  Ren_lType,  Ren_gType,  VarInstance_lType,  VarInstance_gType.

Tactic Notation "auto_unfold" "sin" "*" := repeat unfold subst1,  subst2,  Subst1,  Subst2,  ids,  ren1,  ren2,  Ren1,  Ren2,  Subst_lType,  Subst_gType,  Ren_lType,  Ren_gType,  VarInstance_lType,  VarInstance_gType in *.

Lemma comp_id : forall (A  B : Type) (f : A -> B), f >> ssrfun.id = f. 
Proof. intros. fext. done. 
Qed.

Ltac asimpl' := repeat first [progress rewrite ?instId_lType| progress rewrite ?compComp_lType| progress rewrite ?compComp'_lType| progress rewrite ?instId_gType| progress rewrite ?compComp_gType| progress rewrite ?compComp'_gType| progress rewrite ?rinstId_lType| progress rewrite ?compRen_lType| progress rewrite ?compRen'_lType| progress rewrite ?renComp_lType| progress rewrite ?renComp'_lType| progress rewrite ?renRen_lType| progress rewrite ?renRen'_lType| progress rewrite ?rinstId_gType| progress rewrite ?compRen_gType| progress rewrite ?compRen'_gType| progress rewrite ?renComp_gType| progress rewrite ?renComp'_gType| progress rewrite ?renRen_gType| progress rewrite ?renRen'_gType| progress rewrite ?varL_lType| progress rewrite ?varL_gType| progress rewrite ?varLRen_lType| progress rewrite ?varLRen_gType| progress (unfold up_ren, upRen_lType_lType, upRen_gType_gType, up_lType_lType, up_gType_gType)| progress (cbn [subst_lType subst_gType ren_lType ren_gType] ) | progress rewrite ?comp_id |  fsimpl].

Ltac asimpl := repeat try unfold_funcomp; auto_unfold sin *; asimpl'; repeat try unfold_funcomp.

Tactic Notation "asimpl" "sin" hyp(J) := revert J; asimpl; intros J.

Tactic Notation "auto_case" := auto_case (asimpl; cbn; eauto).

Ltac substify := auto_unfold; try repeat (erewrite rinstInst_lType); try repeat (erewrite rinstInst_gType).

Ltac renamify := auto_unfold; try repeat (erewrite <- rinstInst_lType); try repeat (erewrite <- rinstInst_gType).



From mathcomp Require Import finmap.

Open Scope fset_scope.
Open Scope fmap_scope.

Coercion ptcps_of_act (a : action) := ptcp_from a |` [fset ptcp_to a].

Definition label := (action * (value + nat))%type.

Coercion to_action (l : label) : action := l.1.


Canonical action_predType := PredType (fun a p => p \in ptcps_of_act a). 

Lemma ptcps_of_act_eq : forall a, ptcps_of_act a = [fset ptcp_from a; ptcp_to a].
Proof. done. Qed.

Lemma in_action_eq : forall p a, p \in ptcps_of_act a = (p == ptcp_from a) ||  (p == ptcp_to a).
Proof. intros. destruct a. by rewrite /= /ptcps_of_act !inE /=.  Qed.

(*Let inE := (inE,ptcps_of_act_eq,Bool.negb_involutive,eqxx,negb_or,negb_and).*)
