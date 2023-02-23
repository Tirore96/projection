Require Export Proj.unscoped.
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
  | VLT : endpoint -> ptcp  -> value  
 with mysort  : Set :=
  | SBool : mysort
  | SNat : mysort  
  | SGType : gType -> mysort (*maybe more sorts?*)
 with endpoint  : Set :=
  | EVar : nat -> endpoint  
  | EEnd : endpoint  
  | EMsg : dir -> ch -> value -> endpoint -> endpoint  
  | EBranch  : dir -> ch  -> seq endpoint -> endpoint  
  | ERec : endpoint -> endpoint . 
Set Elimination Schemes.

Section endpoint.


Lemma congr_EEnd  : EEnd  = EEnd  .
Proof. congruence. Qed.

Lemma congr_ERec  { s0 : endpoint   } { t0 : endpoint   } (H1 : s0 = t0) : ERec  s0 = ERec  t0 .
Proof. congruence. Qed.

Lemma congr_EMsg  { s0 : dir   } { s1 : ch   } { s2 : value   } { s3 : endpoint   } { t0 : dir   } { t1 : ch   } { t2 : value   } { t3 : endpoint   } (H1 : s0 = t0) (H2 : s1 = t1) (H3 : s2 = t2) (H4 : s3 = t3) : EMsg  s0 s1 s2 s3 = EMsg  t0 t1 t2 t3 .
Proof. congruence. Qed.

Lemma congr_EBranch  { s0 : dir   } { s1 : ch   } { s2 : list (endpoint  ) } { t0 : dir   } { t1 : ch   } { t2 : list (endpoint  ) } (H1 : s0 = t0) (H2 : s1 = t1) (H3 : s2 = t2) : EBranch  s0 s1 s2 = EBranch  t0 t1 t2 .
Proof. congruence. Qed.

Definition upRen_endpoint_endpoint   (xi : ( fin ) -> fin) : ( fin ) -> fin :=
  (up_ren) xi.

Fixpoint ren_endpoint   (xiendpoint : ( fin ) -> fin) (s : endpoint ) : endpoint  :=
    match s return endpoint  with
    | EVar  s => (EVar ) (xiendpoint s)
    | EEnd   => EEnd 
    | ERec  s0 => ERec  ((ren_endpoint (upRen_endpoint_endpoint xiendpoint)) s0)
    | EMsg  s0 s1 s2 s3 => EMsg  ((fun x => x) s0) ((fun x => x) s1) ((fun x => x) s2) ((ren_endpoint xiendpoint) s3)
    | EBranch  s0 s1 s2 => EBranch  ((fun x => x) s0) ((fun x => x) s1) ((map (ren_endpoint xiendpoint)) s2)
    end.

Definition up_endpoint_endpoint   (sigma : ( fin ) -> endpoint ) : ( fin ) -> endpoint  :=
  (scons) ((EVar ) (var_zero)) ((funcomp) (ren_endpoint (shift)) sigma).

Fixpoint subst_endpoint   (sigmaendpoint : ( fin ) -> endpoint ) (s : endpoint ) : endpoint  :=
    match s return endpoint  with
    | EVar  s => sigmaendpoint s
    | EEnd   => EEnd 
    | ERec  s0 => ERec  ((subst_endpoint (up_endpoint_endpoint sigmaendpoint)) s0)
    | EMsg  s0 s1 s2 s3 => EMsg  ((fun x => x) s0) ((fun x => x) s1) ((fun x => x) s2) ((subst_endpoint sigmaendpoint) s3)
    | EBranch  s0 s1 s2 => EBranch  ((fun x => x) s0) ((fun x => x) s1) ((map (subst_endpoint sigmaendpoint)) s2)
    end.




Definition upId_endpoint_endpoint  (sigma : ( fin ) -> endpoint ) (Eq : forall x, sigma x = (EVar ) x) : forall x, (up_endpoint_endpoint sigma) x = (EVar ) x :=
  fun n => match n with
  | S fin_n => (ap) (ren_endpoint (shift)) (Eq fin_n)
  | 0  => Logic.eq_refl
  end.


Fixpoint idSubst_endpoint  (sigmaendpoint : ( fin ) -> endpoint ) (Eqendpoint : forall x, sigmaendpoint x = (EVar ) x) (s : endpoint ) : subst_endpoint sigmaendpoint s = s :=
    match s return subst_endpoint sigmaendpoint s = s with
    | EVar  s => Eqendpoint s
    | EEnd   => congr_EEnd 
    | ERec  s0 => congr_ERec ((@idSubst_endpoint (up_endpoint_endpoint sigmaendpoint) (@upId_endpoint_endpoint (_) Eqendpoint)) s0)
    | EMsg  s0 s1 s2 s3 => congr_EMsg ((fun x => (Logic.eq_refl) x) s0) ((fun x => (Logic.eq_refl) x) s1) ((fun x => (Logic.eq_refl) x) s2) ((@idSubst_endpoint sigmaendpoint  Eqendpoint) s3)
    | EBranch  s0 s1 s2 => congr_EBranch ((fun x => (Logic.eq_refl) x) s0) ((fun x => (Logic.eq_refl) x) s1) ((list_id (@idSubst_endpoint sigmaendpoint Eqendpoint)) s2)
    end.



Definition upExtRen_endpoint_endpoint   (xi : ( fin ) -> fin) (zeta : ( fin ) -> fin) (Eq : forall x, xi x = zeta x) : forall x, (upRen_endpoint_endpoint xi) x = (upRen_endpoint_endpoint zeta) x :=
  fun n => match n with
  | S fin_n => (ap) (shift) (Eq fin_n)
  | 0  => Logic.eq_refl
  end.


Fixpoint extRen_endpoint   (xiendpoint : ( fin ) -> fin) (zetaendpoint : ( fin ) -> fin) (Eqendpoint : forall x, xiendpoint x = zetaendpoint x) (s : endpoint ) : ren_endpoint xiendpoint s = ren_endpoint zetaendpoint s :=
    match s return ren_endpoint xiendpoint s = ren_endpoint zetaendpoint s with
    | EVar  s => (ap) (EVar ) (Eqendpoint s)
    | EEnd   => congr_EEnd 
    | ERec  s0 => congr_ERec ((@extRen_endpoint (upRen_endpoint_endpoint xiendpoint) (upRen_endpoint_endpoint zetaendpoint) (@upExtRen_endpoint_endpoint (_) (_) Eqendpoint)) s0)
    | EMsg  s0 s1 s2 s3 => congr_EMsg ((fun x => (Logic.eq_refl) x) s0) ((fun x => (Logic.eq_refl) x) s1) ((fun x => (Logic.eq_refl) x) s2) ((@extRen_endpoint xiendpoint zetaendpoint Eqendpoint) s3)
    | EBranch  s0 s1 s2 => congr_EBranch ((fun x => (Logic.eq_refl) x) s0) ((fun x => (Logic.eq_refl) x) s1) ((list_ext (@extRen_endpoint xiendpoint zetaendpoint Eqendpoint)) s2)
    end.

Definition upExt_endpoint_endpoint   (sigma : ( fin ) -> endpoint ) (tau : ( fin ) -> endpoint ) (Eq : forall x, sigma x = tau x) : forall x, (up_endpoint_endpoint sigma) x = (up_endpoint_endpoint tau) x :=
  fun n => match n with
  | S fin_n => (ap) (ren_endpoint (shift)) (Eq fin_n)
  | 0  => Logic.eq_refl
  end.

Fixpoint ext_endpoint   (sigmaendpoint : ( fin ) -> endpoint ) (tauendpoint : ( fin ) -> endpoint ) (Eqendpoint : forall x, sigmaendpoint x = tauendpoint x) (s : endpoint ) : subst_endpoint sigmaendpoint s = subst_endpoint tauendpoint s :=
    match s return subst_endpoint sigmaendpoint s = subst_endpoint tauendpoint s with
    | EVar  s => Eqendpoint s
    | EEnd   => congr_EEnd 
    | ERec  s0 => congr_ERec ((ext_endpoint (up_endpoint_endpoint sigmaendpoint) (up_endpoint_endpoint tauendpoint) (upExt_endpoint_endpoint (_) (_) Eqendpoint)) s0)
    | EMsg  s0 s1 s2 s3 => congr_EMsg ((fun x => (Logic.eq_refl) x) s0) ((fun x => (Logic.eq_refl) x) s1) ((fun x => (Logic.eq_refl) x) s2) ((ext_endpoint sigmaendpoint tauendpoint Eqendpoint) s3)
    | EBranch  s0 s1 s2 => congr_EBranch ((fun x => (Logic.eq_refl) x) s0) ((fun x => (Logic.eq_refl) x) s1) ((list_ext (ext_endpoint sigmaendpoint tauendpoint Eqendpoint)) s2)
    end.

Definition up_ren_ren_endpoint_endpoint    (xi : ( fin ) -> fin) (tau : ( fin ) -> fin) (theta : ( fin ) -> fin) (Eq : forall x, ((funcomp) tau xi) x = theta x) : forall x, ((funcomp) (upRen_endpoint_endpoint tau) (upRen_endpoint_endpoint xi)) x = (upRen_endpoint_endpoint theta) x :=
  up_ren_ren xi tau theta Eq.

Fixpoint compRenRen_endpoint    (xiendpoint : ( fin ) -> fin) (zetaendpoint : ( fin ) -> fin) (rhoendpoint : ( fin ) -> fin) (Eqendpoint : forall x, ((funcomp) zetaendpoint xiendpoint) x = rhoendpoint x) (s : endpoint ) : ren_endpoint zetaendpoint (ren_endpoint xiendpoint s) = ren_endpoint rhoendpoint s :=
    match s return ren_endpoint zetaendpoint (ren_endpoint xiendpoint s) = ren_endpoint rhoendpoint s with
    | EVar  s => (ap) (EVar ) (Eqendpoint s)
    | EEnd   => congr_EEnd 
    | ERec  s0 => congr_ERec ((compRenRen_endpoint (upRen_endpoint_endpoint xiendpoint) (upRen_endpoint_endpoint zetaendpoint) (upRen_endpoint_endpoint rhoendpoint) (up_ren_ren (_) (_) (_) Eqendpoint)) s0)
    | EMsg  s0 s1 s2 s3 => congr_EMsg ((fun x => (Logic.eq_refl) x) s0) ((fun x => (Logic.eq_refl) x) s1) ((fun x => (Logic.eq_refl) x) s2) ((compRenRen_endpoint xiendpoint zetaendpoint rhoendpoint Eqendpoint) s3)
    | EBranch  s0 s1 s2 => congr_EBranch ((fun x => (Logic.eq_refl) x) s0) ((fun x => (Logic.eq_refl) x) s1) ((list_comp (compRenRen_endpoint xiendpoint zetaendpoint rhoendpoint Eqendpoint)) s2)
    end.

Definition up_ren_subst_endpoint_endpoint    (xi : ( fin ) -> fin) (tau : ( fin ) -> endpoint ) (theta : ( fin ) -> endpoint ) (Eq : forall x, ((funcomp) tau xi) x = theta x) : forall x, ((funcomp) (up_endpoint_endpoint tau) (upRen_endpoint_endpoint xi)) x = (up_endpoint_endpoint theta) x :=
  fun n => match n with
  | S fin_n => (ap) (ren_endpoint (shift)) (Eq fin_n)
  | 0  => Logic.eq_refl
  end.

Fixpoint compRenSubst_endpoint    (xiendpoint : ( fin ) -> fin) (tauendpoint : ( fin ) -> endpoint ) (thetaendpoint : ( fin ) -> endpoint ) (Eqendpoint : forall x, ((funcomp) tauendpoint xiendpoint) x = thetaendpoint x) (s : endpoint ) : subst_endpoint tauendpoint (ren_endpoint xiendpoint s) = subst_endpoint thetaendpoint s :=
    match s return subst_endpoint tauendpoint (ren_endpoint xiendpoint s) = subst_endpoint thetaendpoint s with
    | EVar  s => Eqendpoint s
    | EEnd   => congr_EEnd 
    | ERec  s0 => congr_ERec ((compRenSubst_endpoint (upRen_endpoint_endpoint xiendpoint) (up_endpoint_endpoint tauendpoint) (up_endpoint_endpoint thetaendpoint) (up_ren_subst_endpoint_endpoint (_) (_) (_) Eqendpoint)) s0)
    | EMsg  s0 s1 s2 s3 => congr_EMsg ((fun x => (Logic.eq_refl) x) s0) ((fun x => (Logic.eq_refl) x) s1) ((fun x => (Logic.eq_refl) x) s2) ((compRenSubst_endpoint xiendpoint tauendpoint thetaendpoint Eqendpoint) s3)
    | EBranch  s0 s1 s2 => congr_EBranch ((fun x => (Logic.eq_refl) x) s0) ((fun x => (Logic.eq_refl) x) s1) ((list_comp (compRenSubst_endpoint xiendpoint tauendpoint thetaendpoint Eqendpoint)) s2)
    end.


(*Definition up_subst_ren_gType_gType    (sigma : ( fin ) -> gType ) (zetagType : ( fin ) -> fin) (theta : ( fin ) -> gType ) (Eq : forall x, ((funcomp) (ren_gType zetagType) sigma) x = theta x) : forall x, ((funcomp) (ren_gType (upRen_gType_gType zetagType)) (up_gType_gType sigma)) x = (up_gType_gType theta) x :=
  fun n => match n with
  | S fin_n => (eq_trans) (compRenRen_gType (shift) (upRen_gType_gType zetagType) ((funcomp) (shift) zetagType) (fun x => Logic.eq_refl) (sigma fin_n)) 
               ((eq_trans) ((eq_sym) (compRenRen_gType zetagType (shift) ((funcomp) (shift) zetagType) (fun x => Logic.eq_refl) (sigma fin_n))) 
                           ((ap) (ren_gType (shift)) (Eq fin_n)))
  | 0  => Logic.eq_refl
  end.
*)
Check compRenRen_endpoint. Check Logic.eq_sym. Check eq_sym.
Definition up_subst_ren_endpoint_endpoint    (sigma : ( fin ) -> endpoint ) (zetaendpoint : ( fin ) -> fin) (theta : ( fin ) -> endpoint ) (Eq : forall x, ((funcomp) (ren_endpoint zetaendpoint) sigma) x = theta x) : 
forall x, ((funcomp) (ren_endpoint (upRen_endpoint_endpoint zetaendpoint)) (up_endpoint_endpoint sigma)) x = (up_endpoint_endpoint theta) x :=
  fun n => match n with
  | S fin_n => (eq_trans) (compRenRen_endpoint (shift) (upRen_endpoint_endpoint zetaendpoint) ((funcomp) (shift) zetaendpoint) (fun x => Logic.eq_refl) (sigma fin_n)) 
              ((eq_trans) ((Logic.eq_sym) (compRenRen_endpoint zetaendpoint (shift) ((funcomp) (shift) zetaendpoint) (fun x => Logic.eq_refl) (sigma fin_n))) 
                          ((ap) (ren_endpoint (shift)) (Eq fin_n)))
  | 0  => Logic.eq_refl
  end.

Fixpoint compSubstRen_endpoint    (sigmaendpoint : ( fin ) -> endpoint ) (zetaendpoint : ( fin ) -> fin) (thetaendpoint : ( fin ) -> endpoint ) (Eqendpoint : forall x, ((funcomp) (ren_endpoint zetaendpoint) sigmaendpoint) x = thetaendpoint x) (s : endpoint ) : ren_endpoint zetaendpoint (subst_endpoint sigmaendpoint s) = subst_endpoint thetaendpoint s :=
    match s return ren_endpoint zetaendpoint (subst_endpoint sigmaendpoint s) = subst_endpoint thetaendpoint s with
    | EVar  s => Eqendpoint s
    | EEnd   => congr_EEnd 
    | ERec  s0 => congr_ERec ((compSubstRen_endpoint (up_endpoint_endpoint sigmaendpoint) (upRen_endpoint_endpoint zetaendpoint) (up_endpoint_endpoint thetaendpoint) (up_subst_ren_endpoint_endpoint (_) (_) (_) Eqendpoint)) s0)
    | EMsg  s0 s1 s2 s3 => congr_EMsg ((fun x => (Logic.eq_refl) x) s0) ((fun x => (Logic.eq_refl) x) s1) ((fun x => (Logic.eq_refl) x) s2) ((compSubstRen_endpoint sigmaendpoint zetaendpoint thetaendpoint Eqendpoint) s3)
    | EBranch  s0 s1 s2 => congr_EBranch ((fun x => (Logic.eq_refl) x) s0) ((fun x => (Logic.eq_refl) x) s1) ((list_comp (compSubstRen_endpoint sigmaendpoint zetaendpoint thetaendpoint Eqendpoint)) s2)
    end.

Definition up_subst_subst_endpoint_endpoint    (sigma : ( fin ) -> endpoint ) (tauendpoint : ( fin ) -> endpoint ) (theta : ( fin ) -> endpoint ) (Eq : forall x, ((funcomp) (subst_endpoint tauendpoint) sigma) x = theta x) : forall x, ((funcomp) (subst_endpoint (up_endpoint_endpoint tauendpoint)) (up_endpoint_endpoint sigma)) x = (up_endpoint_endpoint theta) x :=
  fun n => match n with
  | S fin_n => (eq_trans) (compRenSubst_endpoint (shift) (up_endpoint_endpoint tauendpoint) ((funcomp) (up_endpoint_endpoint tauendpoint) (shift)) (fun x => Logic.eq_refl) (sigma fin_n)) ((eq_trans) ((Logic.eq_sym) (compSubstRen_endpoint tauendpoint (shift) ((funcomp) (ren_endpoint (shift)) tauendpoint) (fun x => Logic.eq_refl) (sigma fin_n))) ((ap) (ren_endpoint (shift)) (Eq fin_n)))
  | 0  => Logic.eq_refl
  end.

Fixpoint compSubstSubst_endpoint    (sigmaendpoint : ( fin ) -> endpoint ) (tauendpoint : ( fin ) -> endpoint ) (thetaendpoint : ( fin ) -> endpoint ) (Eqendpoint : forall x, ((funcomp) (subst_endpoint tauendpoint) sigmaendpoint) x = thetaendpoint x) (s : endpoint ) : subst_endpoint tauendpoint (subst_endpoint sigmaendpoint s) = subst_endpoint thetaendpoint s :=
    match s return subst_endpoint tauendpoint (subst_endpoint sigmaendpoint s) = subst_endpoint thetaendpoint s with
    | EVar  s => Eqendpoint s
    | EEnd   => congr_EEnd 
    | ERec  s0 => congr_ERec ((compSubstSubst_endpoint (up_endpoint_endpoint sigmaendpoint) (up_endpoint_endpoint tauendpoint) (up_endpoint_endpoint thetaendpoint) (up_subst_subst_endpoint_endpoint (_) (_) (_) Eqendpoint)) s0)
    | EMsg  s0 s1 s2 s3 => congr_EMsg ((fun x => (Logic.eq_refl) x) s0) ((fun x => (Logic.eq_refl) x) s1) ((fun x => (Logic.eq_refl) x) s2) ((compSubstSubst_endpoint sigmaendpoint tauendpoint thetaendpoint Eqendpoint) s3)
    | EBranch  s0 s1 s2 => congr_EBranch ((fun x => (Logic.eq_refl) x) s0) ((fun x => (Logic.eq_refl) x) s1) ((list_comp (compSubstSubst_endpoint sigmaendpoint tauendpoint thetaendpoint Eqendpoint)) s2)
    end.

Definition rinstInst_up_endpoint_endpoint   (xi : ( fin ) -> fin) (sigma : ( fin ) -> endpoint ) (Eq : forall x, ((funcomp) (EVar ) xi) x = sigma x) : forall x, ((funcomp) (EVar ) (upRen_endpoint_endpoint xi)) x = (up_endpoint_endpoint sigma) x :=
  fun n => match n with
  | S fin_n => (ap) (ren_endpoint (shift)) (Eq fin_n)
  | 0  => Logic.eq_refl
  end.

Fixpoint rinst_inst_endpoint   (xiendpoint : ( fin ) -> fin) (sigmaendpoint : ( fin ) -> endpoint ) (Eqendpoint : forall x, ((funcomp) (EVar ) xiendpoint) x = sigmaendpoint x) (s : endpoint ) : ren_endpoint xiendpoint s = subst_endpoint sigmaendpoint s :=
    match s return ren_endpoint xiendpoint s = subst_endpoint sigmaendpoint s with
    | EVar  s => Eqendpoint s
    | EEnd   => congr_EEnd 
    | ERec  s0 => congr_ERec ((rinst_inst_endpoint (upRen_endpoint_endpoint xiendpoint) (up_endpoint_endpoint sigmaendpoint) (rinstInst_up_endpoint_endpoint (_) (_) Eqendpoint)) s0)
    | EMsg  s0 s1 s2 s3 => congr_EMsg ((fun x => (Logic.eq_refl) x) s0) ((fun x => (Logic.eq_refl) x) s1) ((fun x => (Logic.eq_refl) x) s2) ((rinst_inst_endpoint xiendpoint sigmaendpoint Eqendpoint) s3)
    | EBranch  s0 s1 s2 => congr_EBranch ((fun x => (Logic.eq_refl) x) s0) ((fun x => (Logic.eq_refl) x) s1) ((list_ext (rinst_inst_endpoint xiendpoint sigmaendpoint Eqendpoint)) s2)
    end.

Lemma rinstInst_endpoint   (xiendpoint : ( fin ) -> fin) : ren_endpoint xiendpoint = subst_endpoint ((funcomp) (EVar ) xiendpoint) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => rinst_inst_endpoint xiendpoint (_) (fun n => Logic.eq_refl) x)). Qed.

Lemma instId_endpoint  : subst_endpoint (EVar ) = id .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => idSubst_endpoint (EVar ) (fun n => Logic.eq_refl) ((id) x))). Qed.

Lemma rinstId_endpoint  : @ren_endpoint   (id) = id .
Proof. exact ((eq_trans) (rinstInst_endpoint ((id) (_))) instId_endpoint). Qed.

Lemma varL_endpoint   (sigmaendpoint : ( fin ) -> endpoint ) : (funcomp) (subst_endpoint sigmaendpoint) (EVar ) = sigmaendpoint .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => Logic.eq_refl)). Qed.

Lemma varLRen_endpoint   (xiendpoint : ( fin ) -> fin) : (funcomp) (ren_endpoint xiendpoint) (EVar ) = (funcomp) (EVar ) xiendpoint .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => Logic.eq_refl)). Qed.

Lemma compComp_endpoint    (sigmaendpoint : ( fin ) -> endpoint ) (tauendpoint : ( fin ) -> endpoint ) (s : endpoint ) : subst_endpoint tauendpoint (subst_endpoint sigmaendpoint s) = subst_endpoint ((funcomp) (subst_endpoint tauendpoint) sigmaendpoint) s .
Proof. exact (compSubstSubst_endpoint sigmaendpoint tauendpoint (_) (fun n => Logic.eq_refl) s). Qed.

Lemma compComp'_endpoint    (sigmaendpoint : ( fin ) -> endpoint ) (tauendpoint : ( fin ) -> endpoint ) : (funcomp) (subst_endpoint tauendpoint) (subst_endpoint sigmaendpoint) = subst_endpoint ((funcomp) (subst_endpoint tauendpoint) sigmaendpoint) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => compComp_endpoint sigmaendpoint tauendpoint n)). Qed.

Lemma compRen_endpoint    (sigmaendpoint : ( fin ) -> endpoint ) (zetaendpoint : ( fin ) -> fin) (s : endpoint ) : ren_endpoint zetaendpoint (subst_endpoint sigmaendpoint s) = subst_endpoint ((funcomp) (ren_endpoint zetaendpoint) sigmaendpoint) s .
Proof. exact (compSubstRen_endpoint sigmaendpoint zetaendpoint (_) (fun n => Logic.eq_refl) s). Qed.

Lemma compRen'_endpoint    (sigmaendpoint : ( fin ) -> endpoint ) (zetaendpoint : ( fin ) -> fin) : (funcomp) (ren_endpoint zetaendpoint) (subst_endpoint sigmaendpoint) = subst_endpoint ((funcomp) (ren_endpoint zetaendpoint) sigmaendpoint) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => compRen_endpoint sigmaendpoint zetaendpoint n)). Qed.

Lemma renComp_endpoint    (xiendpoint : ( fin ) -> fin) (tauendpoint : ( fin ) -> endpoint ) (s : endpoint ) : subst_endpoint tauendpoint (ren_endpoint xiendpoint s) = subst_endpoint ((funcomp) tauendpoint xiendpoint) s .
Proof. exact (compRenSubst_endpoint xiendpoint tauendpoint (_) (fun n => Logic.eq_refl) s). Qed.

Lemma renComp'_endpoint    (xiendpoint : ( fin ) -> fin) (tauendpoint : ( fin ) -> endpoint ) : (funcomp) (subst_endpoint tauendpoint) (ren_endpoint xiendpoint) = subst_endpoint ((funcomp) tauendpoint xiendpoint) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => renComp_endpoint xiendpoint tauendpoint n)). Qed.

Lemma renRen_endpoint    (xiendpoint : ( fin ) -> fin) (zetaendpoint : ( fin ) -> fin) (s : endpoint ) : ren_endpoint zetaendpoint (ren_endpoint xiendpoint s) = ren_endpoint ((funcomp) zetaendpoint xiendpoint) s .
Proof. exact (compRenRen_endpoint xiendpoint zetaendpoint (_) (fun n => Logic.eq_refl) s). Qed.

Lemma renRen'_endpoint    (xiendpoint : ( fin ) -> fin) (zetaendpoint : ( fin ) -> fin) : (funcomp) (ren_endpoint zetaendpoint) (ren_endpoint xiendpoint) = ren_endpoint ((funcomp) zetaendpoint xiendpoint) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => renRen_endpoint xiendpoint zetaendpoint n)). Qed.

End endpoint.


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





















Global Instance Subst_endpoint   : Subst1 (( fin ) -> endpoint ) (endpoint ) (endpoint ) := @subst_endpoint   .

Global Instance Subst_gType   : Subst1 (( fin ) -> gType ) (gType ) (gType ) := @subst_gType   .

Global Instance Ren_endpoint   : Ren1 (( fin ) -> fin) (endpoint ) (endpoint ) := @ren_endpoint   .

Global Instance Ren_gType   : Ren1 (( fin ) -> fin) (gType ) (gType ) := @ren_gType   .

Global Instance VarInstance_endpoint  : Var (fin) (endpoint ) := @EVar  .

Notation "x '__endpoint'" := (EVar x) (at level 5, format "x __endpoint") : subst_scope.

Notation "x '__endpoint'" := (@ids (_) (_) VarInstance_endpoint x) (at level 5,  format "x __endpoint") : subst_scope.

Notation "'var'" := (EVar) ( at level 1) : subst_scope.

Global Instance VarInstance_gType  : Var (fin) (gType ) := @GVar  .

Notation "x '__gType'" := (GVar x) (at level 5, format "x __gType") : subst_scope.

Notation "x '__gType'" := (@ids (_) (_) VarInstance_gType x) (at level 5,  format "x __gType") : subst_scope.

Notation "'var'" := (GVar) ( at level 1) : subst_scope.

Class Up_endpoint X Y := up_endpoint : ( X ) -> Y.

Notation "↑__endpoint" := (up_endpoint)  : subst_scope.

Class Up_gType X Y := up_gType : ( X ) -> Y.

Notation "↑__gType" := (up_gType) : subst_scope.

Notation "↑__endpoint" := (up_endpoint_endpoint) : subst_scope.

Global Instance Up_endpoint_endpoint   : Up_endpoint (_) (_) := @up_endpoint_endpoint   .

Notation "↑__gType" := (up_gType_gType) : subst_scope.

Global Instance Up_gType_gType   : Up_gType (_) (_) := @up_gType_gType   .

Notation "s [e sigmaendpoint ]" := (subst_endpoint sigmaendpoint s) (at level 7, left associativity) : subst_scope.

Notation "[e sigmaendpoint ]" := (subst_endpoint sigmaendpoint) (at level 1, left associativity) : fscope.

Notation "s ⟨e xiendpoint ⟩" := (ren_endpoint xiendpoint s) (at level 7, left associativity) : subst_scope.

Notation "⟨e xiendpoint ⟩" := (ren_endpoint xiendpoint) (at level 1, left associativity) : fscope.

Notation "s [g sigmagType ]" := (subst_gType sigmagType s) (at level 7, left associativity) : subst_scope.

Notation "[g sigmagType ]" := (subst_gType sigmagType) (at level 1, left associativity) : fscope.

Notation "s ⟨g xigType ⟩" := (ren_gType xigType s) (at level 7, left associativity) : subst_scope.

Notation "⟨g xigType ⟩" := (ren_gType xigType) (at level 1, left associativity) : fscope.

Ltac auto_unfold := repeat unfold subst1,  subst2,  Subst1,  Subst2,  ids,  ren1,  ren2,  Ren1,  Ren2,  Subst_endpoint,  Subst_gType,  Ren_endpoint,  Ren_gType,  VarInstance_endpoint,  VarInstance_gType.

Tactic Notation "auto_unfold" "sin" "*" := repeat unfold subst1,  subst2,  Subst1,  Subst2,  ids,  ren1,  ren2,  Ren1,  Ren2,  Subst_endpoint,  Subst_gType,  Ren_endpoint,  Ren_gType,  VarInstance_endpoint,  VarInstance_gType in *.

Lemma comp_id : forall (A  B : Type) (f : A -> B), f >> ssrfun.id = f. 
Proof. intros. fext. done. 
Qed.

Ltac asimpl' := repeat first [progress rewrite ?instId_endpoint| progress rewrite ?compComp_endpoint| progress rewrite ?compComp'_endpoint| progress rewrite ?instId_gType| progress rewrite ?compComp_gType| progress rewrite ?compComp'_gType| progress rewrite ?rinstId_endpoint| progress rewrite ?compRen_endpoint| progress rewrite ?compRen'_endpoint| progress rewrite ?renComp_endpoint| progress rewrite ?renComp'_endpoint| progress rewrite ?renRen_endpoint| progress rewrite ?renRen'_endpoint| progress rewrite ?rinstId_gType| progress rewrite ?compRen_gType| progress rewrite ?compRen'_gType| progress rewrite ?renComp_gType| progress rewrite ?renComp'_gType| progress rewrite ?renRen_gType| progress rewrite ?renRen'_gType| progress rewrite ?varL_endpoint| progress rewrite ?varL_gType| progress rewrite ?varLRen_endpoint| progress rewrite ?varLRen_gType| progress (unfold up_ren, upRen_endpoint_endpoint, upRen_gType_gType, up_endpoint_endpoint, up_gType_gType)| progress (cbn [subst_endpoint subst_gType ren_endpoint ren_gType] ) | progress rewrite ?comp_id |  fsimpl].

Ltac asimpl := repeat try unfold_funcomp; auto_unfold sin *; asimpl'; repeat try unfold_funcomp.

Tactic Notation "asimpl" "sin" hyp(J) := revert J; asimpl; intros J.

Tactic Notation "auto_case" := auto_case (asimpl; cbn; eauto).

(*Tactic Notation "asimpl" "sin" "*" := auto_unfold sin *; 
repeat first [
progress rewrite ?instId_endpoint in *| 
progress rewrite ?compComp_endpoint in *| 
progress rewrite ?compComp'_endpoint in *| 
progress rewrite ?instId_gType in *| 
progress rewrite ?compComp_gType in *| 
progress rewrite ?compComp'_gType in *| 
progress rewrite ?rinstId_endpoint in *| 
progress rewrite ?compRen_endpoint in *| 
progress rewrite ?compRen'_endpoint in *| 
progress rewrite ?renComp_endpoint in *| 
progress rewrite ?renComp'_endpoint in *| 
progress rewrite ?renRen_endpoint in *| 
progress rewrite ?renRen'_endpoint in *| 
progress rewrite ?rinstId_gType in *| 
progress rewrite ?compRen_gType in *| 
progress rewrite ?compRen'_gType in *| 
progress rewrite ?renComp_gType in *| 
progress rewrite ?renComp'_gType in *| 
progress rewrite ?renRen_gType in *| 
progress rewrite ?renRen'_gType in *| 
progress rewrite ?varL_endpoint in *| 
progress rewrite ?varL_gType in *| 
progress rewrite ?varLRen_endpoint in *| 
progress rewrite ?varLRen_gType in *| progress (unfold up_ren, upRen_endpoint_endpoint, upRen_gType_gType, up_endpoint_endpoint, up_gType_gType in *)

(*  | progress (cbn [subst_endpoint subst_gType ren_endpoint ren_gType] in *)(*| fsimpl in *].
*)


Ltac substify := auto_unfold; try repeat (erewrite rinstInst_endpoint); try repeat (erewrite rinstInst_gType).

Ltac renamify := auto_unfold; try repeat (erewrite <- rinstInst_endpoint); try repeat (erewrite <- rinstInst_gType).



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

Let inE := (inE,ptcps_of_act_eq,Bool.negb_involutive,eqxx,negb_or,negb_and).

Definition fset_ptcp := {fset ptcp}.


Fixpoint ptcps (g : gType) : {fset ptcp} := 
match g with 
| GMsg a _ g0 => a `|`(ptcps g0)
| GBranch a gs => a `|` \bigcup_( i <- map ptcps gs) i
| GRec g0 => ptcps g0
| _ => fset0
end.

Canonical gType_predType := PredType (fun g p => p \in ptcps g). 



Fixpoint gType_fv (g : gType) :=
match g with
| GVar j => [fset j]
| GEnd => fset0
| GMsg _ _ g0 => gType_fv g0
| GBranch _ gs => \bigcup_( i <- map gType_fv gs) i 
| GRec g0 => [fset[tt]  n.-1 | n in (gType_fv g0) & n != 0]
end. 

(*Definition bound g := gType_fv g == fset0.*)

Fixpoint endpoint_fv (e : endpoint) :=
match e with
| EVar j => [fset j]
| EEnd => fset0
| EMsg _ _ _ g0 => endpoint_fv g0
| EBranch _ _ gs => \bigcup_( i <- map endpoint_fv gs) i 
| ERec g0 => [fset[tt] n.-1 | n in (endpoint_fv g0) & n != 0 ]
end.

(*Definition ebound e := endpoint_fv e == fset0. *)



Fixpoint mu_height g :=
match g with
| GRec g0 => (mu_height g0).+1
| _ => 0
end.

Fixpoint emu_height g :=
match g with
| ERec g0 => (emu_height g0).+1
| _ => 0
end.

Fixpoint action_pred g :=
match g with 
| GMsg a u g0 => (~~ (ptcp_from a == ptcp_to a)) && action_pred g0
| GBranch a gs => (~~ (ptcp_from a == ptcp_to a)) && all action_pred gs
| GRec g0 => action_pred g0
| _ => true 
end.


Fixpoint size_pred (g : gType) :=
match g with 
| GMsg a u g0 => size_pred g0
| GBranch a gs => (0 < size gs) && all size_pred gs
| GRec g0 => size_pred g0
| _ => true
end.

Fixpoint esize_pred (g : endpoint) :=
match g with 
| EMsg _ _ _ e0 => esize_pred e0
| EBranch _ _ es => (0 < size es) && all esize_pred es
| ERec g0 => esize_pred g0
| _ => true
end.

Fixpoint guarded i g := 
match g with
| GVar j => j != i
| GEnd => true
| GMsg _ _ g0 => true
| GBranch _ gs => true
| GRec g0 => guarded i.+1 g0
end. 

Fixpoint eguarded i g := 
match g with
| EVar j => j != i
| EEnd => true
| EMsg _ _ _ g0 => true
| EBranch _ _ gs => true
| ERec g0 => eguarded i.+1 g0
end. 

Fixpoint contractive2 g := 
match g with
| GVar j => true
| GEnd => true
| GMsg _ _ g0 => contractive2 g0
| GBranch  _ gs => all contractive2 gs
| GRec g0 => (guarded 0 g0) && (contractive2 g0)
end. 

Fixpoint econtractive2 g := 
match g with
| EVar j => true
| EEnd => true
| EMsg _ _ _ g0 => econtractive2 g0
| EBranch _ _ gs => all econtractive2 gs
| ERec g0 => (eguarded 0 g0) && (econtractive2 g0)
end. 


Fixpoint bound_i (i : nat) g  := 
match g with 
| GEnd => true
| GMsg _ _ g0 => bound_i i g0
| GBranch _ gs => all (bound_i i) gs
| GRec g0 => bound_i (S i) g0
| GVar n => n < i
end.

Fixpoint ebound_i (i : nat) g  := 
match g with 
| EEnd => true
| EMsg _ _ _ g0 => ebound_i i g0
| EBranch _ _ gs => all (ebound_i i) gs
| ERec g0 => ebound_i (S i) g0
| EVar n => n < i
end.


Fixpoint substitution (i : nat) g g'  := 
match g with 
| GEnd => GEnd
| GMsg a u g0 => GMsg a u (substitution i g0 g')
| GBranch a gs => GBranch a (map (fun g => substitution i g g) gs)
| GRec g0 => GRec (substitution i.+1 g0 g') 
| GVar n => if n == i then g' else g
end.


Open Scope nat_scope.
Fixpoint gsize e := 
match e with 
| GMsg  _ _ e0 => (gsize e0).+1
| GBranch _ es => foldr (fun e0 acc => (gsize e0) + acc ) 2 es
(*| GRec  e0 =>  (gsize e0).+1*)
| GRec  e0 =>  (gsize e0) +  (gsize e0)
| _ => 1
end.




Fixpoint esize e := 
match e with 
| EMsg _  _ _ e0 => (esize e0).+1
| EBranch _ _ es => foldr (fun e0 acc => (esize e0) + acc ) 2 es
| ERec  e0 => (esize e0).+1
| _ => 1
end.


Lemma inject2 : forall sigma, injective sigma ->  injective (0 .: sigma >> succn).
Proof. 
intros. intro. intros. destruct x1;destruct x2;try done. inversion H0. f_equal. apply/H. done. 
Qed.


Lemma injective_shift : injective S.
Proof. intro. intros. inversion H.  done. Qed.

Lemma inject_comp : forall (A B C : Type) (sigma : A -> B) (sigma' : B -> C) , injective sigma -> injective sigma' -> injective (sigma >> sigma').  
Proof. 
intros. rewrite /funcomp. intro. intros. apply H. apply H0. done.
Qed.



Hint Resolve inject2 injective_shift.

Definition comp_dir p a :=  if p == (ptcp_from a) then Some Sd else if p == (ptcp_to a) then Some Rd else None.
Ltac comp_disc  :=  solve [ destruct (comp_dir _ _);done].
