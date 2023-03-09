From mathcomp Require Import all_ssreflect zify.
Require Export Proj.Utils.
From IndTypes Require Export Syntax. 
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(*It is hard to give a mutually inductive nested induction principle*)
(*
Scheme gType_ind := Induction for gType Sort Prop 
with value_ind := Induction for value Sort Prop 
with mysort_ind := Induction for mysort Sort Prop 
with endpoint_ind := Induction for endpoint Sort Prop.
Check gType_ind.
Combined Scheme gvme_ind from gType_ind,value_ind,mysort_ind,endpoint_ind.
*)



Section Elimination.

Variables (Pg : gType -> Type) 
          (Pv : value -> Type) 
          (Pe : endpoint -> Type) 
          (Pm : mysort -> Type)
          (P_glist : seq gType -> Type)
          (P_elist : seq endpoint -> Type)
          (P_mlist : seq mysort -> Type).

Hypothesis Pg_var : (forall n : nat, Pg (GVar n)).
Hypothesis Pg_end : Pg GEnd.
Hypothesis Pg_rec : (forall g : gType, Pg g -> Pg (GRec g)).
Hypothesis Pg_msg : (forall (a : action) (v : value), Pv v -> forall g : gType, Pg g -> Pg (GMsg a v g)).
Hypothesis Pg_branch : (forall (a : action) (l : seq gType), P_glist l  -> Pg (GBranch a l)).

Hypothesis Pv_vst : forall l : seq mysort, P_mlist l -> Pv (VSeqSort l).
Hypothesis Pv_vlt : forall e, Pe e -> forall p, Pv (VLT e p).

Hypothesis Pm_bool : Pm SBool.
Hypothesis Pm_nat : Pm SNat.
Hypothesis Pm_sgtype : forall g : gType, Pg g -> Pm (SGType g).

Hypothesis Pe_var : forall n : nat, Pe (EVar n). 
Hypothesis Pe_end : Pe EEnd. 
Hypothesis Pe_msg : forall (d : dir) (c : ch) (s : value), Pv s -> forall e : endpoint, Pe e -> Pe (EMsg d c s e).
Hypothesis Pe_branch : forall (d : dir) (c : ch) (l : seq endpoint), P_elist l  -> Pe (EBranch d c l).
Hypothesis Pe_rec : forall e : endpoint, Pe e -> Pe (ERec e).

Hypothesis P_glist_0 : P_glist nil.
Hypothesis P_glist_cons : forall g, Pg g -> forall l, P_glist l -> P_glist (g::l).

Hypothesis P_elist_0 : P_elist nil.
Hypothesis P_elist_cons : forall e, Pe e -> forall l, P_elist l -> P_elist (e::l).

Hypothesis P_mlist_0 : P_mlist nil.
Hypothesis P_mlist_cons : forall s, Pm s -> forall l, P_mlist l -> P_mlist (s::l).

(*Maybe used derive mutual induct instead*) 
Fixpoint gType_rect g : Pg g :=
  let fix seq_gType_rect gs : P_glist gs := 
    match gs with 
     | [::] => P_glist_0
     | g'::gs' => P_glist_cons (gType_rect g') (seq_gType_rect gs') 
     end in
  match g with 
   | GVar n => Pg_var n
   | GEnd => Pg_end
   | GRec g => Pg_rec (gType_rect g)
   | GMsg a u g => Pg_msg a (value_rect u) (gType_rect g)
   | GBranch a l => Pg_branch a (seq_gType_rect l)
   end
with mysort_rect m : Pm m :=
match m with 
| SBool => Pm_bool
| SNat => Pm_nat
| SGType g => Pm_sgtype (gType_rect g)
end
with value_rect v : Pv v :=
let fix seq_mysort_rect ss : P_mlist ss :=
 match ss with
  | [::] => P_mlist_0
  | m::ms => P_mlist_cons (mysort_rect m) (seq_mysort_rect ms)
 end
in
match v with 
| VSeqSort ss => Pv_vst (seq_mysort_rect ss)
| VLT e p => Pv_vlt (endpoint_rect e) p
end

with endpoint_rect e : Pe e :=
let fix seq_endpoint_rect ss : P_elist ss :=
 match ss with
  | [::] => P_elist_0
  | m::ms => P_elist_cons (endpoint_rect m) (seq_endpoint_rect ms)
 end in
match e with
| EVar n => Pe_var n
| EEnd => Pe_end
| EMsg d c m e => Pe_msg d c (value_rect m) (endpoint_rect e)
| EBranch d c es => Pe_branch d c (seq_endpoint_rect es)
| ERec e => Pe_rec  (endpoint_rect e)
end.



Definition seq_gType_rect : forall gs, P_glist gs :=
 fix seq_gType_rect gs : P_glist gs := 
    match gs with 
     | [::] => P_glist_0
     | g'::gs' => P_glist_cons (gType_rect g') (seq_gType_rect gs') 
     end.

Definition seq_mysort_rect : forall ms, P_mlist ms :=
 fix seq_mysort_rect ss : P_mlist ss :=
 match ss with
  | [::] => P_mlist_0
  | m::ms => P_mlist_cons (mysort_rect m) (seq_mysort_rect ms)
 end.

Definition seq_endpoint_rect : forall es, P_elist es :=
fix seq_endpoint_rect ss : P_elist ss :=
 match ss with
  | [::] => P_elist_0
  | m::ms => P_elist_cons (endpoint_rect m) (seq_endpoint_rect ms)
 end.

End Elimination.


Combined Scheme mut_ind_aux from gType_rect, mysort_rect, value_rect, endpoint_rect.


Inductive ForallT {A : Type} (P : A -> Type) : seq A -> Type :=
    Forall_nilT : ForallT P ([::]) | Forall_consT : forall (x : A) (l : seq A), P x -> ForallT P l -> ForallT P (x :: l).

Lemma ForallT_forall : forall (A : Type) (P : A -> Prop) l, ForallT P l -> (forall x, In x l -> P x). 
Proof. 
move => A P. elim. intros.  simpl in H. done.  
intros. inv X. inv H0. done. auto. 
Qed.




Definition list_eq {A} (r : A -> A -> bool) l0 l1 :=  (fix list_eq
     (s1 s2 : seq A) {struct s1} :
       bool :=
     match s1 with
     | [::] =>
         match s2 with
         | [::] => true
         | _ :: _ => false
         end
     | x1 :: s1' =>
         match s2 with
         | [::] => false
         | x2 :: s2' =>
             r x1 x2 &&
             list_eq s1' s2'
         end
     end) l0 l1.
Print VSeqSort. 
Fixpoint gType_eqb (g0 g1 : gType) { struct g0} : bool :=
match g0, g1 with
| GMsg a0 v0 g0', GMsg a0' v0' g1' => (a0 == a0') && value_eqb v0 v0' && (gType_eqb g0' g1') 
| GRec g0', GRec g1' => gType_eqb g0' g1' 
| GEnd, GEnd => true
| GBranch a gs, GBranch a' gs' => (a == a') && (list_eq gType_eqb  gs gs')
| GVar n, GVar n' => n == n'
| _, _ => false
end
with value_eqb (v0 v1 : value) {struct v0} :=
match v0, v1 with 
| VSeqSort s0, VSeqSort s1 => list_eq mysort_eqb s0 s1
| VLT e0 p0, VLT e1 p1 => endpoint_eqb e0 e1 && ( p0 == p1)
| _ , _ => false
end 

with endpoint_eqb (e0 e1 : endpoint) {struct e0} :=

match e0, e1 with
| EVar n0, EVar n1 => n0 == n1
| EEnd , EEnd => true
| EMsg d ch0 s0 e0, EMsg d1 ch1 s1 e1 =>  ((d,ch0) == (d1,ch1))  && (value_eqb s0 s1) && (endpoint_eqb e0 e1)
| EBranch d0 ch0 s0, EBranch d1 ch1 s1 => ((d0,ch0) == (d1,ch1))  && (list_eq endpoint_eqb s0 s1)
| ERec e0, ERec e1 => endpoint_eqb e0 e1
| _ , _ => false
end
with mysort_eqb (st0 st1 : mysort) {struct st0} :=
match st0,st1 with 
 | SBool, SBool => true
 | SNat, SNat => true
 | SGType g0, SGType g1 => gType_eqb g0 g1
 | _ , _ => false
end.




Section SpecializeElimination. 
Variables (Pg : gType -> Type) 
          (Pv : value -> Type) 
          (Pe : endpoint -> Type) 
          (Ps : mysort -> Type).


Definition mut_ind := (@mut_ind_aux Pg Pv Pe Ps (ForallT Pg) (ForallT Pe) (ForallT Ps)).  
(*(fun gl => forall g, In g gl ->Pg g)
                                                (fun el => forall e, In e el ->Pe e)
                                                (fun sl  => forall s, In s sl ->Ps s)). *)
End SpecializeElimination.

Definition refl (A : Type) (f : A -> A -> bool) := forall a, f a a. 
Lemma refl_eqbs : refl gType_eqb *  (refl mysort_eqb *  (refl value_eqb *  refl endpoint_eqb)).
Proof. unfold refl.  apply : mut_ind;intros; try split;simpl.
all : try solve [ lia | ssa | con;auto ].
ssa.  
elim : l X. done. simpl. ssa. inv X. done. inv X. auto. 
elim : l X. done. simpl. ssa. inv X. done. inv X. auto. 
ssa. 
elim : l X. done. simpl. ssa. inv X. done. inv X. auto.
Qed.

Definition leib_eq' (A : Type) (f : A -> A -> bool) := forall a b, f a b -> a = b.
Ltac inj := split; solve [ by move/eqP=>-> | by case; move=>->].
Ltac case_filter :=  case;try (rewrite /= ; constructor ; done);intros.
Ltac case_filter_on x :=  move : x;case_filter.

Ltac inject :=  split; [ by move=>-> | by case ].
Ltac inject2 :=  split;[ case; by move =>->-> | case;by move =>->-> ]. 
Ltac inject3 := split; [ case;  move=>->; case; move=>->->; done |  case; move =>->->->; done]. 

Lemma axioms_eqbs2 : leib_eq' gType_eqb *  (leib_eq' mysort_eqb *  (leib_eq' value_eqb *  leib_eq' endpoint_eqb)).
Proof. unfold leib_eq'.  apply : mut_ind;intros; try split;simpl in *.
-  destruct b;try done. f_equal. lia. 
-  destruct b;try done. 
-  destruct b;try done. 
- all : try solve  [ destruct b;try done | f_equal;auto | con;auto ]. 
-  destruct b;try done. ssa. rewrite (eqP H1) (H _ H4) (H0 _ H3) //=. 
- destruct b;try done. ssa. rewrite (eqP H0). f_equal. 
  elim : l l0 H1 X. case. done. done. simpl. intros. destruct l0;try done.
  ssa.  f_equal. inv X. rewrite <- H4.   done. done. inv X.  auto. 
- destruct b;try done. f_equal. 
  elim : l l0 X H. case. done. done. simpl. intros. destruct l0;try done.
  ssa.  f_equal. inv X. f_equal. apply/H3. done. apply/H.  inv X. auto. done. 
- destruct b;try done. ssa. rewrite (H _ H1) (eqP H2). ssa. 
- destruct b;try done. rewrite (H _ H0). ssa. 
- destruct b;try done. f_equal. lia. 
- destruct b;try done. ssa. move : H1. move/eqP. case. intros. subst. 
  f_equal; auto. 
- destruct b;try done. ssa. move : H0. move/eqP. case. intros. subst. 
  f_equal. 
  elim : l l0 X H1. case. done. done. simpl. intros. destruct l0;try done.
  ssa.  f_equal. inv X. f_equal. apply/H3. done. apply/H.  inv X. auto. done. 
- destruct b;try done. f_equal.  auto.
Qed. 

Definition leib_eq (A : Type) (f : A -> A -> bool) := forall a b, f a b <-> a = b.

Lemma axioms_eqbs : leib_eq gType_eqb *  (leib_eq mysort_eqb *  (leib_eq value_eqb *  leib_eq endpoint_eqb)).
Proof.
 split. split;intros. apply axioms_eqbs2=>//=. subst. apply refl_eqbs. 
 split. split;intros. apply axioms_eqbs2=>//=. subst. apply refl_eqbs. 
 split. split;intros. apply axioms_eqbs2=>//=. subst. apply refl_eqbs. 
 split;intros. apply axioms_eqbs2=>//=. subst. apply refl_eqbs. 
Qed.

Lemma iff_reflect : forall A (eqb : A -> A -> bool),
 (forall a0 a1, eqb a0 a1 <-> a0 = a1) -> forall x y , reflect (x = y) (eqb x y).
Proof.
intros. destruct (eqb x y) eqn:Heqn.
- constructor.  rewrite <- H. done. constructor.  intro. specialize H with x y. destruct H. 
  apply H1 in H0. rewrite Heqn in H0. done. 
Qed.

Lemma endpoint_axiom : Equality.axiom endpoint_eqb.
Proof. move : axioms_eqbs. do ? (case;intro). move/iff_reflect. done. 
Qed.

Lemma gType_axiom : Equality.axiom gType_eqb.
Proof. move : axioms_eqbs. do ? (case;intro). move : a.  move/iff_reflect.  done. 
Qed.

Lemma mysort_axiom : Equality.axiom mysort_eqb.
Proof. move : axioms_eqbs. do ? (case;intro). move : a0.  move/iff_reflect.  done. 
Qed.

Lemma value_axiom : Equality.axiom value_eqb.
Proof. move : axioms_eqbs. do ? (case;intro). move : a1.  move/iff_reflect.  done. 
Qed.

Definition endpoint_EqMixin := EqMixin endpoint_axiom.
Global Canonical endpoint_EqType := EqType endpoint endpoint_EqMixin.

Definition gType_EqMixin := EqMixin gType_axiom.
Global Canonical gType_EqType := EqType gType gType_EqMixin.

Definition mysort_EqMixin := EqMixin mysort_axiom.
Global Canonical mysort_EqType := EqType mysort mysort_EqMixin.

Definition value_EqMixin := EqMixin value_axiom.
Global Canonical value_EqType := EqType value value_EqMixin.



Definition true_pred A := fun (_ : A) => nat.

(*Fixpoint inb (A : Type) (f : A -> A -> bool) (a : A) (l : seq A) := 
match l with
| [::] => false
| b :: m => (f a b) || (inb f a m)
end.*)

Section SpecializeElimination2. 
Variables (Pg : gType -> Type) 
          (Pv : value -> Type) 
          (Pe : endpoint -> Type) 
          (Ps : mysort -> Type).


(*(fun gl => forall g, In g gl ->Pg g)
                                                (fun el => forall e, In e el ->Pe e)
                                                (fun sl  => forall s, In s sl ->Ps s)). *)



Definition gType_rect_true := (@gType_rect Pg  (@true_pred value) (@true_pred endpoint) (@true_pred mysort) (fun gl => forall g, g \in  gl ->Pg g)
                                                (@true_pred (seq endpoint))
                                                (@true_pred (seq mysort))).

Definition endpoint_rect_true := (@endpoint_rect (@true_pred gType) (@true_pred value) Pe (@true_pred mysort) (@true_pred (seq gType))
                                                (fun el => forall e,  e \in el -> Pe e)
                                                (@true_pred (seq mysort))).
End SpecializeElimination2.




Lemma inP : forall {A : eqType} l (g : A) , reflect (In g l) (g \in l).
Proof.
move => A. elim.
rewrite /=. intros. rewrite in_nil. constructor. done.
- move => a l H g. rewrite /=. apply Bool.iff_reflect. split. case.
move=>->. by rewrite in_cons eqxx. rewrite in_cons. move/H=>->.
by rewrite orbC. 
rewrite inE. move/orP =>[].  move/eqP=>->. auto. move/H. auto.
Qed.


Print gType_rect. 


Lemma gType_ind
     : forall (Pg : gType -> Prop  ),
       (forall n : nat, Pg (GVar n)) ->
       Pg GEnd ->
       (forall g : gType, Pg g -> Pg (GRec g)) ->
       (forall (a : action) (v : value),
        forall g : gType,
        Pg g -> Pg (GMsg a v g)) ->
       (forall (a : action) (l : seq gType),
         (forall g, g \in l -> Pg g) -> Pg (GBranch a l)) ->
       forall g : gType, Pg g.
Proof.
intros.  apply : gType_rect_true;auto. con. con. 
intros. con. con. done. intros. rewrite inE in H6. destruct (orP H6). rewrite (eqP H7). done. auto. 
simpl. 
Print true_pred. con. con. 
Qed.

Lemma gType_indT
     : forall (Pg : gType -> Type ),
       (forall n : nat, Pg (GVar n)) ->
       Pg GEnd ->
       (forall g : gType, Pg g -> Pg (GRec g)) ->
       (forall (a : action) (v : value),
        forall g : gType,
        Pg g -> Pg (GMsg a v g)) ->
       (forall (a : action) (l : seq gType),
         (forall g, g \in l -> Pg g) -> Pg (GBranch a l)) ->
       forall g : gType, Pg g.
Proof.
intros.  apply : gType_rect_true;auto. con. con. 
intros. con. con. done. intros. rewrite inE in H. 
destruct (eqVneq g1 g0). subst. auto. simpl in H. auto. 
con. con. 
Qed.

Lemma endpoint_ind
     : forall (Pe : endpoint -> Prop),
       (forall n : nat, Pe (EVar n)) ->
       Pe EEnd ->
       (forall e : endpoint, Pe e -> Pe (ERec e)) ->
       (forall d c (v : value),
        forall e : endpoint,
        Pe e  -> Pe (EMsg d c v e)) ->
       (forall d c (l : seq endpoint),
         (forall g, g \in l -> Pe g) -> Pe (EBranch d c l)) ->
       forall g : endpoint, Pe g.
Proof.
intros. apply : endpoint_rect_true;auto.
all: try (rewrite /true_pred; constructor). 
intros.  done. intros. rewrite inE in H6. destruct (orP H6). rewrite (eqP H7). done. 
auto. 
Qed.

(*Section Operations.
Implicit Type g : gType.*)
(*Fixpoint bound_i (i : nat) g  := 
match g with 
| GEnd => true
| GMsg _ _ g0 => bound_i i g0
| GBranch _ gs => all (bound_i i) gs
(*| GPar g0 g1 => (bound_i i g0) && (bound_i i g1)*)
| GRec g0 => bound_i (S i) g0
| GVar n => n < i
end.
Fixpoint bound_i_e i e := 
  match e with
  | EVar n => n < i
  | EEnd => true
  | ERec g0 => bound_i_e i.+1 g0
  | EMsg _ _ _ g0 => bound_i_e i g0
  | EBranch _ _ gs => all (bound_i_e i) gs
  end.
(*Inspired by Francisco*)
Fixpoint contractive_i (d : nat) g :=
match g with 
| GEnd => true
| GMsg _ _ g0 => contractive_i 0 g0
| GBranch _ gs => all (contractive_i 0) gs
(*| GPar g0 g1 => (contractive_i d g0) && (contractive_i d g1)*)
| GRec g0 => contractive_i (S d) g0
| GVar n => d <= n
end. *)




(*Fixpoint mu_height g :=
match g with
| GRec g0 => (mu_height g0).+1
| _ => 0
end.
Lemma mu_height_subst : forall g0 g1  i, contractive_i (S i) g0 -> mu_height (substitution i g0 g1) = mu_height g0.
Proof. 
elim; try solve [by rewrite /=].
- rewrite /=. intros. case : (eqVneq n i) H. move=>->. by rewrite ltnn. by rewrite /=. 
- intros. rewrite /=. f_equal. apply H. done. 
Qed.
Definition g_next_aux g := 
match g with 
| GMsg a u g0 => Some (a,[::g0])
| GBranch a gs => Some (a,gs)
| _ => None
end.*)


(*Notation dec x := (Sumbool.sumbool_of_bool x).
Equations unf_recs (i : nat) g : gType by wf (mu_height g)  :=
unf_recs i (GRec g) := if (dec (contractive_i i (GRec g))) is left _  then (unf_recs i (substitution i g (GRec g))) else g;
unf_recs i g := g.
Next Obligation.
rewrite mu_height_subst. done. done.
Qed.
Definition g_next g :=
match unf_recs 0 g with 
| GMsg _ _ g0 => [::g0]
| GBranch _ gs => gs
| _ => [::]
end.
Definition act_of_g g :=
match unf_recs 0 g with 
| GMsg a _ _ => Some a
| GBranch a _ => Some a
| _ => None
end.*)

(*End Operations.*)


(*Derive Inversion gType_inv with gType Sort Prop.

Check gType_inv.*)
