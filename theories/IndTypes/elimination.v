From mathcomp Require Import all_ssreflect zify.
Require Export Proj.utils.
From IndTypes Require Export syntax. 
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

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

Fixpoint esize_pred (g : lType) :=
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

Fixpoint gcontractive g := 
match g with
| GVar j => true
| GEnd => true
| GMsg _ _ g0 => gcontractive g0
| GBranch  _ gs => all gcontractive gs
| GRec g0 => (guarded 0 g0) && (gcontractive g0)
end. 

Fixpoint lcontractive g := 
match g with
| EVar j => true
| EEnd => true
| EMsg _ _ _ g0 => lcontractive g0
| EBranch _ _ gs => all lcontractive gs
| ERec g0 => (eguarded 0 g0) && (lcontractive g0)
end. 

Open Scope nat_scope.
Fixpoint gsize e := 
match e with 
| GMsg  _ _ e0 => (gsize e0).+1
| GBranch _ es => foldr (fun e0 acc => (gsize e0) + acc ) 2 es
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




Section Elimination.

Variables (Pg : gType -> Type) 
          (Pv : value -> Type) 
          (Pe : lType -> Type) 
          (Pm : mysort -> Type)
          (P_glist : seq gType -> Type)
          (P_elist : seq lType -> Type)
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
Hypothesis Pe_msg : forall (d : dir) (c : ch) (s : value), Pv s -> forall e : lType, Pe e -> Pe (EMsg d c s e).
Hypothesis Pe_branch : forall (d : dir) (c : ch) (l : seq lType), P_elist l  -> Pe (EBranch d c l).
Hypothesis Pe_rec : forall e : lType, Pe e -> Pe (ERec e).

Hypothesis P_glist_0 : P_glist nil.
Hypothesis P_glist_cons : forall g, Pg g -> forall l, P_glist l -> P_glist (g::l).

Hypothesis P_elist_0 : P_elist nil.
Hypothesis P_elist_cons : forall e, Pe e -> forall l, P_elist l -> P_elist (e::l).

Hypothesis P_mlist_0 : P_mlist nil.
Hypothesis P_mlist_cons : forall s, Pm s -> forall l, P_mlist l -> P_mlist (s::l).

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
| VLT e p => Pv_vlt (lType_rect e) p
end

with lType_rect e : Pe e :=
let fix seq_lType_rect ss : P_elist ss :=
 match ss with
  | [::] => P_elist_0
  | m::ms => P_elist_cons (lType_rect m) (seq_lType_rect ms)
 end in
match e with
| EVar n => Pe_var n
| EEnd => Pe_end
| EMsg d c m e => Pe_msg d c (value_rect m) (lType_rect e)
| EBranch d c es => Pe_branch d c (seq_lType_rect es)
| ERec e => Pe_rec  (lType_rect e)
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

Definition seq_lType_rect : forall es, P_elist es :=
fix seq_lType_rect ss : P_elist ss :=
 match ss with
  | [::] => P_elist_0
  | m::ms => P_elist_cons (lType_rect m) (seq_lType_rect ms)
 end.

End Elimination.


Combined Scheme mut_ind_aux from gType_rect, mysort_rect, value_rect, lType_rect.


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
| VLT e0 p0, VLT e1 p1 => lType_eqb e0 e1 && ( p0 == p1)
| _ , _ => false
end 

with lType_eqb (e0 e1 : lType) {struct e0} :=

match e0, e1 with
| EVar n0, EVar n1 => n0 == n1
| EEnd , EEnd => true
| EMsg d ch0 s0 e0, EMsg d1 ch1 s1 e1 =>  ((d,ch0) == (d1,ch1))  && (value_eqb s0 s1) && (lType_eqb e0 e1)
| EBranch d0 ch0 s0, EBranch d1 ch1 s1 => ((d0,ch0) == (d1,ch1))  && (list_eq lType_eqb s0 s1)
| ERec e0, ERec e1 => lType_eqb e0 e1
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
          (Pe : lType -> Type) 
          (Ps : mysort -> Type).


Definition mut_ind := (@mut_ind_aux Pg Pv Pe Ps (ForallT Pg) (ForallT Pe) (ForallT Ps)).  
End SpecializeElimination.

Definition refl (A : Type) (f : A -> A -> bool) := forall a, f a a. 
Lemma refl_eqbs : refl gType_eqb *  (refl mysort_eqb *  (refl value_eqb *  refl lType_eqb)).
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

Lemma axioms_eqbs2 : leib_eq' gType_eqb *  (leib_eq' mysort_eqb *  (leib_eq' value_eqb *  leib_eq' lType_eqb)).
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

Lemma axioms_eqbs : leib_eq gType_eqb *  (leib_eq mysort_eqb *  (leib_eq value_eqb *  leib_eq lType_eqb)).
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

Lemma lType_axiom : Equality.axiom lType_eqb.
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

Definition lType_EqMixin := EqMixin lType_axiom.
Global Canonical lType_EqType := EqType lType lType_EqMixin.

Definition gType_EqMixin := EqMixin gType_axiom.
Global Canonical gType_EqType := EqType gType gType_EqMixin.

Definition mysort_EqMixin := EqMixin mysort_axiom.
Global Canonical mysort_EqType := EqType mysort mysort_EqMixin.

Definition value_EqMixin := EqMixin value_axiom.
Global Canonical value_EqType := EqType value value_EqMixin.



Definition true_pred A := fun (_ : A) => nat.
Section SpecializeElimination2. 
Variables (Pg : gType -> Type) 
          (Pv : value -> Type) 
          (Pe : lType -> Type) 
          (Ps : mysort -> Type).

Definition gType_rect_true := (@gType_rect Pg  (@true_pred value) (@true_pred lType) (@true_pred mysort) (fun gl => forall g, g \in  gl ->Pg g)
                                                (@true_pred (seq lType))
                                                (@true_pred (seq mysort))).

Definition lType_rect_true := (@lType_rect (@true_pred gType) (@true_pred value) Pe (@true_pred mysort) (@true_pred (seq gType))
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

Lemma lType_ind
     : forall (Pe : lType -> Prop),
       (forall n : nat, Pe (EVar n)) ->
       Pe EEnd ->
       (forall e : lType, Pe e -> Pe (ERec e)) ->
       (forall d c (v : value),
        forall e : lType,
        Pe e  -> Pe (EMsg d c v e)) ->
       (forall d c (l : seq lType),
         (forall g, g \in l -> Pe g) -> Pe (EBranch d c l)) ->
       forall g : lType, Pe g.
Proof.
intros. apply : lType_rect_true;auto.
all: try (rewrite /true_pred; constructor). 
intros.  done. intros. rewrite inE in H6. destruct (orP H6). rewrite (eqP H7). done. 
auto. 
Qed.
