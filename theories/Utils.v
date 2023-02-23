From mathcomp Require Import all_ssreflect finmap zify.
From Equations Require Import Equations.



Equations foldIn {A B : Type} (l : list A) (f : forall (x : A), List.In x l -> B -> B) (b : B) : B := 
  foldIn nil f b := b;
  foldIn (x:: xs) f b := f x _ (foldIn xs (fun x H b => f x _ b) b).


Equations filterIn {A : Type} (l : list A) (f : forall (x : A), List.In x l -> bool)  : seq A := 
  filterIn nil f := nil;
  filterIn (x:: xs) f := if f x _ then x :: (filterIn xs (fun x H => f x _)) else filterIn xs (fun x H => f x _).



Lemma filterInP : forall (A : Type) (l : list A) (f : A -> bool), filterIn l (fun x H => f x) = filter f l.
Proof. 
move => A. elim. done. 
intros. simpl.   simp filterIn. destruct (f _ ). f_equal. done. done. 
Qed. 

Definition foldInMap {A B : Type} (l : list A) (f : forall (x : A), List.In x l -> B) : seq B := 
 foldIn l (fun x H b => (f x H)::b) nil. 


Lemma foldInMapP : forall (A B : Type) (l : list A) (f : A -> B), foldInMap l (fun x H => f x) = map f l.
Proof. 
move => A B. rewrite /foldInMap.  elim. done. 
intros. simpl.   simp foldIn. f_equal. done. 
Qed. 


Definition foldInFilter {A : Type} (l : list A) (f : forall (x : A), List.In x l -> bool) : seq A := 
 foldIn l (fun x H b => if f x H then x::b else b) nil. 


Lemma foldInFilterP : forall (A : Type) (l : list A) (f : A -> bool), foldInFilter l (fun x H => f x) = filter f l.
Proof. 
move => A. rewrite /foldInFilter.  elim. done. 
intros. simpl.   simp foldIn. destruct (f _ ). f_equal. done. done. 
Qed. 

Lemma foldInFilterP2 : forall (A : Type) (l : list A) (f : forall (x : A), List.In x l -> bool) (f' : A -> bool), (forall (x : A) (H : List.In x l), f x H = f' x) -> 
  foldInFilter l f = filter (fun x => f' x) l.
Proof. 
move => A. rewrite /foldInFilter.  elim. done. 
intros. simpl.   simp foldIn. rewrite H0. destruct (f' _ ). f_equal. apply H. auto. apply H. auto. 
Qed. 


Definition foldInPmap {A B : Type} (l : list A) (f : forall (x : A), List.In x l -> option B) : seq B := 
 foldIn l (fun x H b => if f x H is Some e then e::b else b) nil. 


Lemma foldInPmapP : forall (A B : Type) (l : list A) (f : A -> option B), foldInPmap l (fun x H => f x) = pmap f l.
Proof. 
move => A B. rewrite /foldInPmap.  elim. done. 
intros. simpl.   simp foldIn. destruct (f a). simpl. f_equal. apply H. simpl. done. 
Qed. 

Definition foldInHas {A : Type} (l : list A) (f : forall (x : A), List.In x l -> bool) : bool  := 
 foldIn l (fun x H b => (f x H) || b ) false. 

Lemma foldInHasP : forall (A: Type) (l : list A) (f : A -> bool), foldInHas l (fun x H => f x) = has f l.
Proof. 
move => A. rewrite /foldInHas.  elim. done. 
intros. simpl.   simp foldIn. destruct (f a). done.  simpl. apply H. 
Qed. 


Definition foldInAll {A : Type} (l : list A) (f : forall (x : A), List.In x l -> bool) : bool  := 
 foldIn l (fun x H b => (f x H) && b ) true.  

Lemma foldInAllP : forall (A: Type) (l : list A) (f : A -> bool), foldInAll l (fun x H => f x) = all f l.
Proof. 
move => A. rewrite /foldInAll.  elim. done. 
intros. simpl.   simp foldIn. f_equal.  done. 
Qed. 


Equations findIn {A: Type} (l : list A) (f : forall (x : A), List.In x l -> bool) : nat := 
  findIn nil f  := 0;
  findIn (x:: xs) f := if f x _ then 0 else (findIn xs (fun x H => f x _)).+1.

Lemma findInP : forall (A: Type) (l : list A) (f : A -> bool), findIn l (fun x H => f x) = find f l.
Proof. 
move => A. elim. done. intros. simpl. simp findIn. destruct (f a). done. rewrite H. done. 
Qed. 




(*
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.*)

Locate Forall.

Notation In := List.In.
Notation Forall := List.Forall.


Lemma In_in : forall (A : eqType) (a : A) l, In a l <-> a \in l.
Proof.
move => A a. elim. split;done.
intros. rewrite /= inE. split. case. move=>->. rewrite eqxx. done. move/H. move=>->. by rewrite orbC. 
move/orP. case. move/eqP. move=>->. auto. move/H. auto. 
Qed.

Lemma Forall_forall
     : forall (A : eqType) (P : A -> Prop) (l : seq A), Forall P l <-> (forall x : A, x \in l -> P x).
Proof. intros. rewrite List.Forall_forall. split;intros;auto;by apply/H/In_in. Qed.

Lemma nat_fact : forall n, n - (n - n) = n. lia. Qed.

Lemma forallzipP1 : forall (A B : eqType) (P : A * B -> Prop) a b l l',  size l = size l' -> (forall x0, x0 < size l -> P (nth a l x0,nth b l' x0)) -> 
Forall P (zip l l').
Proof.
intros. apply/Forall_forall. intros. move : H1. move/nthP=>HH. specialize HH with (a,b). 
destruct HH. rewrite -H2. rewrite nth_zip //=. apply H0. move : H1. by rewrite size_zip minnE H nat_fact. 
Qed.


Lemma forallzipP2 : forall (A B : eqType) (P : A * B -> Prop) a b l l', Forall P (zip l l') -> size l = size l' -> (forall x0, x0 < size l -> P (nth a l x0,nth b l' x0)).
Proof.
move => A B P a b. elim. case. done. done. move => a0 l IH. case. done. move => a1 l0 H Hsize. intros. simpl in H0. destruct x0. simpl. simpl in H. inversion H. done. simpl. apply IH. simpl in H. inversion H. done. simpl in Hsize. lia. lia. 
Qed.

Lemma forallzipP : forall (A B : eqType) (P : A * B -> Prop) a b l l',  size l = size l' -> (forall x0, x0 < size l -> P (nth a l x0,nth b l' x0)) <-> 
Forall P (zip l l').
Proof.
intros.  split. apply forallzipP1. done. move/forallzipP2=>HH. apply HH. done. 
Qed.

Lemma forallzipto1 : forall (A B : Type) (P : A -> Prop) (l : seq A) (l' : seq B), size l = size l' -> 
Forall (fun p => P p.1) (zip l l') -> Forall P l.
Proof.
move => A B P. elim. case. done. done. intros. destruct l'. simpl in H0. done. simpl in *. inversion H1. subst. simpl in *. constructor. done. apply :H. inversion H0. eauto. done. 
Qed.

Lemma forallzipto2 : forall (A B : Type) (P : B -> Prop) (l' : seq B) (l : seq A), size l = size l' -> 
Forall (fun p => P p.2) (zip l l') -> Forall P l'.
Proof.
move => A B P. elim. case. done. done. intros. destruct l0. simpl in H0. done. simpl in *. inversion H1. subst. simpl in *. constructor. done. apply :H. inversion H0. eauto. done. 
Qed.


Lemma forallP : forall (A : eqType) (P : A -> Prop) a l,(forall x0, x0 < size l -> P (nth a l x0)) -> 
Forall P l.
Proof. intros.
apply/Forall_forall. intros. move : H0 => /nthP H3.  specialize H3 with a. destruct H3. rewrite -H1. auto.
Qed.

Lemma my_in_cons : forall (A :eqType) (a : A) l, a \in (a::l).
Proof. intros. rewrite !inE eqxx. done. Qed.

Lemma my_in_cons2 : forall (A :eqType) (a a0 : A) l, a \in l -> a \in (a0::l).
Proof. intros. rewrite !inE H. lia. Qed.

Hint Resolve my_in_cons my_in_cons2.

Ltac case_if := match goal with 
                | [ |- context[if ?X then _ else _ ]] => have : X by subst
                | [ |- context[if ?X then _ else _ ]] => have : X = false by subst 

                | [ |- context[if ?X then _ else _ ]] => let H := fresh in destruct X eqn:H

                end; try (move=>->).

(*Ltac iflia := case_if;*)

Ltac rifliad := (repeat case_if); try done.

Lemma neg_sym : forall (A : eqType) (a b : A), (a != b) = (b != a).
Proof.
intros. destruct (eqVneq a b).  done. done. 
Qed.

Ltac split_and := intros;repeat (match goal with 
                   | [ H : is_true (_ && _) |- _ ] => destruct (andP H);clear H
                   | [ H : (_ && _) = true  |- _ ] => destruct (andP H);clear H
                   | [ H : _ /\ _  |- _ ] => destruct H
                   | [ |- _ /\ _ ] => split
                   | [ |- is_true (_ && _) ] => apply/andP;split 

                  end);auto.

Notation eq_iff := Bool.eq_iff_eq_true.
Ltac ssa := rewrite ?inE;simpl in *; split_and;try done.



Lemma negb_involutive : forall b, ~~ ~~ b = b. case;done. Qed.


Open Scope fset_scope.
Lemma big_exists : forall (A : eqType) (B : choiceType) (l : seq A) (f0 : A -> {fset B}) p, p \in \bigcup_(j <- l) (f0 j) = has (fun x => p \in f0 x) l. 
Proof. 
move => A B. elim. move => f0 p. rewrite big_nil. done. intros. simpl. rewrite big_cons !inE. destruct ( (p \in f0 a) ) eqn:Heqn;rewrite /=. 
done.
apply H.
Qed.

Lemma big_f_eq : forall (A : eqType) (B : choiceType)  (l : seq A) (f : A -> {fset B}) f1, (forall g, g \in l -> f g = f1 g) ->  \bigcup_(j <- l) (f j) =  \bigcup_(j <- l) (f1 j).
Proof. move => A B. elim. intros. by rewrite !big_nil.
intros. rewrite !big_cons. f_equal. auto. apply H. auto. 
Qed.

Lemma big_if : forall (A : eqType) (B : choiceType) (l : seq A) (p : pred A) (f : A -> {fset B}) S, 
                  \bigcup_(j <- l) (if p j then f j `|` S else f j) = 
                   (\bigcup_(j <- l) (f j)) `|` (if has p l then S else fset0).
Proof. move => A B. elim. intros. rewrite !big_nil /=. apply/fsetP=>k. by rewrite !inE. 
intros. rewrite !big_cons /= H. rifliad. all : apply/fsetP=>k; rewrite !inE; lia. 
Qed.

Lemma big_cup_in : forall (A : eqType) (B: choiceType) n (l : seq A) (f0 f1 : A -> {fset B}), (forall x n, x \in l -> n \in (f0 x) -> n \in (f1 x)) -> n \in \bigcup_(j <- l) (f0 j) ->  n \in \bigcup_(j <- l) (f1 j).
Proof. move => A B n. elim. move => f0 f1.  rewrite big_nil. done. intros. move : H1. rewrite !big_cons !inE. move/orP=>[].  intros. rewrite H0 //=. intros. erewrite H. lia. intros. apply H0. eauto. eauto. apply b. 
Qed.


Ltac norm_eqs := repeat (match goal with 
                   | [ H : (_ == _) |- _ ] => move : H => /eqP=>H
                   | [ H : (_ == _) = true |- _ ] => move : H => /eqP=>H
                   | [ H : (_ == _) = false |- _ ] => move : H => /negbT=>H

                  end);subst;repeat (match goal with 
                   | [ H : is_true (?a != ?a_) |- _ ] => rewrite eqxx in H;done 

                  end).


Let inE := (inE, eqxx,negb_or,negb_and).



Fixpoint compose {A B C : Type} (aa : seq A) (bb : seq B) (r : A -> B -> C) :=
match aa with 
| nil => nil
| a::aa' => (map (r a) bb) ++ (compose aa' bb r)
end.


Lemma mem_compose : forall (A B C : eqType) (aa : seq A) (bb : seq B) (a : A) (b : B) (r : A -> B -> C), a \in aa -> b \in bb -> r a b \in compose aa bb r.
Proof. move => A B C. elim;intros. done. 
simpl. rewrite mem_cat. rewrite !inE in H0. destruct (orP H0). rewrite (eqP H2). apply/orP. 
left. apply/map_f. done. apply/orP. right. apply/H. done. done. 
Qed.

Lemma mem_compose2 : forall (A B : eqType) aa bb (a : A) (b : B),   pair a b \in compose aa bb pair ->  a \in aa /\ b \in bb.
Proof. move => A B. elim;intros. done. 
move : H0=>/=. rewrite mem_cat. move/orP. case. move/mapP=>[] //=. intros. inversion q. subst. rewrite inE //= eqxx. lia. 
move/H. case. rewrite inE. move=>->. ssa. lia. 
Qed.


Lemma mem_zip : forall (A B: eqType) l0 l1  (a : A) (b : B),  (a,b) \in zip l0 l1 -> a \in l0 /\ b \in l1. 
Proof. 
move => A B.
elim.  intros. destruct l1.  done. done. 
intros. destruct l1.  simpl in H0. done. simpl in H0. rewrite inE in H0. destruct (orP H0). move : (eqP H1). case. intros. subst. 
rewrite inE eqxx /=. ssa. rewrite eqxx //=. 
apply H in H1. ssa. 
rewrite H1. lia. rewrite H2. lia. 
Qed.




Arguments rem {_}.
Fixpoint rep_rem {A : eqType} (xs l : seq A) :=
match xs with 
| nil => l 
| x::xs' => rem x (rep_rem xs' l)
end. 

Lemma mem_rem : forall (A : eqType) l' (a a' : A), a != a' -> a \in l' ->  a \in rem a' l'.  
Proof. 
move => A.
elim. done. 
intros. simpl. case_if. move : H2. move/eqP=>HH. subst. rewrite inE in H1. 
move : H1. move : (negbTE H0)=>-> //=.
move : H1. 
rewrite !inE. move/orP. case. move=>-> //=. move/H=>->. lia. done. 
Qed.

Lemma mem_rem2 : forall (A : eqType) l' (a a' : A), a != a' -> a \in rem a' l'  -> a \in l'.  
Proof. 
move => A. 
elim. done. 
intros. simpl in H1. move : H1. case_if. rewrite inE. move=>->. lia.
rewrite inE. move/orP=>[]. move/eqP=>->. done. 
move/H. rewrite inE. move=>->. lia. lia. 
Qed.

Lemma mem_rep_rem : forall (A : eqType) l l' (a : A), a \notin l -> a \in l' ->  a \in rep_rem l l'.  
Proof. 
move => A. elim. done.
intros. simpl. rewrite inE negb_or in H0. ssa. apply/mem_rem. done. auto. 
Qed.

Lemma mem_rep_rem2 : forall (A : eqType) l l' (a : A), a \in rep_rem l l' -> a \notin l -> a \in l'.  
Proof. 
move => A. elim. done.
intros. simpl. rewrite inE negb_or in H1. ssa.
apply mem_rem2 in H0.  auto. lia. 
Qed.

Lemma mem_rep_iff : forall (A : eqType) l l' (a : A),  a \notin l  -> a \in l'  <-> a \in rep_rem l l'.
Proof. 
move => A. 
intros. split;intros. apply/mem_rep_rem;auto.  
apply/mem_rep_rem2;eauto. 
Qed.


Definition next_closed {A: eqType} (l : seq A) (next : A -> seq A) := forall a a', a \in l -> a' \in next a -> a' \in l.
Definition unf_closed {A: eqType} (l : seq A) (unf : A ->  A) := forall a, a \in l -> unf a \in l. 


Lemma closed_next_fin_next : forall (A : eqType) l (f : A -> seq A) , next_closed l f -> (adhoc_seq_sub_finType l) -> 
seq  (adhoc_seq_sub_finType l). 
Proof. 
intros. destruct X. 
move : ssvalP.  move/H=>HH. clear H.
elim : (f ssval) HH. intros. exact nil.
intros. simpl. apply cons. econstructor. apply/HH. rewrite inE.   apply/orP. left. apply eqxx. 
apply/X. intros 
apply cons.  apply/HH. rewrite inE cons. lia. 
Defined. 

CoInductive coseq (A : Type) : Type :=  conil : coseq A | cocons : A -> coseq A -> coseq A.

Arguments coseq _. 
Arguments conil {_}. 
Arguments cocons {_}. 

Lemma coseq_match : forall {A : Type} (g : coseq A), g = match g with | conil  => conil | cocons a b => cocons a b end.  
Proof. move => A[] //=. Qed. 

Inductive forall_gen {A B : Type} (P : A -> B -> Prop)  (R : coseq A -> coseq B -> Prop)  : coseq A -> coseq B -> Prop :=
| FEE_nil : forall_gen P R conil conil
| FEE_cons e0 e1 es0 es1 : P e0 e1 -> R es0 es1 -> forall_gen P R (cocons e0 es0) (cocons e1 es1).

Require Import Paco.paco. 
Lemma forall_gen_mon (A B : Type) (P : A -> B -> Prop)  : monotone2 (forall_gen P). 
Proof. 
move => x y. intros. induction IN. constructor. constructor. done. auto. 
Qed. 

Hint Resolve forall_gen_mon : paco. 


Lemma forall_gen_nil : forall (A B : Type) (r : coseq A -> coseq B -> Prop) (P : A -> B -> Prop), paco2 (forall_gen P) r conil conil. 
Proof. 
intros. pfold. constructor. 
Qed.

Hint Resolve forall_gen_nil. 

Definition ForallC {A B : Type} (P : A -> B -> Prop)  es0 es1 := paco2 (forall_gen P) bot2 es0 es1. 

(*Notation "l0 =[ R ]= l1" :=  (paco2 (forall_gen R) bot2 l0 l1)(at level 70). *)

Lemma forall_gen_mon2 : forall (A B : Type) (P0 P1: A -> B -> Prop) (R0 R1 : coseq A -> coseq B -> Prop),
 R0 <2= R1 -> P0 <2= P1 ->  paco2 (forall_gen P0) R0 <2= paco2 (forall_gen  P1) R1. 
Proof.
move => A B P0 P1 R0 R1.
pcofix CIH. 
intros. pfold. punfold PR. induction PR.  constructor. 
constructor. auto. inversion H2. right. apply/CIH. auto. done.  
done. auto. 
Qed.

Lemma forall_genF_mon2 : forall (A B : Type) (P0 P1: A -> B -> Prop) (R0 R1 : coseq A -> coseq B -> Prop),
 R0 <2= R1 -> P0 <2= P1 ->  (forall_gen P0) R0 <2= (forall_gen  P1) R1. 
Proof.
move => A B P0 P1 R0 R1.
intros. induction PR. constructor. constructor. auto. auto. 
Qed.

CoFixpoint to_coseq {A: Type} (l : seq A) : coseq A := 
match l with 
| nil => conil
| cons a l' => cocons a (to_coseq l')
end. 

Coercion to_coseq : seq  >-> coseq.

Definition ForallC1 {A : Type} (P : A ->  Prop) aa := paco2 (forall_gen (fun a _ => P a)) bot2 aa aa. 

Inductive CoIn {A : Type} (eq : A -> A -> Prop) :  A -> coseq A -> Prop :=
(*| CoInC a a' l : eq a  a' \/ CoIn eq a l ->  CoIn eq a (cocons a' l).*)
| CoInC1 a a' l : eq a  a' ->  CoIn eq a (cocons a' l)
| CoInC2 a a' l : CoIn eq a l ->  CoIn eq a (cocons a' l).


Notation "x <<( U ) R >> y" := (paco2 R U x y)(at level 10, R at next level).
Notation "x << R >> y" := (paco2 R bot2 x y)(at level 10, R at next level).

Ltac coseq_tac := rewrite (coseq_match (to_coseq _)) /=. 
Ltac coseq_tac_in H := rewrite (coseq_match (to_coseq _)) /= in H. 
 

Lemma cocons_coerce : forall (A : Type) (e0 : A) (es0 : coseq A) (es : seq A), cocons e0 es0 = to_coseq es -> exists es', es = e0::es' /\ to_coseq es' = es0.
Proof. 
move => A. intros. coseq_tac_in H. destruct es;try done. exists es. ssa. 
inversion H. 
done. inversion H. done. 
Qed.

Lemma to_coseq_cons : forall (A: Type) (a : A) (e : seq A), to_coseq (a::e) = cocons a e.
Proof. 
intros. coseq_tac. done. 
Qed.

Lemma to_coseq_nil : forall (A: Type) , to_coseq (@nil A) = conil.
Proof. 
intros. coseq_tac. done. 
Qed.

Let coeq := (to_coseq_nil, to_coseq_cons).

Lemma forall_gen_refl : forall (A : Type) g r (P : A -> A -> Prop) , (forall x, P x x) -> g <<(r) (forall_gen P)  >>  g. 
Proof. 
intros. move : g. pcofix CIH. 
case. pfold. constructor.  
intros. pfold. constructor ;auto.  
Qed.

Hint Resolve forall_gen_refl. 

Lemma forall_gen_P_mon : forall (A  B : Type) (P0 P1 : A -> B -> Prop) l0 l1, l0 << (forall_gen P0) >> l1 ->  (forall a b, P0 a b -> P1 a b) -> l0 << (forall_gen P1) >> l1. 
Proof.
intros. move : l0 l1 H. pcofix CIH. 
intros. 
pcofix CIH.  
intros. punfold H1. inversion H1. done. pfold. constructor. auto. eauto. 
right. apply/CIH. pclearbot. done. 
Qed.

Ltac inv H := inversion H;subst. 
Ltac pc := pfold;constructor;auto.
Ltac uis H := (try  punfold H);inversion H;subst;try pc;auto;pclearbot. 
Ltac cauto := pclearbot;auto. 

Fixpoint approx_coseq {A : Type} n (l : coseq A) := 
if n is n'.+1 then if l is cocons a l' then a :: (approx_coseq n' l') else nil else nil. 

Definition co_nth {A : Type} (d : A) (l : coseq A) (n : nat) := nth d (approx_coseq n.+1 l) n.


Lemma index_ForallIC : forall {A : eqType} {B : Type} (l0 : seq A) (l1 : coseq B) a b n (R : A -> B -> Prop), ForallC R l0 l1 -> n < size l0 ->  R (nth a l0 n) (co_nth b l1 n).  
Proof. 
move => A B.  elim;intros. done. 
ssa. destruct l1. punfold H0. inversion H0. rewrite coeq in H0. inv H0. 
destruct n. 
simpl. pclearbot. rewrite /co_nth /=. rewrite coeq in H0. uis H0.  
simpl. have :  (co_nth b (cocons b0 l1) n.+1) =  (co_nth b l1) n.   rewrite /co_nth /=. done. move=>->. 
apply H. rewrite coeq in H0. uis H0. done. auto. 
Qed.  

Lemma forall_gen_mon_coerce : forall (A  B : Type) (aa : seq A) (bb : coseq B) (P0 P1 : A -> B -> Prop) (R0 R1 : coseq A -> coseq B -> Prop), 
(forall a b, P0 a b -> P1 a b) -> 
(forall (x0 : seq A) (x1 : coseq B), R0 x0 x1 -> R1 x0 x1) ->  paco2 (forall_gen P0) R0 aa bb  -> paco2 (forall_gen P1) R1 aa bb.
Proof.
move => A B. elim. intros. destruct bb. pfold. 
rewrite (coseq_match (to_coseq _)) /=. constructor.
coseq_tac_in H1. punfold H1. inversion H1. 
intros. destruct bb. coseq_tac_in H2. punfold H2. inversion H2. 
coseq_tac_in H2. punfold H2. inversion H2. subst. 
coseq_tac. pfold. constructor. auto. 
inversion H8. left. apply/H. 2: { eauto. } eauto. done. right. auto. 
Qed.

Lemma monotone_comp1 : forall (A : Type) (F0 F1 : (A  -> Prop) -> (A  -> Prop)),  monotone1 F0 -> monotone1 F1 -> monotone1 (F0 \o F1). 
Proof. intros. move => x0 x1. intros. apply/H. eauto. eauto. 
Qed.


Lemma monotone_comp : forall (A B : Type) (F0 F1 : (A -> B -> Prop) -> (A -> B -> Prop)),  monotone2 F0 -> monotone2 F1 -> monotone2 (F0 \o F1). 
Proof. intros. move => x0 x1. intros. apply/H. eauto. eauto.  Qed. 


Hint Resolve  monotone_comp1 monotone_comp : paco. 

Definition idemp {A : Type} (f : A -> A) := forall a, f (f a) = f a. 



Lemma rep_rem2 : forall (A : eqType) (l l0 l1 : seq A) a, a \notin l -> (forall x, x \in l0 -> x \in l1) ->a \in rep_rem l l0  -> a \in rep_rem l l1.
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
Qed.

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
Qed.

Ltac con := constructor. 

Definition comap' {A B : Type} (f0 : coseq A ->  coseq B) (f : A -> B) (l : coseq A) := 
match l with 
| conil => conil 
| cocons a l' => cocons (f a) (f0 l')
end. 

Lemma comap'_eq : forall A B (f0 : coseq A -> coseq B) f l, comap' f0 f l = (match l with 
| conil => conil 
| cocons a l' => cocons (f a) (f0 l')
end). 
Proof. 
intros. rewrite /comap'. done. 
Qed.

(*Fix f before defining cofixpoint to make g_to_gc pass productivity check*)
Definition comap {A B : Type} (f : A -> B) := 
 cofix comap (l : coseq A) : coseq B := comap' comap f l. 


Lemma comap_eq : forall A B (f : A -> B) l, comap f l = comap' (comap f) f l. 
Proof. 
intros. rewrite /comap.  rewrite (coseq_match  (_ l)). 
destruct (comap' (cofix comap (l0 : coseq A) : coseq B := comap' comap f l0) f l). done. done. 
Qed.

Let comap_eqs := (comap'_eq, comap_eq). 


Variant ApplyF {A B : Type} (fa : A -> A) (fb : B -> B) (R : A -> B  -> Prop) : A -> B  -> Prop :=
 Unf_intro a b :  R (fa a) (fb b) -> ApplyF fa fb R a b.

Lemma ApplyF_mon A B fa fb  : monotone2 (@ApplyF A B fa fb). 
Proof. intro. intros. inv IN. con. eauto. Qed. 

Hint Resolve ApplyF_mon : paco.

Variant ApplyF1 {A : Type} (f : A -> A) (R : A ->  Prop) : A  -> Prop :=
    Unf1_intro : forall (a : A), R (f a) -> ApplyF1 f R a.
Hint Constructors ApplyF1.

Lemma ApplyF1_mon (A : Type) (f : A -> A)  : monotone1 (ApplyF1 f).   
Proof. intro. intros. con. inv IN. eauto.
Qed. 

Hint Resolve ApplyF1_mon : paco. 


Notation R_pair := (fun P p => P p.1 p.2).  

Lemma coerce_forall : forall (A B : Type) (P : A -> B -> Prop) l0 l1, (to_coseq l0) << (forall_gen P) >> l1 -> exists l', size l0 = size l' /\ to_coseq l' = l1 /\ Forall (R_pair P) (zip l0 l'). 
Proof. 
move => A B P. 
elim;intros. rewrite coeq in H. uis H. exists nil. ssa. rewrite coeq //=.
uis H0. rewrite coeq in H2. done. 
rewrite coeq in H1. inv H1. apply H in H3. destruct H3. ssa.  
exists (e1::x). ssa. rewrite !coeq. f_equal. done. 
Qed.

Lemma coerce_forall2 : forall (A B : Type) (P : A -> B -> Prop) l0 l1,  size l0 = size l1 -> Forall (R_pair P) (zip l0 l1) -> (to_coseq l0) << (forall_gen P) >> (to_coseq l1).
Proof. 
move => A B P. 
elim;intros. destruct l1. rewrite !coeq. auto.  done. 
destruct l1. done. rewrite !coeq. inv H1.  simpl in *. pc. 
Qed.

Lemma Forall_ForallC : forall (A B : Type) (l0 : seq A) (l1 : seq B) P, size l0 = size l1 -> Forall (R_pair P) (zip l0 l1)  -> (to_coseq l0) << (forall_gen P) >> (to_coseq l1). 
Proof. 
move => A B. elim. case. intros. rewrite !coeq. auto.
done. 
move => a l IH [];first done. intros. rewrite !coeq.  inv H0.
pc.  
Qed.

Lemma In_zip : forall (A B : Type) (a : A) l (l1 : seq B), In a l -> size l = size l1 -> exists a1, In a1 l1 /\ In (a,a1) (zip l l1). 
Proof. 
move => A B a. elim=> [] //=.
move => a0 l IH [] //= a1 l0 [ -> [Hsize ] |  Hin [Hsize] ].
- exists a1=>//=. ssa. 
- move : (IH _ Hin Hsize)=>[] x [] Hin2 Hin3. exists x. ssa. 
Qed.

Lemma In_zip2 : forall (A B : Type) (a1 : B) (l : seq A) (l1 : seq B), In a1 l1 -> size l = size l1 -> exists a, In a l /\ In (a,a1) (zip l l1). 
Proof. 
move => A B a1. elim=> [] //=. move=>[] //=.
move => a l IH [] //= a0 l0 [ -> [Hsize ] |  Hin [Hsize] ].
- exists a=>//=. ssa. 
- move : (IH _ Hin Hsize)=>[] x [] Hin2 Hin3. exists x. ssa. 
Qed.

Lemma to_coseq_inj : forall  (A : Type) (l0 l1 : seq A), to_coseq l0 = to_coseq l1 -> l0 = l1. 
Proof. 
move => A. elim. case. done. intros. rewrite !coeq in H. done. 
intros. destruct l1. rewrite !coeq in H0. done.
rewrite !coeq in H0.  inv H0. 
f_equal. auto. 
Qed.



Ltac injt := match goal with 
                   | [ H : to_coseq _ = to_coseq _ |- _ ] => apply to_coseq_inj in H;subst 
                  end.


Definition Forall_consP := List.Forall_cons_iff.
Definition ForallP := List.Forall_forall.
Ltac forallApp H1 H2 := move : H1; move/[dup]/ForallP  => /(_ _ H2). 
