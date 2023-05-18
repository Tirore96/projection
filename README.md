This repository is the Coq mechanisation that accompanies the paper "Sound and Complete Projection of Global Types". The code has been tested with Coq version 8.15.2.

# Folder structure
The code is located in the theories/ folder with the following structure

utils.v : Miscellaneous definitions and proofs\
IndTypes/axioms.v, unscoped.v, syntax.v : Generated by autosubst to support substitution\
IndTypes/elimination.v : Induction principle for global and local types\
CoTypes/coGlobal.v : Coinductive Global Types\
CoTypes/coLocal.v : Coinductive Local Types\
CoTypes/coProj.v : Coinductive Projection\
Examples/* : Examples 5, 6, 20 and 28 from the paper\
Projection/intermediateProj.v : Intermediate Projection\
Projection/projectDecide.v : Decision procedure for intermediate projection\
Projection/indProj.v : Computable Inductive Projection, soundness and completeness proofs

# Mapping from paper to code
Section 2 (Global Types, Local Types, and Standard Projection) -> IndTypes/\
Section 3 (Projection on Coinductive Types) -> CoTypes/\
Section 4 (Projection on Inductive Types: Soundness and Completeness) -> Projection/IndProj.v\
Section 5 (Deciding Projectability) -> Projection/Intermediateproj.v, Projection/ProjectDecide.v

# Locations of definitions, lemmas, corollaries and theorems
Definition 1 ---> IndTypes/syntax.v (gType,lType)\
Definition 2 ---> coTypes/coGlobal.v (gcType), coTypes/coLocal.v (lcType)\
Definition 3 ---> coTypes/coGlobal.v (gUnravel), coTypes/coLocal.v (lUnravel)\
Proposition 4 ---> CoTypes/coGlobal.v (proposition_4)\
Definition 7 ---> Projection/indProj.v (proj)\
Definition 8 ---> Projection/indProj.v (trans)\
Definition 9 ---> Projection/indProj.v (projectable)\
Theorem 10 ---> Projection/indProj.v (proj_sound)\
Definition 11 ---> CoTypes/coGlobal.v (gtocoind), CoTypes/coLlobal.v (ltocoind)\
Lemma 12 ---> Projection/indProj.v (unravelling_of_trans)\
Lemma 13 ---> Projection/indProj.v (trans_as_projection)\
Theorem 14 ---> Projection/indProj.v (proj_complete)\
Lemma 15 ---> Projection/intermediateProj.v (ICProject_iff)\
Corrolary 16 ---> Projection/indProj.v (projectable_iff_intermed)\
Definition 17 ---> We use no generic graph structure, only concrete instantiations in definitions 18 and 24\
Definition 18 ---> CoTypes/coGlobal.v (sat1), Projection/projDecide.v (sat2) (remark: More general formulation than presented in the paper)\
Definition 19 ---> CoTypes/coGlobal.v (graph of g is (enumg g,nextg_unf), see Remark 2 below)\
Lemma 21 ---> CoTypes/coGlobal.v (enumg_closed_nextg_unf)\
Definition 22 ---> CoTypes/coGlobal.v (UnravelPred)\
Lemma 23 ---> CoTypes/coGlobal.v (dec_gUnravels)\
Definition 24 ---> Projection/projectDecide.v (g_top_act, remark: does not do unfolding, combined with PL_p from Def. 26)\
Definition 25 ---> Projection/projectDecide.v (e_top_act, remark: does not do unfolding)\
Definition 27 ---> Projection/projectDecide.v (graph of (g,t) is (enumge (g,t), nextge_unf))\
Definition 29 ---> Projection/projectDecide.v (project_predP)\
Theorem 30 ---> Projection/projectDecide.v (projectb_iff)\
Corollary 31 ---> Projection/indProj.v (decide_projectable)


# Syntax representation
The syntax of inductive global types represented by the gType, is mapped to the paper presentation the following way
a -> b : k<U>.g ----> GMsg (Action a b k) U g
a -> b : k \{ L0:G0...Ln:Gn \} ----> GBranch (Action a b k) [G0,..,Gn] (where [..] is inductive list)
\mu t.g ----> GRec g (De Brujin indices means the binder is not named)
t ----> GVar n
end ----> GEnd

The syntax of inductive local types does unlike the paper presentation use directions (Sd and Rd of type dir, to indicate sending/receving messaging and branching communications).

The representation of (Co)-inductive local type and coinductive global types are similar, with the exception that coinductive branching uses a coinductive list (rather that inductive list as seen above). This is due to a limitation of Coq's productivity checker disallowing a nested fixpoint inside a cofixpoint when defining tocoind. To ensure lists in coinductive types are finite, we define a coercion (to_coseq : seq A -> coseq A) and use the Finite predicate (in CoTypes/coProj.v) to assert all branches gcs is of shape (to_coseq gs).

a -> b :^c k \{ L0:G0^c...Ln:Gn^c \} ----> GCBranch (Action a b k) [G0,..,Gn] (where [..] is inductive list)


# Other remarks

1. The unraveling relation from Section 3 is represnted by gUnravel (in CoTypes/coGlobal) and lUnravel (in CoTypes/coLocal). The relations gUnravel2 and lUnravel2 are however more convenient (and proved equivalent to their counterparts) so nearly all lemmas (except for the main ones) are stated in terms of these relations.

2. The graph construction in Section 5 consisting of triple (states,d,delta) is used in CoTypes/coGlobal.v for deciding if a global type unravels to something and Project/projectDecide for deciding intermediate projection. In both cases we represent these graphs' delta and d functions simply as a function computing the list of continations (nextg_unf and nextge_unf respectively).

3. sat has two implementations (sat1 and sat2), respectively for deciding unravelling and intermediate projection. For both implementations, their type differ slightly from how sat is presented in the paper by using a predicate P of type A -> seq A -> A, rather than simply being A -> bool. This makes the definition more general, but so the function is only used in the way shown in the paper. 

