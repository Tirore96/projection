This repository is the Coq mechanisation that accompanies the paper "Sound and Complete Projection of Multi Party Session Types". 
We now describe the conceptual mapping from the paper to the code 

Section 2 (Global Types, Local Types, and Standard Projection):
Global and Local type syntax: theories/Syntax.v


Notes:
Difference Unravele (paper and main theorem) and Unravele2 (used internally)
to_coseq trick (Finite, why we need it)

Lemma 27, should have ( (has_tree g) && (pair_next_rec p nil (project_predP p) true (g,e))) on the right hand side

Unravelg <-> Unravelg2