:-[syn3d].

constant_functions(_,[],[]).

combine_expression_values(_,L,R,O1,O2,(L<R),O):-bitless(O1,O2,O).
combine_expression_values(NbOfBits,L,R,O1,O2,L=R,O):-biteq(NbOfBits,O1,O2,O).
