verify(InputFileName) :- see(InputFileName),
    read(Prems), read(Goal), read(Proof),
    seen,
    valid_proof(Prems, Goal, Proof).    

% BOXES
% Check for box. Base case
check_box(_,[],_).
% Check if Head is a list (box in a box)   
check_box(Prems, [Head|_], FullCheckedProof) :- check_box(Prems, Head, [Head| FullCheckedProof]). 
% Check if Head is assumption and that there aren't any other assumptions in the same box.                                            
check_box(Prems, [Head|Tail], FullCheckedProof) :- Head = [_, _,assumption], not(member([_,_ ,assumption],Tail)), check_box(Prems, Tail, [Head| FullCheckedProof]).                  
% Checks line for the box. 
check_box(Prems, [Head|Tail], FullCheckedProof) :-  check_line(Prems, Head,FullCheckedProof), check_box(Prems, Tail, [Head| FullCheckedProof]).

% Finds a box in FullCheckedProof
find_box(A,[H | _], H) :- member([A,_,_], H), !.
find_box(A,[_ | T], BoxList) :- find_box(A,T, BoxList). 

% START OF ALGORITHM
% Check if the last line of proof is Goal, and then check if proof is correct. This means the proof is valid. 
valid_proof(Prems, Goal, Proof) :- check_goal_equal_to_proof(Goal,Proof), check_proof(Prems, Proof, []).

% Go to the last line in proof and check if equal to Goal
last1(X,Y) :- append(_,[X],Y).
nth1(N,L,E) :- nth1(1,N,L,E).
nth1(N,N,[H|_],H).
nth1(K,N,[_|T],H) :- K1 is K+1, nth1(K1,N,T,H).

check_goal_equal_to_proof(Goal, Proof) :- last1(Y, Proof), nth1(2, Y, Z), Goal = Z.

% PROOF CHECKING
% Check proof. Base case
check_proof(_,[],[_|_]). 
% Check if current line is a box. If true, go to next line
check_proof(Prems, [Head|Tail], FullCheckedProof) :-  check_box(Prems, Head, FullCheckedProof), check_proof(Prems,Tail, [Head | FullCheckedProof]).
% Check a line of Proof to see if it is valid. If true, go to next line
check_proof(Prems, [Head|Tail], FullCheckedProof) :- check_line(Prems, Head, FullCheckedProof),
                                                                    check_proof(Prems, Tail, [Head|FullCheckedProof]),!.

% Proof is split up into [RowNumber, rule, nameOfRule]
% premise. 
check_line(Prems, [_, X, premise], _) :- member(X,Prems).

% copy
check_line(_, [_,X, copy(A)], FullCheckedProof) :- member([A,X,_], FullCheckedProof).

% andint(A,B) 
check_line(_, [_,and(X,Y),andint(A,B)], FullCheckedProof) :- member([A,X,_],FullCheckedProof), member([B,Y,_],FullCheckedProof).

% andel1(A) 
check_line(_, [_,X,andel1(A)], FullCheckedProof) :- member([A,and(X,_),_], FullCheckedProof).

% andel2(A) 
check_line(_, [_,X,andel2(B)],FullCheckedProof) :- member([B,and(_,X),_],FullCheckedProof).
                                                                                                     
% orint1(A)                                       
check_line(_, [_,or(X,_),orint1(A)], FullCheckedProof) :- member([A,X,_], FullCheckedProof).
                                                                                                              
% orint2(A) 
check_line(_, [_,or(_,X),orint2(A)], FullCheckedProof) :- member([A,X,_], FullCheckedProof). 
                                                                                                               

% orel(A,B,C,D,E)  (Box)
check_line(_, [_, X, orel(A,B,C,D,E)],FullCheckedProof) :- find_box(B,FullCheckedProof, BoxForY),
                                                                      find_box(D,FullCheckedProof, BoxForV), 
                                                                      member([A,or(Y,V), _], FullCheckedProof),        
                                                                      member([B,Y,assumption], BoxForY),
                                                                      member([C,X,_], BoxForY),
                                                                      member([D,V,assumption], BoxForV),
                                                                      member([E,X,_], BoxForV).
                                                                                                             
% impint(A,B) (Box)
check_line(_, [_, imp(X,Y), impint(A,B)],FullCheckedProof) :- find_box(A, FullCheckedProof, BoxList),
                                                                          member([A,X,assumption], BoxList), 
                                                                          member([B,Y,_], BoxList). 
                                                                                      
% impel(A,B) 
check_line(_, [_, Y, impel(A,B)],FullCheckedProof) :- member([A,X,_],FullCheckedProof), 
                                                          member([B,imp(X,Y),_],FullCheckedProof).                                                                                                         

% negint(A,B) (Box) 
check_line(_, [_, neg(X), negint(A,B)],FullCheckedProof) :- find_box(A, FullCheckedProof, BoxList), 
                                                                      member([A,X, assumption],BoxList),
                                                                        member([B,cont, _],BoxList).                                                                                                            

% negel(A,B) 
check_line(_, [_, cont, negel(A,B)],FullCheckedProof) :- member([A,X, _],FullCheckedProof),
                                                             member([B,neg(X), _], FullCheckedProof).                                                                                                            

% contel(A) 
check_line(_, [_, _, contel(A)],FullCheckedProof) :- member([A, cont, _], FullCheckedProof).

% negnegint(A) 
check_line(_, [_, neg(neg(X)), negnegint(A)],FullCheckedProof) :-member([A, X, _], FullCheckedProof).
                                                                                                                     
% negnegel(A) 
check_line(_, [_, X, negnegel(A)],FullCheckedProof) :- member([A,neg(neg(X)),_], FullCheckedProof).

% mt(A,B)
check_line(_, [_, neg(X), mt(A,B)],FullCheckedProof) :- member([A, imp(X,Y),_], FullCheckedProof), member([B,neg(Y),_], FullCheckedProof).

% pbc(A,B) (Box)
check_line(_, [_, X, pbc(A,B)],FullCheckedProof) :- find_box(A, FullCheckedProof, BoxList), 
                                                              member([A, neg(X), assumption], BoxList), 
                                                              member([B, cont, _], BoxList).

%lem(A,B) (tautologi)
check_line(_, A,_) :- A = [_,or(X,neg(X)),lem].

/* 
[ [1, imp(p,q),   premise], HEAD - Fail
  [ HEAD - True
    [2, p,        assumption],    A
    [3, q,        impel(2,1)],    
    [4, neg(q),   premise],
    [5, cont,     negel(3,4)]
  ],
  [6, neg(p),     negint(2,5)]
]. */
