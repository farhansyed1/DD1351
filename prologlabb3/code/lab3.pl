% Abhinav Sasikumar and Farhan Syed 2022-12-14
% For SICStus, uncomment line below: (needed for member/2)
use_module(library(lists)).
% Load model, initial state and formula from file.
verify(Input) :-
    see(Input), read(T), read(L), read(S), read(F), seen,
    check(T, L, S, [], F).

    % check(T, L, S, U, F)
    % T - The transitions in form of adjacency lists
    % L - The labeling
    % S - Current state
    % U - Currently recorded states
    % F - CTL Formula to check.
    %
    % Should evaluate to true iff the sequent below is valid.
    %
    % (T,L), S |- F
    % U
    % To execute: consult('your_file.pl'). verify('input.txt').
    % Literals
% p, checks whether a label is true in a given state
check(_, L, S, [], Phi) :- member([S,Label] , L), member(Phi, Label). % Checks if Phi exists in the label list of S

% neg P, checks whether a label is false in a given state
check(_, L, S, [], neg(Phi)) :- member([S, Label] , L), \+member(Phi, Label). %  Checks if Phi does not exist in the label list of S

%and, checks whether two labels are true in a given state
check(T, L, S, [], and(Phi,Psi)) :- check(T, L, S, [], Phi), check(T,L,S,[], Psi),!. % Checks if both Phi and Psi are true in the given state. 

% Or, checks whether either label s true in a given state
check(T,L,S, [], or(Phi,Psi)) :-  check(T, L, S, [], Phi); check(T, L, S, [], Psi), !. % Checks whether either Psi or Phi is true in the given state.

% AX Phi - In every next state, phi is true.
check(T,L,S, U, ax(Phi)) :-   member([S,Adjacent], T), ax_check(T,L,Adjacent,U,Phi). % Takes out all adjacent nodes to S and checks them using the help function. 

ax_check(_,_,[],_,_).
ax_check(T,L,[S|Tail],U, Phi) :- check(T,L,S,U,Phi),!,ax_check(T,L,Tail,U,Phi). % Recursively checks whether Phi is true in each state

% EX Phi- There exists a next state where Phi is true
check(T,L,S,U,ex(Phi)) :- member([S, Adjacent],T), member(A, Adjacent), check(T, L, A, U, Phi). % Checks whether the state exists in the adjacency list and whether there exists a neighbour such that the label is valid.

% AG Phi - Phi is true for all paths
check(_,_,S,U, ag(_)) :- member(S,U).       % Base case: If Phi has been visited, then we do nothing.  
check(T,L,S,U, ag(Phi)) :- check(T,L,S,[], Phi), check(T,L,S,[S| U], ax(ag(Phi))). %  CHecks if Phi is true in the current state as well as whether In every next state for each path, phi is true.



% EG Phi - There exists a path where Phi is always true
check(_,_,S,U, eg(_)) :- member(S,U), !.  % Base case: If Phi has been visited, then we cut the recursion. 
check(T,L,S,U, eg(Phi)) :- check(T, L, S, [], Phi), check(T, L, S, [S | U], ex(eg(Phi))). % Checks if Phi is true in the current state as well as whether there exists a next state where Phi will be true recursively


% EF  Phi - There exists a path such that there is some future state where Phi will be true in the future

check(T,L,S,U, ef(Phi)) :- \+member(S,U), check(T,L, S, [], Phi). % Base case: If phi has not been visited, then we check whether the state is true in S. 

check(T,L,S,U, ef(Phi)) :- \+ member(S,U), check(T,L,S,[S|U], ex(ef(Phi))). %  Checks that for each path that can be taken from S, that there exists a next state where ef(Phi) will be true

% AF Phi - For all paths Phi will be true in the future. 


check(T, L, S, U, af(Phi)) :- \+member(S,U), check(T,L,S,[], Phi). % Base case: If phi has not been visited, then we check whether the state is true in S.
check(T,L,S,U, af(Phi)) :- \+ member(S,U), check(T,L,S,[S| U], ax(af(Phi))). % Checks that for each path that can be taken from S, that in every next state AF(Phi) will be true


