% Definitioner
append1([],L,L).
append1([H|T],L,[H|R]) :- append1(T,L,R).

append1El(X, [], [X]).
append1El(X, [H | T], [H | Y]) :-
           append1El(X, T, Y).

length1([],0).
length1([_|T],N) :- length1(T,N1), N is N1+1.

nth1(N,L,E) :- nth1(1,N,L,E).
nth1(N,N,[H|_],H).
nth1(K,N,[_|T],H) :- K1 is K+1, nth1(K1,N,T,H).

subset1([], []).
subset1([H|T], [H|R]) :- subset1(T, R).
subset1([_|T], R) :- subset1(T, R).

select1(X,[X|T],T).
select1(X,[Y|T],[Y|R]) :- select1(X,T,R).

member1(X,L) :- select1(X,L,_).
memberchk1(X,L) :- select1(X,L,_), !.

list([]).
list([H|T]) :- list(T).

% Uppgift 1
/* 
| ?- T=f(a,Y,Z), T=f(X,X,b).

T = f(a,a,b)
X = a
Y = a
Z = b

Dessa bindningar måste göras för att dessa två satser ska vara lika

*/ 

% Uppgift 2
remove_duplicates([],Ret) :- list(Ret), !.
remove_duplicates([Head | Tail], Ret) :- memberchk1(Head, Ret), !, remove_duplicates(Tail, Ret).
remove_duplicates([Head | Tail], [Ret | Head]) :- remove_duplicates(Tail, Ret).

% Uppgift 3
createPrefix(X, Y) :- append1(Y,_,X).
%Y är en prefix till X om vi kan appenda någon annan lista till Y så att vi får X

% Exempel
/* createPrefix([2,3,4],X).
X = [] ;
X = [2] ;
X = [2, 3] ;
X = [2, 3, 4] ;
*/ 

partstring([Head|Tail], [Head|RetTail], L) :- createPrefix(Tail, RetTail), length1([Tail|RetTail], L). % vi skapar alla prefixes som börjar med 1. (returnar samma head). Ger 1, [1,2], [1,2,3] osv
partstring([_|Tail], RetTail, L) :- partstring(Tail,RetTail,L), length1(RetTail, L).               % Vi går till nästa head, vilket blir 2. Vi kör övre raden igen men med [2,3,4] som input. 


%Uppgift 4

/*  Stockholm --- Paris
     |              |
     |              |
     London  ---- Rom   --- Berlin
                    |
                    | 
                    New York 

*/

node(stockholm, [london,paris]).
node(london,[stockholm,rom]).
node(paris,[stockholm,rom]).
node(rom,[london,paris,newyork,berlin]).
node(berlin,[rom]).
node(newyork,[rom]).

reverselist1([],[]).
reverselist1([Head],[Head]).
reverselist1([Head|Tail], Return) :- reverselist1(Tail,R),!, append1(R, [Head], Return).

pathfinder(X,Y,R) :- pathfinder1(X,Y,[X],NonReversed), reverselist1(NonReversed,R).
pathfinder1(Start,Start,R,R).
pathfinder1(Start,End,Visited,R) :- node(Start,Grannar), node(End,_),
                                    select(X,Grannar,_), 
                                    \+(memberchk1(X,Visited)),
                                    pathfinder1(X,End,[X | Visited], R).

