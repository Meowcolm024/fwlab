
lives(agatha).
lives(butler).
lives(charles).

richer(A, B) :- lives(A), lives(B), \+ A=B.

hate(charles, B) :- lives(B), \+ hate(agatha, B).
hate(agatha, B) :- lives(B), \+ B=butler.
hate(butler, B) :- lives(B), hate(agatha, B), \+ richer(B, agatha).

kill(A, B) :-
    lives(A),
    lives(B),
    hate(A, B),
    \+ richer(A, B).
