male(namihei). male(katsuo). male(tara). male(masuo).

female(fune). female(wakame). female(sazae).

father(masuo, tara). father(namihei, sazae). father(namihei, katsuo).
father(namihei, wakame).

mother(sazae, tara). mother(fune, sazae). mother(fune, katsuo).
mother(fune, wakame).

parents(X, Y) :- father(X, Y). parents(X, Y) :- mother(X, Y).
son(X, Y) :- parents(Y, X), male(X).
daughter(X, Y) :- parents(Y, X), female(X).
grandfather(X, Y) :- parents(Z, Y), father(X, Z).
grandmother(X, Y) :- parents(Z, Y), mother(X, Z).
