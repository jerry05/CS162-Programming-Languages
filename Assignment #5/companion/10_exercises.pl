% Write out whether or not the following queries are true or
% false, replacing `???` where appropriate.
% If a query is true and involves variable instantiations, then write out
% all possible variable instantiations which make the query
% true.  Some have already been done for you, to give an
% example of the expected format, and to provide additional examples.
% If you wish, you may simply
% copy and paste the output of SWI-PL here directly; we will be grading
% this by hand, so the output format isn't important.

% QUERY: 1 = 1.
% ANSWER: true

% QUERY: 2 = 2.
% ANSWER: true

% QUERY: 1 = 2.
% ANSWER: false

% QUERY: 2 = 3.
% ANSWER: false

% QUERY: X = 1.
% ANSWER: X = 1

% QUERY: X = 2.
% ANSWER: X = 2

% QUERY: 1 = X.
% ANSWER: X = 1

% QUERY: 2 = X.
% ANSWER: X = 2

% QUERY: foo = foo.
% ANSWER: true

% QUERY: bar = bar.
% ANSWER: true

% QUERY: foo = bar.
% ANSWER: false

% QUERY: bar = baz.
% ANSWER: false

% QUERY: X = foo.
% ANSWER: X = foo

% QUERY: bar = X.
% ANSWER: X = bar

% QUERY: X = X.
% ANSWER: true

% QUERY: X = Y.
% ANSWER: X = Y

% QUERY: X = 1, X = Y.
% ANSWER: (X = Y, Y = 1)

% QUERY: a(X) = a(1).
% ANSWER: X = 1

% QUERY: b(X) = b(1).
% ANSWER: X = 1

% QUERY: a(X, Y) = a(1).
% ANSWER: false

% QUERY: a(1) = a(X, Y).
% ANSWER: false

% QUERY: a(X) = b(1).
% ANSWER: false

% QUERY: b(1) = c(1).
% ANSWER: false

% QUERY: a(b,c) = a(X,Y).
% ANSWER: (X = b, Y = c)

% QUERY: a(X,c(d,X)) = a(2,c(d,Y)).
% ANSWER: (X = Y, Y = 2)

% QUERY: a(X,Y) = a(b(c,Y),Z).
% ANSWER: (X = b(c,Z), Y = Z)

% QUERY: tree(left, root, Right) = tree(left, root, tree(a, b, tree(c, d, e))).
% ANSWER: Right = tree(a,b,tree(c,d,e))
