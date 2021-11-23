-module(ff).
-export([sub/3, add/3, mul/3, divide/3, pow/3]).

mod(X,Y)->(X rem Y + Y) rem Y.
symetric_view([], _) -> [];
symetric_view([H|T], Y) ->
    [symetric_view(H, Y)|
     symetric_view(T, Y)];
symetric_view(X, Y) ->
    Y2 = Y div 2,
    if
        (X > Y2) -> X - Y;
        true -> X
    end.
sub(A, B, Base) ->
    mod(A - B, Base).
neg(A, Base) ->
    sub(0, A, Base).
add(A, B, Base) ->
    mod(A + B, Base).
mul(A, B, Base) ->
    mod(A * B, Base).
divide(A, B, N) ->
    B2 = inverse(B, N),
    mul(A, B2, N).
pow(_, 0, _) -> 1;
pow(A, B, N) ->
    basics:lrpow(A, B, N).
add_all([A], _) -> A;
add_all([A, B|T], Base) -> 
    add_all([add(A, B, Base)|T], Base).
inverse(A, Base) ->
    basics:inverse(A, Base).
