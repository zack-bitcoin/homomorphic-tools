-module(elliptic).
-export([test/1, make/3, addition/3, 
         multiplication/3]).

-record(curve, {a, b, g, n, p}).

mod(X,Y)->(X rem Y + Y) rem Y.

on_curve(A, B, X, Y, P) ->
    %check that the point is on the curve.
    %y^2 = x^3 + A*x + B
    0 == mod((X*X*X) + (A*X) + B - (Y*Y), P).
    

make(A, B, X, Y, P) ->
    true = on_curve(A, B, X, Y, P),

    %check that the field is big enough to conform to elliptic curve logic.
    true = P>3,

    %check that discriminate is not 0, so the curve has no cusps.
    false = mod((4*A*A*A) + (27*B*B), P) == 0,

    #curve{a = A, b = B, g = {X, Y}, p = P}.
make(A, B, P) ->
    {X, Y} = find_point(A, B, P),
    make(A, B, X, Y, P).

x_table(_, _, P, P) -> [];
x_table(A, B, T, P) -> 
    [{((T*T*T) + (A*T) + B) rem P, T}|
     x_table(A, B, T+1, P)].
y_table(P, P) -> [];
y_table(T, P) -> 
    [{(T*T) rem P, T}|y_table(T+1, P)].

find_match2(A, [{A, Y}|_]) ->
    {true, Y};
find_match2(_, []) ->
    {false, error};
find_match2(A, [_|Ys]) ->
    find_match2(A, Ys).
find_match([{A, X}|Xs], Ys) ->
    {B, Y} = find_match2(A, Ys),
    if
        B -> {X, Y};
        true -> find_match(Xs, Ys)
    end.
             
    
find_point(A, B, P) ->
    %y^2 = x^3 + A*x + B
    Xs = x_table(A, B, 1, P),
    Ys = y_table(1, P),
    find_match(Xs, Ys).
%Right = ((X*X*X) + (A*X) + B) rem P,
    %needs a formula for square root.
%    ok.
    

addition(infinity, P2, _) -> P2;
addition(P1, infinity, _) -> P1;
addition(P1, P2, E) ->
    {X1, Y1} = P1,
    {X2, Y2} = P2,
    #curve{
            a = A,
            p = N
         } = E,
    if
        (X1 == X2) and (not(Y1 == Y2)) ->
            infinity;
        true ->
            M = if
                    ((P1 == P2) 
                     and (not(Y1 == 0))) ->
                        mod(((3*X1*X1)+A) * basics:inverse(2*Y1, N), N);
                    (not (X1 == X2)) ->
                        mod((Y2 - Y1) * basics:inverse(mod(X2 - X1, N), N), N)
                end, 
            X3 = mod(mod(M*M, N) - X1 - X2, N),
            Y3 = mod(mod(M * (X1 - X3), N) - Y1, N),
            {X3, Y3}
    end.

%multiplication(infinity, _, _) ->
%    infinity;
multiplication(P1, 0, E) ->
    io:fwrite("can't multiply by zero\n"),
    error;
multiplication(P1, X, E) 
  when ((X rem 2) == 0) ->
    multiplication(addition(P1, P1, E),
                   X div 2, E);
multiplication(P1, 1, _) -> 
    P1;
multiplication(P1, X, E) ->
    addition(P1,
             multiplication(P1, X-1, E),
             E).

hex_digit_to_int("A") -> 10;
hex_digit_to_int("B") -> 11;
hex_digit_to_int("C") -> 12;
hex_digit_to_int("D") -> 13;
hex_digit_to_int("E") -> 14;
hex_digit_to_int("F") -> 15;
hex_digit_to_int(X) -> 
    list_to_integer(X).

hex_to_int(L) ->
    hex_to_int2(L, 0).
hex_to_int2("", A) -> A;
hex_to_int2([H|T], A) -> 
    A2 = (A*16) + hex_digit_to_int([H]),
    hex_to_int2(T, A2).

mul_all(_, L, L, _) -> [];
mul_all(G, I, L, E) ->
    V = multiplication(G, I, E),
    case V of
        infinity -> io:fwrite("infinity \n");
        {X, Y} ->
            io:fwrite(integer_to_list(X)),
            io:fwrite(" "),
            io:fwrite(integer_to_list(Y)),
            io:fwrite("\n")
    end,
    [V|
     mul_all(G, I+1, L, E)].
    
test(1) ->    
    %P = hex_to_int("FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F"),
    A = 0,
    B = 7,
    P = 13,
    {X, Y} = find_point(A, B, P),
    
    E = make(A, B, X, Y, P),
    #curve{
            g = G
          } = E,
    
    {
      multiplication(G, 1, E),
      multiplication(G, 31, E),
      multiplication(G, 32, E),
      mul_all(G, 1, 100, E)
    };
test(2) ->
    A = 2,
    B = 3,
    P = 7,
    {X, Y} = find_point(A, B, P),
    E = make(A, B, X, Y, P),
    #curve{
            g = G
          } = E,
    {3, 6} = addition({2, 1}, {2, 1}, E),
    infinity = addition({2, 1}, {2, 6}, E),
    {2, 6} = addition({2, 1}, {3, 1}, E),
    {6, 0} = addition({2, 1}, {3, 6}, E),
    mul_all(G, 1, 20, E);

test(3) ->
    %FFFFFFFF FFFFFFFF FFFFFFFF FFFFFFFF FFFFFFFF FFFFFFFF FFFFFFFE FFFFFC2F
%2256 - 232 - 29 - 28 - 27 - 26 - 24 - 1
    P=det_pow(2, 256) -
        det_pow(2, 32) - 
        det_pow(2, 9) -
        det_pow(2, 8) -
        det_pow(2, 7) -
        det_pow(2, 6) -
        det_pow(2, 4) -
        1,
    A = 0,
    B = 7,
    X = hex_to_int("79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798"),
    Y = hex_to_int("483ADA7726A3C4655DA4FBFC0E1108A8FD17B448A68554199C47D08FFB10D4B8"),
    N = hex_to_int("FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141"),%group order.
    E = make(A, B, X, Y, P),

    gen_point(E).

gen_point(E) ->
    #curve{
           p = P,
           b = B,
           a = A
          } = E,
    X = random:uniform(det_pow(2, 256))-1,
    Ysquare = mod(mod(X*mod(X*X, P), P) - (A*X) + B, P),
    Pident = (P+1) div 4,
    Y = basics:rlpow(Ysquare, Pident, P),
    Check = on_curve(A, B, X, Y, P),
    if
        Check -> {X, Y};
        true -> 
            io:fwrite("failed\n"),
            gen_point(E)
    end.
            


det_pow(0, _) -> 0;
det_pow(_, 0) -> 1;
det_pow(A, 1) -> A;
det_pow(A, N) when ((N rem 2) == 0) -> 
    det_pow(A*A, N div 2);
det_pow(A, N) -> 
    A*det_pow(A, N-1).

