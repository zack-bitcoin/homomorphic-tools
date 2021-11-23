-module(secp256k1).
-export([test/1, make/0, addition/3, 
         multiplication/3, gen_point/1,
         field_prime/1, order/1,
         on_curve/2,
         mod/2,

         to_jacob/1, to_affine/2
]).

-record(curve, {a, b, g, n, p}).
field_prime(C) -> C#curve.p.
order(C) -> C#curve.n.

mod(X,Y)->(X rem Y + Y) rem Y.

on_curve({X, Y}, C) ->
    #curve{a = A, b = B, p = P
         } = C,
    on_curve(A, B, X, Y, P).
on_curve(A, B, X, Y, P) ->
    %check that the point is on the curve.
    %y^2 = x^3 + A*x + B
    0 == mod(mod(mod(X*X, P)*X, P) 
             + mod(A*X, P) 
             + B 
             - mod(Y*Y, P), 
             P).

make(A, B, X, Y, P, N) ->
    #curve{a = A, b = B, g = {X, Y}, 
           p = P, n = N}.

det_pow(0, _) -> 0;
det_pow(_, 0) -> 1;
det_pow(A, 1) -> A;
det_pow(A, N) when ((N rem 2) == 0) -> 
    det_pow(A*A, N div 2);
det_pow(A, N) -> 
    A*det_pow(A, N-1).

make() ->
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
    make(A, B, X, Y, P, N).

to_jacob({X, Y}) ->
    {X, Y, 1}.
to_affine({X, Y, Z}, E) ->
    Base = field_prime(E),
    P2 = ff:mul(Z, Z, Base),
    P3 = ff:mul(Z, P2, Base),
    {ff:divide(X, P2, Base),
     ff:divide(Y, P3, Base)}.

jacob_negate({X, Y, Z}, E) ->
    Base = field_prime(E),
    {X, ff:sub(0, Y, Base), Z}.

jacob_equal({X1, Y1, Z1}, {X2, Y2, Z2}, E) ->
    Base = field_prime(E),
    ZZ = ff:mul(Z1, Z1, Base),
    ZZZ = ff:mul(Z1, ZZ, Base),
    ZZ2 = ff:mul(Z2, Z2, Base),
    ZZZ2 = ff:mul(Z2, ZZ2, Base),
    Check1 = ff:mul(X1, ZZ2, Base) == 
        ff:mul(X2, ZZ, Base),
    Check2 = ff:mul(Y1, ZZZ2, Base) == 
        ff:mul(Y2, ZZZ, Base),
    Check1 and Check2.

jacob_add(P, {0, _, _}, E) -> P;
jacob_add(P, {_, 0, _}, E) -> P;
jacob_add({0, _, _}, P, E) -> P;
jacob_add({_, 0, _}, P, E) -> P;
jacob_add({X1, Y1, Z1}, {X2, Y2, Z2}, E) ->
    %http://hyperelliptic.org/EFD/g1p/auto-shortw-jacobian-0.html#addition-add-2007-bl 
    Base = field_prime(E),
    Z1Z1 = ff:mul(Z1, Z1, Base),
    Z2Z2 = ff:mul(Z2, Z2, Base),
    U1 = ff:mul(X1, Z2Z2, Base),
    U2 = ff:mul(X2, Z1Z1, Base),
    S1 = ff:mul(Y1, ff:mul(Z2, Z2Z2, Base), Base),
    S2 = ff:mul(Y2, ff:mul(Z1, Z1Z1, Base), Base),
    H = ff:sub(U2, U1, Base),
    HH = ff:mul(H, H, Base),
    I = ff:mul(4, HH, Base),
    J = ff:mul(H, I, Base),
    R = ff:mul(2, ff:sub(S2, S1, Base), Base),
    if
        (H == 0) and (R == 0) -> 
            io:fwrite("same point\n"),
            jacob_double({X1, Y1, Z1}, E);
        (H == 0) ->
            jacob_zero();
        true ->
    V = ff:mul(U1, I, Base),
    RR = ff:mul(R, R, Base),
    V2 = ff:mul(2, V, Base),
    X3 = ff:sub(RR, ff:add(J, V2, Base), Base),
    Y3 = ff:sub(
           ff:mul(R, ff:sub(V, X3, Base), Base),
           ff:mul(2, ff:mul(S1, J, Base), Base),
           Base),
    Z1pZ2 = ff:add(Z1, Z2, Base),
    Z3 = ff:mul(
           H, 
           ff:sub(ff:mul(Z1pZ2, Z1pZ2, Base),
                  ff:add(Z1Z1, Z2Z2, Base),
                 Base),
           Base),
    %io:fwrite({X1, Y1, Z1}, {X3, Y3, Z3}),
    {X3, Y3, Z3}
    end.
jacob_double({X1, Y1, Z1}, Curve) ->
    %http://hyperelliptic.org/EFD/g1p/auto-shortw-jacobian-0.html#doubling-dbl-2009-l
    Base = field_prime(Curve),
    A = ff:mul(X1, X1, Base),
    B = ff:mul(Y1, Y1, Base),
    C = ff:mul(B, B, Base),
    D1 = ff:add(X1, B, Base),
    D2 = ff:mul(D1, D1, Base),
    D3 = ff:sub(D2, ff:add(A, C, Base), Base),
    D = ff:mul(2, D3, Base),
    E = ff:mul(3, A, Base),
    F = ff:mul(E, E, Base),
    X3 = ff:sub(F, ff:mul(2, D, Base), Base),
    Y3 = ff:sub(ff:mul(E, ff:sub(D, X3, Base), Base),
                ff:mul(8, C, Base),
                Base),
    Z3 = ff:mul(2, ff:mul(Y1, Z1, Base), Base),
    {X3, Y3, Z3}.

    
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
                        %(A+(3*x1*x1))/(2*Y1)
                        ff:divide(
                          ff:add(
                            A, 
                            ff:mul(
                              3, 
                              ff:mul(X1, X1, N), 
                              N), N),
                          ff:mul(2, Y1, N), N);
                    (not (X1 == X2)) ->
                        %(y2-y1)/(x2-x1)
                        ff:divide(
                          ff:sub(Y2, Y1, N),
                          ff:sub(X2, X1, N), N)
                end, 
            %X3 = mod(mod(M*M, N) - X1 - X2, N),
            X3 = ff:sub(ff:mul(M, M, N),
                        ff:add(X1, X2, N),
                        N),
            %Y3 = mod(mod(M * (X1 - X3), N) - Y1, N),
            Y3 = ff:sub(
                   ff:mul(
                     M, ff:sub(X1, X3, N), N),
                   Y1, N),
            {X3, Y3}
    end.

jacob_zero() -> {0,1,0}.
jacob_mul(P, X, E) ->
    jacob_mul(jacob_zero(), P, X, E).
jacob_mul(_, _, 0, E) -> 
    io:fwrite("zero case\n"),
    jacob_zero();
jacob_mul(_, {_, _, 0}, _, E) -> 
    io:fwrite("zero case 2\n"),
    jacob_zero();
jacob_mul(A, P, X, E) when (X < 0) ->
    jacob_mul(A, jacob_negate(P, E), -X, E);
jacob_mul(A, P, 1, E) -> jacob_add(A, P, E);
jacob_mul(A, P, X, E) 
  when ((X rem 2) == 0) -> 
    jacob_mul(A, jacob_double(P, E),
              X div 2, E);
jacob_mul(A, P, X, E) -> 
    jacob_mul(jacob_add(P, A, E),
              P, X-1, E).

%multiplication(infinity, _, _) ->
%    infinity;
multiplication(P1, 0, E) ->
    infinity;
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

gen_point(E) ->
    #curve{
           p = P
          } = E,
    X = (random:uniform(det_pow(2, 256)) rem P),
    G = gen_point(E, X),
    case G of
        error -> gen_point(E);
        _ -> G
    end.
            
gen_point(E, X) ->
    %based on the decrompression of bitcoin pubkeys algorithm.
    #curve{
           p = P,
           b = B,
           a = A
          } = E,
    Ysquare = mod(mod(X*mod(X*X, P), P) - (A*X) + B, P),
    Pident = (P+1) div 4,
    Y = basics:rlpow(Ysquare, Pident, P),
    Check = on_curve(A, B, X, Y, P),
    if
        Check -> {X, Y};
        true -> 
            %io:fwrite("failed\n"),
            error
    end.
add_times(_, _, _, 0) -> ok;
add_times(A, B, E, N) -> 
    add_times(A, addition(A, B, E), E, N-1).
jacob_add_times(_, _, _, 0) -> ok;
jacob_add_times(A, B, E, N) -> 
    jacob_add_times(A, jacob_add(A, B, E), E, N-1).
square_times(_, _, 0) -> ok;
square_times(A, E, N) -> 
    square_times(addition(A, A, E), E, N-1).
jacob_square_times(_, _, 0) -> ok;
jacob_square_times(A, E, N) -> 
    jacob_square_times(jacob_double(A, E), E, N-1).

test(1) ->
    %testing to see if a random number can be used to make a generator of the group.
    E = make(),
    gen_point(E);
test(2) ->
    E = make(),
    G = gen_point(E),
    T1 = erlang:timestamp(),
    add_times(G, G, E, 500000),
    T2 = erlang:timestamp(),%23 seconds for 1/2 million.
    timer:now_diff(T2, T1);
test(3) ->
    E = make(),
    G = gen_point(E),
    T1 = erlang:timestamp(),
    square_times(G, E, 500000),
    T2 = erlang:timestamp(),%24 seconds for 1/2 million.
    timer:now_diff(T2, T1);
test(4) ->
    %testing the new addition formula.
    E = make(),
    G = gen_point(E),
    %G = {360, ff:sub(0, 360, Base)},
    Gj = to_jacob(G),
    G = to_affine(Gj, E),
    G2 = addition(G, G, E),
    G3 = addition(G2, G, E),
    Gj2 = jacob_double(Gj, E), 
    Gj3 = jacob_add(Gj2, Gj, E), 
    G2 = to_affine(Gj2, E),
    G3 = to_affine(Gj3, E),
    success;
test(5) ->
    E = make(),
    G = gen_point(E),
    Gj = to_jacob(G),
    T1 = erlang:timestamp(),
    jacob_square_times(Gj, E, 500000),
    T2 = erlang:timestamp(),%4 seconds for 1/2 million.
    %6x improvement
    timer:now_diff(T2, T1);
test(6) ->
    E = make(),
    G1 = to_jacob(gen_point(E)),
    G = to_jacob(gen_point(E)),
    T1 = erlang:timestamp(),
    jacob_add_times(G1, G, E, 500000),
    T2 = erlang:timestamp(),%6 seconds for 1/2 million.
    %4x improvement
    timer:now_diff(T2, T1);
test(7) ->
    E = make(),
    G = to_jacob(gen_point(E)),
    GN = jacob_negate(G, E),
    jacob_equal(
      G,
      jacob_add(
        G, jacob_add(G, GN, E), E),
      E);
test(8) ->
    E = make(),
    G2 = gen_point(E),
    G = to_jacob(G2),
    Z = jacob_add(G, jacob_negate(G, E), E),
    {
      Z,
      jacob_zero(),
      jacob_equal(Z, jacob_zero(), E),
      jacob_equal(G, G, E),
      jacob_equal(jacob_add(Z, G, E), G, E),
      to_affine(jacob_mul(G, 1000000000000, E), E),
      multiplication(G2, 1000000000000, E)}.
    


