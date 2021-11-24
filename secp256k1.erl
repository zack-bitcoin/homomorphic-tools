-module(secp256k1).
-export([test/1, make/0, addition/3, 
         multiplication/3, gen_point/1,
         field_prime/1, order/1,
         on_curve/2,
         mod/2, invert_batch/2,

         to_jacob/1, to_affine/2,
         jacob_mul/3, jacob_add/3, jacob_zero/0,
         jacob_equal/3, jacob_negate/2, jacob_sub/3,

         multi_exponent/3
]).

-define(pow_2_128, 340282366920938463463374607431768211456).

-record(curve, {a, b, g, n, p, e}).
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

make(A, B, X, Y, P, N, Endo) ->
    #curve{a = A, b = B, g = {X, Y}, 
           p = P, n = N, e = Endo}.

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
    Endomorphism = hex_to_int("7AE96A2B657C07106E64479EAC3434E99CF0497512F58995C1396C28719501EE"),
    make(A, B, X, Y, P, N, Endomorphism).

to_jacob({X, Y}) ->
    {X, Y, 1}.
to_affine(P = {_, _, 0}, E) ->
    infinity;
to_affine(P = {_, _, Z}, E) ->
    Base = field_prime(E),
    Z2 = ff:inverse(Z, Base),
    to_affine(P, Z2, E).
to_affine({X, Y, _}, Inverse, E) ->
    Base = field_prime(E),
    P2 = ff:mul(Inverse, Inverse, Base),
    P3 = ff:mul(Inverse, P2, Base),
    {ff:mul(X, P2, Base),
     ff:mul(Y, P3, Base)}.
    
to_affine_batch(Ps, E) ->
    Base = field_prime(E),
    Zs = lists:map(fun({_, _, Z}) -> Z end, 
                   Ps),
    Is = invert_batch(Zs, Base),
    lists:zipwith(
      fun(P, I) -> to_affine(P, I, E) end,
      Ps, Is).
   
pis([], _, _) -> [];
pis([H|T], A, B) -> 
    X = ff:mul(H, A, B),
    [X|pis(T, X, B)].

invert_batch(Vs, Base) ->
    [All|V2] = lists:reverse(pis(Vs, 1, Base)),%[v16, v15, v14, v13, v12, v1]
    AllI = ff:inverse(All, Base),%i16
    VI = lists:map(
           fun(V) -> ff:mul(AllI, V, Base) end,
           V2), %[i6, i56, i46, i36, i26]
    V3 = lists:reverse(pis(lists:reverse(Vs), 1, Base)),%[v16, v26, v36, v46, v56, v6]
    V4 = tl(V3)++[1],%[v26, v36, v46, v56, v6, 1]
    VI2 = [AllI|lists:reverse(VI)],%[i16, i26, i36, i46, i56, i6]
    lists:zipwith(fun(A, B) ->
                          ff:mul(A, B, Base)
                  end, V4, VI2).

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

jacob_sub(P1, P2, E) -> 
    jacob_add(P1, jacob_negate(P2, E), E).
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
            %io:fwrite("same point\n"),
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
    jacob_zero();
jacob_mul(_, {_, _, 0}, _, E) -> 
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

div_nearest(A, Base) ->
    (A + (Base div 2)) div Base.

split_scalar_endo(K, E) ->
    Base = field_prime(E),
    %A1 = hex_to_int("3086D221A7D46BCDE86C90E49284EB15"),
    %B1 = -hex_to_int("E4437ED6010E88286F547FA90ABFE4C3"),
    %A2 = hex_to_int("114CA50F7A8E2F3F657C1108D9D44CFD8"),
    A1 = 64502973549206556628585045361533709077,
    B1 = -303414439467246543595250775667605759171,
    A2 = 367917413016453100223835821029139468248,
    %io:fwrite({A1, B1, A2}),
    B2 = A1,
    C1 = div_nearest(ff:mul(B2, K, Base), Base),
    C2 = div_nearest(ff:neg(ff:mul(B1, K, Base), Base), Base),
    K1 = ff:sub(
           K, ff:add(
                ff:mul(C1, A1, Base),
                ff:mul(C2, A2, Base),
                Base
               ), Base),
    K2 = ff:sub(ff:neg(ff:mul(C1, B1, Base), Base),
                ff:mul(C2, B2, Base), Base),
    
    K1neg = (K1 > ?pow_2_128),
    K2neg = (K2 > ?pow_2_128),
    K1b = if
              K1neg -> Base - K1;
              true -> K1
          end,
    K2b = if
              K2neg -> Base - K2;
              true -> K2
          end,
    K1b < ?pow_2_128,
    K2b < ?pow_2_128,
    {K1neg, K1b, K2neg, K2b}.

endo_loop(_, 0, K1p, 0, K2p, _) -> 
    {K1p, K2p};
endo_loop(D, K1, K1p, K2, K2p, E) ->
    K1p2 = if
               ((K1 rem 2) == 1) ->
                   jacob_add(K1p, D, E);
               true -> K1p
           end,
    K2p2 = if
               ((K2 rem 2) == 1) ->
                   jacob_add(K2p, D, E);
               true -> K2p
           end,
    D2 = jacob_double(D, E),
    endo_loop(D2, K1 div 2, K1p2, 
                  K2 div 2, K2p2, E).

endo_mul(P, X, E) ->
    Base = field_prime(E),
    {K1neg, K1, K2neg, K2} = 
        split_scalar_endo(X, E),
    {K1b, K2b} = 
        endo_loop(P, K1, jacob_zero(), 
                     K2, jacob_zero(), E),
    K1c = if
              K1neg -> jacob_negate(K1b, E);
              true -> K1b
          end,
    {K2cA, K2cB, K2cC} = 
        if
            K2neg -> jacob_negate(K2b, E);
            true -> K2b
        end,
    K2d = {ff:mul(K2cA, E#curve.e, Base),
           K2cB, K2cC},
    jacob_add(K1c, K2d, E).

%multiplication(infinity, _, _) ->
%    infinity;
multiplication(P1, 0, E) ->
    infinity;
multiplication(P1, X, E) 
  when ((X rem 2) == 0) ->
    multiplication(
      addition(P1, P1, E),
      X div 2, E);
multiplication(P1, 1, _) -> 
    P1;
multiplication(P1, X, E) ->
    addition(
      P1,
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

many(_, 0) -> [];
many(X, N) when (N > 0) -> 
    [X|many(X, N-1)].

chunkify(_, _, 0) -> [];
chunkify(R, C, Many) -> 
    [(R rem C)|
     chunkify(R div C, C, Many-1)].

matrix_diagonal_flip([[]|_]) -> [];
matrix_diagonal_flip(M) ->
    Col = lists:map(fun(X) -> hd(X) end, M),
    Tls = lists:map(fun(X) -> tl(X) end, M),
    [Col|matrix_diagonal_flip(Tls)].
               
bucketify([], Buckets, [], E) -> 
    %for each bucket, sum up the points inside. [S1, S2, S3, ...
    %T_i = S1 + 2*S2 + 3*S3 ... (this is another multi-exponent. a simpler one this time.)
    %compute starting at the end. S7 + (S7 + S6) + (S7 + S6 + S5) ...
    T = tuple_to_list(Buckets),
    T2 = lists:reverse(T),
    bucketify2(tl(T2), hd(T2), hd(T2), E);
bucketify([0|T], Buckets, [_|Gs], E) ->
    bucketify(T, Buckets, Gs, E);
bucketify([BucketNumber|T], Buckets, [G|Gs], E) ->
    %to calculate each T_i.
    %6*G1 + 2*G2 + 5*G3 ... 6th, then 2nd, then 5th buckets.
    %(2^C)-1 buckets in total. 
    %Put a list of the Gs into each bucket.
    Bucket = element(BucketNumber, Buckets),
    Bucket2 = jacob_add(G, Bucket, E),
    Buckets2 = setelement(
                 BucketNumber, Buckets, Bucket2),
    bucketify(T, Buckets2, Gs, E).
bucketify2([], L, T, E) -> T;
bucketify2([S|R], L, T, E) -> 
    L2 = jacob_add(S, L, E),
    T2 = jacob_add(L2, T, E),
    bucketify2(R, L2, T2, E).

remove_zero_terms([], [], A, B) ->
    {lists:reverse(A), lists:reverse(B)};
remove_zero_terms([0|R], [_|G], A, B) ->
    remove_zero_terms(R, G, A, B);
remove_zero_terms(R, G, A, B) ->
    remove_zero_terms(
      tl(R), tl(G), [hd(R)|A], [hd(G)|B]).


multi_exponent(Rs0, Gs0, E) ->
    %output T.
    %T = R1*G1 + R2*G2 + ...
    {Rs, Gs} = remove_zero_terms(Rs0, Gs0, [], []),
    multi_exponent2(Rs, Gs, E).
multi_exponent2([], [], E) ->
    jacob_zero();
multi_exponent2(Rs, Gs, E) ->
    %io:fwrite({Rs}),
    C0 = round(math:log(length(Rs))/math:log(2)),
    C = min(C0, 16),%more than 16 uses a lot of memory.
    %C = max(C1, 4),
    F = det_pow(2, C),
    %write each integer in R in binary. partition the binaries into chunks of C bits.
    B = 256,
    R_chunks = 
        lists:map(
          fun(R) -> L = chunkify(
                          R, F, 1+(B div C)),
                    lists:reverse(L)
          end, Rs),
    %this break the problem up into 256/C instances of multi-exponentiation.
    %each multi-exponentiation has length(Gs) parts. What is different is that instead of the Rs having 256 bits, they only have C bits. each multi-exponentiation makes [T1, T2, T3...]
    Ts = matrix_diagonal_flip(R_chunks),
    Buckets = list_to_tuple(many(jacob_zero(), F)),
    Ss = lists:map(
           fun(X) -> 
                   bucketify(X, Buckets, Gs, E)
           end, Ts),
    me3(Ss, jacob_zero(), F, E).
me3([H], A, _, E) -> 
    jacob_add(H, A, E);
me3([H|T], A, F, E) -> 
    X = jacob_add(H, A, E),
    X2 = jacob_mul(X, F, E),
    me3(T, X2, F, E).



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
      to_affine(endo_mul(G, 1000000000000, E), E),
      multiplication(G2, 1000000000000, E)};
test(9) ->
    E = make(),
    G2 = gen_point(E),
    G = to_jacob(G2),
    Base = field_prime(E),
    P = ff:inverse(ff:neg(1000000000000000, Base), Base),
    Many = many(0, 50),
    T1 = erlang:timestamp(),
    io:fwrite("normal multiplication \n"),
    lists:map(fun(_) ->
                      multiplication(G2, P, E)
              end, Many),
    T2 = erlang:timestamp(),
    io:fwrite("jacob multiplication \n"),
    lists:map(fun(_) ->
                      jacob_mul(G, P, E)
              end, Many),
    T3 = erlang:timestamp(),
    io:fwrite("endo multiplication \n"),
    lists:map(fun(_) ->
                      endo_mul(G, P, E)
              end, Many),
    T4 = erlang:timestamp(),
    D1 = timer:now_diff(T2, T1),
    D2 = timer:now_diff(T3, T2),
    D3 = timer:now_diff(T4, T3),
    {D1, D2, D3};
test(10) ->
    %multi exponent test
    %todo. make it pass.
    E = make(),
    Base = field_prime(E),
    Rs = [ff:neg(1, Base),
         ff:neg(2, Base),
         ff:neg(3, Base),
         ff:neg(4, Base),
         ff:neg(5, Base),
         ff:neg(6, Base)],
    %Rs = [1, 0, 1, 2],
    Gs = lists:map(
      fun(_) ->
              to_jacob(gen_point(E))
      end, many(1, length(Rs))),
    Ps = lists:zipwith(
           fun(R, G) -> jacob_mul(G, R, E) end,
           Rs, Gs),
    true = jacob_equal(
             lists:foldl(
               fun(A, B) -> jacob_add(A, B, E) end,
               jacob_zero(), Ps),
             multi_exponent(Rs, Gs, E),
             E),
    success;
test(11) ->
    %tests multi-exponent
    E = make(),
    Base = field_prime(E),
    T_256 = det_pow(2, 256),
    Many = 1000,
    Rs = lists:map(fun(_) ->
                           random:uniform(T_256) rem Base
                   end, many(1, Many)),
    Gs = lists:map(
           fun(_) ->
                   to_jacob(gen_point(E))
           end, many(1, length(Rs))),
    
    
    T1 = erlang:timestamp(),
    Ps = lists:zipwith(
           fun(R, G) -> jacob_mul(G, R, E) end,
           Rs, Gs),
    Result = 
        lists:foldl(
          fun(A, B) -> jacob_add(A, B, E) end,
          jacob_zero(), Ps),
    T2 = erlang:timestamp(),
    Result2 = multi_exponent(Rs, Gs, E),
    T3 = erlang:timestamp(),
    to_affine(Result2, E),
    T4 = erlang:timestamp(),
    true = jacob_equal(Result, Result2, E),
    {timer:now_diff(T2, T1),
     timer:now_diff(T3, T2),
     timer:now_diff(T4, T3)};
test(12) ->
    %test invert_batch
    E = make(),
    Base = field_prime(E),
    V = [1,2,3,4,5,6],
    IV = invert_batch(V, Base),
    V = invert_batch(IV, Base),
    IV = lists:map(fun(X) -> basics:inverse(X, Base) end, V),
    success.

                           

    


    
    


