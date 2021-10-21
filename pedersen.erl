-module(pedersen).
-export([make_bullet/4,
         verify_bullet/5,
         test/1]).

%finite field arithmetic modulus the group order of the elliptic curve.
%for doing operations on the scalars that we use to multiply curve points.
fadd(X, Y, E) when is_integer(X) ->
    N = order(E),
    (X + Y) rem N.
fmul(X, Y, E) when is_integer(X) ->
    N = order(E),
    (X * Y) rem N.
fdot([], [], E) -> 0;
fdot([X|XT], [Y|YT], E) when is_integer(X) ->
    N = order(E),
    fadd(fmul(X, Y, E), fdot(XT, YT, E), E).
fv_mul(_, [], _) -> [];
fv_mul(S, [H|T], E) when is_integer(H) ->
    [fmul(S, H, E)|fv_mul(S, T, E)].
fv_add(_, [], _) -> [];
fv_add([A|AT], [B|BT], E) when is_integer(A) -> 
    [fadd(A, B, E)|fv_add(AT, BT, E)].
    

%elliptic curve operations.
prime(E) ->
    secp256k1:field_prime(E).
order(E) ->
    secp256k1:order(E).
gen_point(E) ->
    secp256k1:gen_point(E).
add(X, Y, E) ->
    secp256k1:addition(X, Y, E).
mul(X, Y, E) ->
    secp256k1:multiplication(X, Y, E).
sum_up(V, E) ->
    lists:foldl(fun(A, B) -> 
                        add(A, B, E) end,
                infinity, V).
v_add([], [], _) -> [];
v_add([G|GT], [A|AT], E) -> 
    [add(G, A, E)|
     v_add(GT, AT, E)].
v_mul(_, [], _) -> [];
v_mul(S, [H|T], E) ->
    [mul(H, S, E)|
     v_mul(S, T, E)].

%pedersen vector commit.
commit([V1], [G1], E) ->
    mul(G1, V1, E);
%commit([V1, V2], [G1, G2], E) ->
%    add(mul(G1, V1, E),
%        mul(G2, V2, E),
%        E);
commit(V, G, E) ->
    add(mul(hd(G), hd(V), E),
        commit(tl(V), tl(G), E),
        E).
verify(G, V, C, Root, E) ->
    Root == commit([V, 1], [G, C], E).

%get the right and left points to build up squares to collapse the pedersen commitment in half.
get_lr(G, V, E) ->
    {sum_up(get_ls(G, V, E), E),
     sum_up(get_rs(G, V, E), E)}.
get_ls([], [], _) -> [];
get_ls([G1, _|GT], [_, V2|VT], E) -> 
    %P = prime(E),
    %N = secp256k1:order(E),
    [mul(G1, V2, E)|
     get_ls(GT, VT, E)].
get_rs([], [], _) -> [];
get_rs([_, G2|GT], [V1, _|VT], E) -> 
    %P = prime(E),
    [mul(G2, V1, E)|
     get_rs(GT, VT, E)].
   
%calculating the 1/2 length pedersen commitment 
next_v_commit(A, B, C, S, SI) -> 
    next_v_commit(A, B, C, S, SI, [], [], []).
next_v_commit([], [], _, _, _, Bigs, Gs, Vs) -> 
    {lists:reverse(Bigs), 
     lists:reverse(Gs), 
     lists:reverse(Vs)};
next_v_commit([G1, G2|GT], [V1, V2|VT], 
         E, S, SI, Bigs, Gs, Vs) -> 
    %N = order(E),
    G = add(mul(G1, SI, E), 
            mul(G2, S, E), E),
    V = fadd(fmul(V1, S, E), 
             fmul(V2, SI, E), E),
    next_v_commit(GT, VT, E, S, SI,
             [mul(G, V, E)|Bigs],
             [G|Gs], [V|Vs]).

%random number blinding scaling factor for security
apply_s(_, _, [], _, _) -> [];
apply_s(S2, SI2, [L, R|T], N, E) -> 
    [mul(L, SI2, E),
     mul(R, S2, E)|
     apply_s(S2, SI2, T, N+1, E)].

verify_bullet(V, G, E, [X|LRs], S) ->
    N = order(E),
    SI = basics:inverse(S, N),
    S2 = fmul(S, S, E),
    SI2 = fmul(SI, SI, E),
    Commit = commit(V, G, E),
    LR2 = apply_s(S2, SI2, LRs, 0, E),
    X == sum_up([Commit|LR2], E).

scale_lrs([], _, _, _) -> infinity;
   %infinity is the zero element of the elliptic curve group.
scale_lrs([L, R|T], S2, SI2, E) -> 
    add(
      add(mul(L, SI2, E),
          mul(R, S2, E),
          E),
      scale_lrs(T, S2, SI2, E),
      E).

make_bullet(V, Ps, E, S) ->
    %S is the blinding factor random number. It needs to be choosen from a fair non-manipulable source.
    N = order(E),
    LongCommit = commit(V, Ps, E),
    S2 = fmul(S, S, E),
    SI = basics:inverse(S, N),
    SI2 = fmul(SI, SI, E),
    LRs = make_bullet_lrs(V, Ps, E, S, SI),
    ScaledLRs = scale_lrs(LRs, S2, SI2, E),
    Commit = add(LongCommit, ScaledLRs, E),
    [Commit|LRs].

make_bullet_lrs(V, Ps, E, S, SI) ->
    {L, R} = get_lr(Ps, V, E),
    {C2, Ps2, Vs2} = 
        next_v_commit(Ps, V, E, S, SI),
    B = length(C2),
    if
        (B == 1) -> [L, R];
        true ->
            [L, R|make_bullet_lrs(
                    Vs2, Ps2, E, S, SI)]
    end.
   
range(N, N) -> [];
range(A, B) when A < B -> 
    [A|range(A+1, B)].

make_ipa(A, B, G, H, Q, E, X) ->
    %Inner Product Arguments
    
    %C = A*G + B*H + (A*B)q
    %C and Q are elliptic curve points.
    %G and H are vectors of elliptic curve points.
    % Q, G and H, are all generator points.
    %A and B are vectors.
    % * is dot product

    %scale Q with A*G and B*H

    %N = secp256k1:order(E),
    %S = length(A),
    C1 = add(commit(A, G, E),
             add(commit(B, H, E),
                 mul(Q, fdot(A, B, E), E),
                 E), E),
    {Cs, AN, BN, CN} = make_ipa2(C1, A, G, B, H, Q, E, [C1], X), 
    {commit(A, G, E),
     fdot(A, B, E),
     Cs, AN, BN, CN}.
make_ipa2(C1, A, G, B, H, Q, E, Cs, X) ->
    io:fwrite("make ipa2\n"),
    S = length(A),
    io:fwrite(integer_to_list(S)),
    io:fwrite("\n"),
    N = order(E),
    if
        (S == 1) ->
            {Cs, hd(A), hd(B), C1};
        true ->
            S2 = S div 2,
            {Al, Ar} = lists:split(S2, A),
            {Bl, Br} = lists:split(S2, B),
            Zl = fdot(Ar, Bl, E),
            Zr = fdot(Al, Br, E),
            {Gl, Gr} = lists:split(S2, G),
            {Hl, Hr} = lists:split(S2, H),
            Cl = add(commit(Ar, Gl, E),
                     add(commit(Bl, Hr, E),
                         mul(Q, Zl, E), E), 
                     E),
            Cr = add(commit(Al, Gr, E),
                     add(commit(Br, Hl, E),
                         mul(Q, Zr, E), E), E),
 %X should be a fairly calculated random number.
            Xi = basics:inverse(X, N),
            A2 = fv_add(Al, fv_mul(X, Ar, E), E),
            B2 = fv_add(Bl, fv_mul(Xi, Br, E), E),
            %C2 = Cl*X + C1 + Cr*Xi
            C2 = add(mul(Cl, X, E), 
                     add(C1, mul(Cr, Xi, E), E),
                     E),
            G2 = v_add(Gl, v_mul(Xi, Gr, E), E),
            H2 = v_add(Hl, v_mul(X, Hr, E), E),
            make_ipa2(C2, A2, G2, B2, 
                      H2, Q, E, [Cl, Cr|Cs], X)
    end.
get_gn(_, [G], E) -> G;
get_gn(X, G, E) -> 
    S = length(G),
    S2 = S div 2,
    {Gl, Gr} = lists:split(S2, G),
    G2 = v_add(Gl, v_mul(X, Gr, E), E),
    get_gn(X, G2, E).
fold_cs(_X, _Xi, [C], _E) -> C;
fold_cs(X, Xi, [Cl, Cr|Cs], E) ->
    add(
      add(mul(Cl, X, E),
          mul(Cr, Xi, E),
          E),
      fold_cs(X, Xi, Cs, E),
      E).
verify_ipa({AG, AB, Cs, AN, BN, CN}, 
           B, X, G, H, Q, E) ->
    %C3 = C2l*X + C2 + C2r*Xi
       %= C1l*X + C2l*X + C1r*Xi + C2r*Xi + C1
    N = order(E),
    C1 = hd(lists:reverse(Cs)),
    C1 = add(add(AG, commit(B, H, E), E), 
             mul(Q, AB, E), E),
    Xi = basics:inverse(X, N),
    GN = get_gn(Xi, G, E),
    HN = get_gn(X, H, E),
    CN = add(add(mul(GN, AN, E),
                 mul(HN, BN, E),
                 E),
             mul(Q, fmul(AN, BN, E), E),
             E),
    CN = fold_cs(X, Xi, Cs, E),
    true.
    

test(1) ->
    %pedersen vector commitment
    E = secp256k1:make(),
    Ps = lists:map(
           fun(_) ->
                   secp256k1:gen_point(E)
           end, [1,2,3,4,5]),
    [P1, P2, P3, P4, P5] = Ps,

    %storing some numbers in the accumulator. we can store any numbers modulus E#curve.p, the prime base of the finite field that the elliptic curve is defined over.
    [V1, V2, V3, V4, V5] =
        [5, 7, 11, 13, 15],
    V = [V1, V2, V3, V4, V5],
    C = commit(V, Ps, E),
    Proof = commit([V1, V2, V3, V5],
                    [P1, P2, P3, P5],
                    E),
    C = commit([V4, 1], [P4, Proof], E),
    success;
test(2) ->
    %bulletproofs, steps done long form to show what is going on.
    E = secp256k1:make(),
    N = secp256k1:order(E),
    Ps = lists:map(fun(_) ->
                           secp256k1:gen_point(E)
                   end, range(1, 9)),
    V = [1,22,33,44,
         55,66,7,8],
    
    LongCommit = commit(V, Ps, E),
    Proof2 = commit([hd(V)] ++ tl(tl(V)),
                    [hd(Ps)]++tl(tl(Ps)),
                    E),
    LongCommit = 
        commit([hd(tl(V)), 1], 
               [hd(tl(Ps)), Proof2], E),


    %graphical explanation.
    % https://twitter.com/VitalikButerin/status/1371844878968176647/photo/1
    
    %random scalar
    S = 20,
    S2 = fmul(S, S, E),
    SI = basics:inverse(S, N),
    SI2 = fmul(SI, SI, E),

    {L, R} = get_lr(Ps, V, E),
    {C2, Ps2, Vs2} = next_v_commit(Ps, V, E, S, SI),
    Commit2 = sum_up(C2, E),
    Commit2 = sum_up([LongCommit,
%    Commit2 = sum_up([LongCommit,
                      mul(R, S2, E),
                      mul(L, SI2, E)], E),

    {L2, R2} = get_lr(Ps2, Vs2, E),
    {C3, Ps3, Vs3} = next_v_commit(Ps2, Vs2, E, S, SI),
    Commit3 = sum_up(C3, E),
    Commit3 = sum_up([LongCommit, 
                      mul(L, SI2, E), 
                      mul(R, S2, E), 
                      mul(L2, SI2, E), 
                      mul(R2, S2, E)], E),

    {L3, R3} = get_lr(Ps3, Vs3, E),
    {C4, _Ps4, _Vs4} = 
        next_v_commit(Ps3, Vs3, E, S, SI),
    Commit4 = hd(C4),
    Commit4 = 
        sum_up(
          [LongCommit,
           mul(L, SI2, E), 
           mul(R, S2, E),
           mul(L2, SI2, E), 
           mul(R2, S2, E),
           mul(L3, SI2, E), 
           mul(R3, S2, E)], 
          E),

    BulletProof = [Commit4, L, R, L2, R2, L3, R3],
    
    BulletProof2 = make_bullet(V, Ps, E, S),

    BulletProof = BulletProof2,

    true = verify_bullet(V, Ps, E, BulletProof, S),

    success;
test(3) ->
    %bulletproofs using better syntax.
    E = secp256k1:make(),
    V = range(10000, 10256),
    Ps = lists:map(fun(_) ->
                           secp256k1:gen_point(E)
                   end, range(0, length(V))),
    S = 50,
    io:fwrite("proving "),
    io:fwrite(integer_to_list(length(V))),
    io:fwrite(" values.\n"),
    T1 = os:timestamp(),
    BulletProof = make_bullet(V, Ps, E, S),
    io:fwrite("verifying proof of length "),
    io:fwrite(integer_to_list(length(BulletProof))),
    io:fwrite("\n"),
    T2 = os:timestamp(),
    true = verify_bullet(V, Ps, E, BulletProof, S),
    T3 = os:timestamp(),
    io:fwrite("proving took "),
    io:fwrite(float_to_list(timer:now_diff(T2, T1)/1000000)),
    io:fwrite("\n"),
    io:fwrite("verifying took "),
    io:fwrite(float_to_list(timer:now_diff(T3, T2)/1000000)),
    io:fwrite("\n"),
    success;
test(4) ->
    %Inner Product Arguments
    
    %C = A*G + B*H + (A*B)q
    %C and Q are elliptic curve points.
    %G and H are vectors of elliptic curve points.
    % Q, G and H, are all generator points.
    %A and B are vectors.
    % * is dot product
    
    E = secp256k1:make(),
    N = secp256k1:order(E),
    A = range(100, 108),
    S = length(A),
    B = range(200, 200 + S),
    G = lists:map(fun(_) ->
                           gen_point(E)
                   end, range(0, S)),
    H = lists:map(fun(_) ->
                           gen_point(E)
                   end, range(0, S)),
    Q = gen_point(E),
    C1 = add(commit(A, G, E),
             add(commit(B, H, E),
                 mul(Q, fdot(A, B, E), E),
                 E), E),



    S2 = S div 2,
    {Al, Ar} = lists:split(S2, A),
    {Bl, Br} = lists:split(S2, B),
    Zl = fdot(Ar, Bl, E),
    Zr = fdot(Al, Br, E),
    
    {Gl, Gr} = lists:split(S2, G),
    {Hl, Hr} = lists:split(S2, H),
    Cl = add(commit(Ar, Gl, E),
             add(commit(Bl, Hr, E),
                 mul(Q, Zl, E), E), E),
    Cr = add(commit(Al, Gr, E),
             add(commit(Br, Hl, E),
                 mul(Q, Zr, E), E), E),
    %X should be a fairly calculated random number.
    X = basics:inverse(2, N),
    Xi = basics:inverse(X, N),
    %io:fwrite([X, Al, Ar]),
    A2 = fv_add(Al, fv_mul(X, Ar, E), E),
    B2 = fv_add(Bl, fv_mul(Xi, Br, E), E),
    %C2 = Cl*X + C1 + Cr*Xi
    C2 = add(mul(Cl, X, E), 
             add(C1, mul(Cr, Xi, E), E),
             E),
    G2 = v_add(Gl, v_mul(Xi, Gr, E), E),
    H2 = v_add(Hl, v_mul(X, Hr, E), E),
    
    %check
    C2 = add(commit(A2, G2, E),
             add(commit(B2, H2, E),
                 mul(Q, fdot(A2, B2, E), E),
                 E), E),

    %C1 = A*G + B*H + (A*B)q
    %C2 = C1l*X + C1 + C1r*Xi
    %C3 = C2l*X + C2 + C2r*Xi
       %= C1l*X + C2l*X + C1r*Xi + C2r*Xi + C1

    %CN = AN*GN + BN*HN + (AN*BN)q

    %publicly known:
    %G, H, Q
    %A*G is the publicly known commitment.

    %A*B is what we are trying to prove.
    % {A*G, A*B, [C1, C2, ... , CN], AN, BN, CN}
    X = basics:inverse(2, N),
    Bv = [0,0,0,1,1,0,0,0],%103+104 = 207
    Proof = make_ipa(
              A, Bv,%103+104 = 207
              G, H, Q, E, X),
    {_, 207, _, _, _, _} = Proof,
    %io:fwrite(Proof),
    true = verify_ipa(Proof, Bv, X, G, H, Q, E),
    Proof,
    success.
 
    
    
    
