-module(pedersen).
-export([make_bullet/4,
         verify_bullet/5,
         test/1]).

fadd(X, Y, E) when is_integer(X) ->
    N = order(E),
    (X + Y) rem N.
fmul(X, Y, E) when is_integer(X) ->
    N = order(E),
    (X * Y) rem N.
add(X, Y, E) ->
    secp256k1:addition(X, Y, E).
mul(X, Y, E) ->
    secp256k1:multiplication(X, Y, E).

%pedersen vector commit.
commit([V1, V2], [G1, G2], E) ->
    add(mul(G1, V1, E),
        mul(G2, V2, E),
        E);
commit(V, G, E) ->
    add(mul(hd(G), hd(V), E),
        commit(tl(V), tl(G), E),
        E).

verify(G, V, C, Root, E) ->
    Root == commit([V, 1], [G, C], E).

sum_up(V, E) ->
    lists:foldl(fun(A, B) -> 
                        add(A, B, E) end,
                infinity, V).
    

many(N) when N < 1 -> [];
many(N) -> [0|many(N-1)].

get_lr(G, V, E) ->
    {sum_up(get_ls(G, V, E), E),
     sum_up(get_rs(G, V, E), E)}.

get_ls([], [], _) -> [];
get_ls([G1, _|GT], [_, V2|VT], E) -> 
    P = prime(E),
    N = secp256k1:order(E),
    [mul(G1, V2, E)|
     get_ls(GT, VT, E)].
get_rs([], [], _) -> [];
get_rs([_, G2|GT], [V1, _|VT], E) -> 
    P = prime(E),
    [mul(G2, V1, E)|
     get_rs(GT, VT, E)].

prime(E) ->
    secp256k1:field_prime(E).
order(E) ->
    secp256k1:order(E).
    
next_v_commit(A, B, C, S, SI) -> 
    next_v_commit(A, B, C, S, SI, [], [], []).
next_v_commit([], [], _, _, _, Bigs, Gs, Vs) -> 
    {lists:reverse(Bigs), 
     lists:reverse(Gs), 
     lists:reverse(Vs)};
next_v_commit([G1, G2|GT], [V1, V2|VT], 
         E, S, SI, Bigs, Gs, Vs) -> 
    N = order(E),
    G = add(mul(G1, SI, E), mul(G2, S, E), E),
    V = fadd(fmul(V1, S, E), fmul(V2, SI, E), E),
    next_v_commit(GT, VT, E, S, SI,
             [mul(G, V, E)|Bigs],
             [G|Gs], [V|Vs]).

apply_s(_, _, [], _, E) -> [];
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
    {C2, Ps2, Vs2} = next_v_commit(Ps, V, E, S, SI),
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

test(1) ->
    %pedersen vector commitment
    E = secp256k1:make(),
    Ps = lists:map(fun(_) ->
                           secp256k1:gen_point(E)
                   end, [1,2,3,4,5]),
    [P1, P2, P3, P4, P5] = Ps,

    %storing some prime numbers in the accumulator. we can store any numbers modulus E#curve.p, the prime base of the finite field that the elliptic curve is defined over.
    [V1, V2, V3, V4, V5] =
        [5, 7, 11, 13, 17],
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
    P = secp256k1:field_prime(E),
    N = secp256k1:order(E),
    Ps = lists:map(fun(_) ->
                           secp256k1:gen_point(E)
                   end, many(8)),
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
    {C4, Ps4, Vs4} = next_v_commit(Ps3, Vs3, E, S, SI),
    Commit4 = hd(C4),
    Commit4 = sum_up([LongCommit,
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
                   end, many(length(V))),
    S = 50,
    BulletProof = make_bullet(V, Ps, E, S),
    io:fwrite("proving "),
    io:fwrite(integer_to_list(length(V))),
    io:fwrite(" values with a proof of length "),
    io:fwrite(integer_to_list(length(BulletProof))),
    io:fwrite("\n"),
    true = verify_bullet(V, Ps, E, BulletProof, S),
    success.
    

