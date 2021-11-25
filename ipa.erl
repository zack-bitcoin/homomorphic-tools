-module(ipa).
-export([test/1]).
%inner product arguments using pedersen commitments.
%uses the secp256k1 library.

-define(order, 115792089237316195423570985008687907852837564279074904382605163141518161494337).

-define(sub(A, B), ((A - B + ?order) rem ?order)).%assumes B less than ?order
-define(neg(A), ((?order - A) rem ?order)).%assumes A less than ?order
-define(add(A, B), ((A + B) rem ?order)).
-define(mul(A, B), ((A * B) rem ?order)).

dot(A, B) -> dot(A, B, 0).
dot([], [], Acc) -> Acc;
dot([A|AT], [B|BT], Acc) ->
    %dot product of two scalar vectors.
    Acc2 = ?mul(A, B),
    dot(AT, BT, ?add(Acc, Acc2)).
fv_add(As, Bs) ->
    %adding 2 scalar vectors by adding each component.
    lists:zipwith(
      fun(A, B) -> ?add(A, B) end,
      As, Bs).
fv_mul(S, Bs) ->
    %multiplying a scalar vector by a scalar.
    lists:map(fun(X) -> ?mul(X, S) end,
              Bs).
%lists:zipwith(
%      fun(A, B) -> ?mul(A, B) end,
%      As, Bs).

commit(V, G, E) ->
    %pedersen commitment
    %G is a list of jacob encoded points.
    %returns a single jacob encoded point.
    %V1*G1 + V2*G2 + V3*G3 + ...
    secp256k1:multi_exponent(V, G, E).

add(A, B, E) ->
    secp256k1:jacob_add(A, B, E).
sub(A, B, E) ->
    secp256k1:jacob_sub(A, B, E).
double(A, E) ->
    secp256k1:jacob_double(A, E).
mul(X, G, E) ->
    %multiply point G by scalar X.
    secp256k1:jacob_mul(G, X, E).
eq(G, H, E) ->
    secp256k1:jacob_equal(G, H, E).
v_add(As, Bs, E) ->
    lists:zipwith(
      fun(A, B) ->
              add(A, B, E)
      end, As, Bs).
v_mul(A, Bs, E) ->
    %this is like, half way to a commitment. it does the multiplications, but doesn't add up the points at the end.
    lists:map(
      fun(B) ->
              mul(A, B, E)
      end, Bs).

hash(X) when is_binary(X) ->
    crypto:hash(sha256, X).
point_to_entropy(J, E) ->
    {X, Y} = secp256k1:to_affine(J, E),
    <<Z:256>> = hash(<<X:256, Y:256>>),
    Z.
    
make_ipa(A, B, G, H, Q, E) ->
    AG = commit(A, G, E),
    BH = commit(B, H, E),
    AGBH = add(AG, BH, E),
    AB = dot(A, B),
    C1 = add(AGBH, mul(AB, Q, E), E),
    X = point_to_entropy(C1, E),
    Xi = basics:inverse(X, ?order),
    {Cs, AN, BN, CN} = 
        make_ipa2(C1, A, G, B, H, 
                  Q, E, [C1], X, Xi), 
    {AG, AB, Cs, AN, BN, CN}.
    
make_ipa2(C1, [A], _, [B], _, _, _, Cs, _, _) ->
    %maybe at this point we should compress some of this data so it is smaller to send.
    {Cs, A, B, C1};
make_ipa2(C1, A, G, B, H, Q, E, Cs, X, Xi) ->
    S2 = length(A) div 2,
    {Al, Ar} = lists:split(S2, A),
    {Bl, Br} = lists:split(S2, B),
    Zl = dot(Ar, Bl),
    Zr = dot(Al, Br),
    {Gl, Gr} = lists:split(S2, G),
    {Hl, Hr} = lists:split(S2, H),
    Cl = add(commit(Ar, Gl, E),
             add(commit(Bl, Hr, E),
                 mul(Zl, Q, E), E), E),
    Cr = add(commit(Al, Gr, E),
             add(commit(Br, Hl, E),
                 mul(Zr, Q, E), E), E),
    A2 = fv_add(Al, fv_mul(X, Ar)),
    B2 = fv_add(Bl, fv_mul(Xi, Br)),
    C12 = add(mul(X,  Cl, E),
             mul(Xi, Cr, E), E),
    C2 = add(C1, C12, E),
    G2 = v_add(Gl, v_mul(Xi, Gr, E), E),
    H2 = v_add(Hl, v_mul(X, Hr, E), E),
    make_ipa2(C2, A2, G2, B2, 
              H2, Q, E, [Cl, Cr|Cs], X, Xi).

get_gn(_, [G], _) -> G;
get_gn(X, G, E) ->
    S = length(G),
    S2 = S div 2,
    {Gl, Gr} = lists:split(S2, G),
    G2 = v_add(Gl, v_mul(X, Gr, E), E),
    get_gn(X, G2, E).
fold_cs(_, _, [C], _) -> C;
fold_cs(X, Xi, [Cl, Cr|Cs], E) ->
    add(
      add(mul(X, Cl, E),
          mul(Xi, Cr, E),
          E),
      fold_cs(X, Xi, Cs, E),
      E).
    

verify_ipa({AG, AB, Cs, AN, BN, CN}, %the proof
           B, G, H, Q, E) ->
    %we may need to decompress the proof at this point.
    C1 = hd(lists:reverse(Cs)),
    C1b = add(add(AG, commit(B, H, E), E), 
             mul(AB, Q, E), E),
    EB = eq(C1, C1b, E),
    if
        not(EB) -> false;
        true ->
    
            X = point_to_entropy(C1, E),
            Xi = basics:inverse(X, ?order),
            GN = get_gn(Xi, G, E),
            HN = get_gn(X, H, E),
            CNa = add(add(mul(AN, GN, E),
                          mul(BN, HN, E),
                          E),
                      mul(?mul(AN, BN), Q, E),
                      E),
            CNb = fold_cs(X, Xi, Cs, E),
            eq(CNa, CNb, E)
    end.

gen_point(E) ->
    secp256k1:to_jacob(
      secp256k1:gen_point(E)).
basis(S, E) ->
    G = lists:map(fun(_) ->
                           gen_point(E)
                   end, range(0, S)),
    H = lists:map(fun(_) ->
                           gen_point(E)
                   end, range(0, S)),
    Q = gen_point(E),
    {G, H, Q}.

range(X, X) -> [];
range(X, Y) when X < Y -> 
    [X|range(X+1, Y)].

test(1) ->
    A = range(100, 108),
    S = length(A),
    E = secp256k1:make(),
    {G, H, Q} = basis(S, E),
    Bv = [0,0,0,1,1,0,0,0],%103+104 = 207
    Bv2 = [1,0,0,0,0,1,0,0],%100+105 = 205
    Proof = make_ipa(
              A, Bv,%103+104 = 207
              G, H, Q, E),
    {_, 207, _, _, _, _} = Proof,
    Proof2 = make_ipa(
              A, Bv2,%103+104 = 207
              G, H, Q, E),
    true = verify_ipa(Proof, Bv, G, H, Q, E),
    true = verify_ipa(Proof2, Bv2, G, H, Q, E),
    success.