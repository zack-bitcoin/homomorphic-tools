-module(polynomial_commitments).
-export([test/1,
         coefficient_to_evaluation/2,
         evaluation_to_coefficient/2,
         dot_polys_c/3,
         mul_poly/3,
         subtract_poly/3,
         base_polynomial/2,
         add_poly/3,
         div_poly/3,
         eval_poly/3
        ]).

%basics:lrpow(B, E, N) B^E rem N

mod(X,Y)->(X rem Y + Y) rem Y.
pow(B, 0, _) -> 1;
pow(B, E, N) ->
    basics:lrpow(B, E, N).
mul(A, B, N) ->
    mod(A*B, N).
divide(A, B, N) ->
    B2 = basics:inverse(B, N),
    mul(A, B2, N).
add(A, B, N) ->
    mod(A+B, N).
sub(A, B, N) ->
    mod(A-B, N).
    

range(A, A) -> [];
range(A, B) when (A < B) -> 
    [A|range(A+1, B)].

eval_poly(X, P, Base) -> 
    eval_poly2(X, P, 0, Base).
eval_poly2(X, [], _, _) -> 0;
eval_poly2(X, [H|T], N, Base) -> 
    add(mul(H, pow(X, N, Base), Base),
        eval_poly2(X, T, N+1, Base),
        Base).

eval_poly_encrypted(X, P, E) ->
    eval_poly_encrypted2(X, P, 0, E).
eval_poly_encrypted2(_, [], _, _) ->
    infinity;
eval_poly_encrypted2(X, [H|T], N, E) ->
    Base = secp256k1:order(E),
    pedersen:add(
      pedersen:mul(
        H, pow(X, N, Base), E),
      eval_poly_encrypted2(X, T, N+1, E),
      E).


%works for coefficient form
%can work for evaluation form if you are certain the polynomials are the same length.
add_poly([], [], _) -> [];
add_poly([], X, _) -> X;
add_poly(X, [], _) -> X;
add_poly([A|AT], [B|BT], Base) ->
    [add(A, B, Base)|
      add_poly(AT, BT, Base)].
subtract_poly(A, B, Base) ->
    add_poly(A, neg_poly(B, Base), Base).

add_poly_encrypted([], [], _) -> [];
add_poly_encrypted([], X, _) -> X;
add_poly_encrypted(X, [], _) ->  X;
add_poly_encrypted([A|AT], [B|BT], E) -> 
    [pedersen:add(A, B, E)|
     add_poly_encrypted(AT, BT, E)].

%for evaluation form
add_poly_e([], [], _) -> [];
add_poly_e([A|AT], [B|BT], Base) ->
    [add(A, B, Base)|
      add_poly_e(AT, BT, Base)].
subtract_poly_e(A, B, Base) ->
    add_poly_e(A, neg_poly(B, Base), Base).

%works for coefficient form and evaluation form.
neg_poly([], _Base) -> [];
neg_poly([H|T], Base) -> 
    [sub(0, H, Base)|
     neg_poly(T, Base)].
mul_poly_c(_, [], _) -> [];
mul_poly_c(S, [A|T], Base) 
  when is_integer(S) -> 
    [mul(S, A, Base)|
     mul_poly_c(S, T, Base)].
mul_poly_encrypted(_, [], _) -> [];
mul_poly_encrypted(S, [A|T], E) -> 
    [pedersen:mul(S, A, E)|
     mul_poly_encrypted(S, T, E)].
div_poly_c(_, [], _) -> [];
div_poly_c(S, [A|T], Base) -> 
    %0 = A rem S,
    [divide(A, S, Base)|
     div_poly_c(S, T, Base)].

%for coefficient form, or evaluation in the case where the polynomials are the same length.
dot_polys_c([], [], _Base) -> [];
dot_polys_c([A|AT], [P|PT], Base) ->
    add_poly(mul_poly_c(A, P, Base),
             dot_polys_c(AT, PT, Base),
             Base).
%for encrypted mode. A is an elliptic point. P is a polynomial
dot_polys_e([], [], _) -> [];
dot_polys_e([A|AT], [P|PT], E) -> 
    add_poly_encrypted(
      mul_poly_encrypted(A, P, E),
      dot_polys_e(AT, PT, E),
      E).

pedersen_encode(As, Gs, E) ->
    lists:zipwith(
      fun(G, A) ->
              pedersen:mul(G, A, E)
      end, Gs, As).
    

%matrix_application([], Gs, E) ->
%    all_infinities(length(Gs));
matrix_application([H], [G], E) ->
    pedersen_encode(H, many(G, length(H)), E);
matrix_application([H|M], [G|Gs], E) ->
    %add_poly_encrypted(
    lists:zipwith(
      fun(A, B) -> pedersen:add(A, B, E) end,
      pedersen_encode(H, many(G, length(H)), E),
      matrix_application(M, Gs, E)).%,
      %E).

many(_, 0) -> [];
many(X, N) when (N > 0) -> 
    [X|many(X, N-1)].
     
     


%for coefficient form.
mul_poly([A], B, Base) ->
    mul_poly_c(A, B, Base);
mul_poly([A|AT], B, Base) ->
    add_poly(mul_poly_c(A, B, Base),
             mul_poly(AT, [0|B], Base),
             Base).

is_all_zeros([]) -> true;
is_all_zeros([0|T]) -> 
    is_all_zeros(T);
is_all_zeros(_) -> false.

div_poly(A, [1], _Base) -> A;
%div_poly([0|A], [0|B], Base) -> 
%    div_poly(A, B, Base);
%div_poly([0], _, _) -> [0];
%div_poly([0], _, _) -> [];
%div_poly(A, B, _) 
%  when (length(A) < length(B)) ->
%    fail;
div_poly(A, B, Base) -> 
    D = length(A) - length(B),
    %io:fwrite(D),
    AllZeros = is_all_zeros(A),
    if
        AllZeros -> many(0, D+1);
        true ->
            %io:fwrite({A, B}),
            LA = hd(lists:reverse(A)),
            LB = hd(lists:reverse(B)),
            M = divide(LA, LB, Base),
            BM = mul_poly_c(M, B, Base),
            BM2 = all_zeros(D) ++ BM,
            A2 = subtract_poly(A, BM2, Base),
           %A3 = remove_trailing_zeros(A2),
            A3 = lists:reverse(tl(lists:reverse(A2))),
    %io:fwrite({A, B, M, A2, A3}),
    %io:fwrite({A, BM2, A2}),
            div_poly(A3, B, Base) ++ [M]
    end.
    

%for evaluation form
mul_poly_e([], [], _Base) -> [];
mul_poly_e([A|AT], [B|BT], Base) ->
    [mul(A, B, Base)|
     mul_poly_e(AT, BT, Base)].
%div_poly_e([], [], _Base) -> [];
%div_poly_e([0|AT], [0|BT], Base) ->
%    1=2,
%     mul_poly_e(AT, BT, Base);
%div_poly_e([A|AT], [B|BT], Base) ->
%    [divide(A, B, Base)|
%     mul_poly_e(AT, BT, Base)].
    

all_zeros(0) -> [];
all_zeros(N) when (N > 0) -> 
    [0|all_zeros(N-1)].

all_infinities(0) -> [];
all_infinities(N) when (N > 0) -> 
    [infinity|all_infinities(N-1)].

base_polynomial(Intercept, Base) ->
    %Rest = all_zeros(Length - 2),
    [sub(0, Intercept, Base), 1].%|Rest].

remove_element(X, [X|T]) -> T;
remove_element(X, [A|T]) -> 
    [A|remove_element(X, T)].
lagrange_polynomials(Many, Base) ->
    R = range(1, Many+1),
    lists:map(fun(X) -> 
                      lagrange_polynomial(
                        R, Many, X, Base)
              end, R).
lagrange_polynomial(R, Many, N, Base) ->
    R2 = remove_element(N, R),
    Ps = lists:map(fun(X) ->
                           base_polynomial(X, Base)
                   end, R2),
    P = lists:foldl(fun(X, A) ->
                            mul_poly(X, A, Base)
                    end, [1],
                    Ps),
    Ds = lists:map(fun(X) ->
                           sub(N, X, Base)
                               %N - X
                   end, R2),
    D = lists:foldl(fun(X, A) ->
                            %X * A
                            mul(X, A, Base)
                    end, 1, Ds),
    div_poly_c(D, P, Base).
coefficient_to_evaluation(L, Base) ->
    coefficient_to_evaluation(L, 0, Base).
coefficient_to_evaluation(L, M, Base) ->
    %ex L = [1, 2, 3] -> L(x) = 1 + 2*x + 3*x*x.
    M2 = max(length(L), M),
    R = range(1, M2+1),
    lists:map(fun(X) -> eval_poly(X, L, Base) end, R).
evaluation_to_coefficient(L, Base) ->
    R = range(0, length(L)),
    LP = lagrange_polynomials(length(L), Base),
    L4 = evaluation_to_coefficients2(L, LP, Base),
    P = lists:foldl(fun(X, A) ->
                           add_poly(X, A, Base)
                   end, [], L4),
    remove_trailing_zeros(P).
evaluation_to_coefficients2([], [], _) -> [];
evaluation_to_coefficients2(
  [I|IT], [P|PT], Base) ->
    [mul_poly_c(I, P, Base)|
     evaluation_to_coefficients2(IT, PT, Base)].
remove_leading_zeros([0|T]) ->
    remove_leading_zeros(T);
remove_leading_zeros(X) -> X.
remove_trailing_zeros(L) ->
    L2 = lists:reverse(L),
    L3 = remove_leading_zeros(L2),
    lists:reverse(L3).

mul_list([], [], _) -> [];
mul_list([S|ST], [G|GT], Base) -> 
    [mul(S, G, Base)|
    %[S*G|
     mul_list(ST, GT, Base)].
phi_list(N, Base) ->
    phi_list(N, 1, 1, Base).
phi_list(0, A, B, _) ->
    [A, B];
phi_list(N, A, B, Base) ->
    [A|phi_list(N-1, B, add(A, B, Base), Base)].

powers(X, N, Base) ->
    powers2(X, 1, N, Base).
powers2(_, _, 0, _) -> [];
powers2(X, A, N, Base) ->
    [A|powers2(X, mul(A, X, Base), N-1, Base)].
    


test(1) ->
    Base = 19,
    C = [0, 1],
    E = coefficient_to_evaluation(C, Base),
    %io:fwrite({E}),
    C = evaluation_to_coefficient(E, Base),

    C1 = [1,2],%1 + 2x
    C2 = [2,1],%2 + x
    C3 = [2, 5, 2],%2 + 5x + 2x*x
    E1 = coefficient_to_evaluation(C1, 3, Base),
    E2 = coefficient_to_evaluation(C2, 3, Base),
    E3 = coefficient_to_evaluation(C3, Base),
    E3 = mul_list(E1, E2, Base),
    success;
test(2) ->
    Base = 22953686867719691230002707821868552601124472329079,
    %E = [1,1,2,3,5,8,13],
    E = phi_list(100, Base),
    C = evaluation_to_coefficient(E, Base),
    E = coefficient_to_evaluation(C, Base),
    E1 = tl(E),
    E2 = tl(tl(E)),

    C1 = evaluation_to_coefficient(E1, Base),
    C2 = evaluation_to_coefficient(E2, Base),

    C3 = subtract_poly(
           subtract_poly(C2, C1, Base),
           C, Base),
    E3 = coefficient_to_evaluation(C3, Base),

    E3b = subtract_poly(
           subtract_poly(E2, E1, Base),
           E, Base),
    C3b = evaluation_to_coefficient(E3b, Base),
    
    {lists:reverse(E3), lists:reverse(E3b), C3, C3b};
%[E, C, hd(lists:reverse(E))].

test(3) ->
    Base = 23,
    P1 = [2, 3],
    P2 = [0, 5],
    P3 = mul_poly(P1, P2, Base),
    P1 = div_poly(P3, P2, Base),
    P2 = div_poly(P3, P1, Base),
    success;
    
test(4) -> 
    %accessing a variable without telling which one.

    %R1CS r 1 constraint systems explained here https://medium.com/@VitalikButerin/quadratic-arithmetic-programs-from-zero-to-hero-f6d558cea649
    % for a computation, rewrite using only +, -, *, /
    % calculate all the intermediate values.
    % find vector s and matrices a, b, and c such that (s dot a) * (s dot b) = (s dot c),
    % vector s is the values being passed through the computation. It is a witness that the computation happened.
    % some of the s values can be un-blinded to reveal aspects of the computation.

    % s is elliptic curves. a, b, and c are matricies of integers that we multiply the curve points by.

    %A = [5, 7],
    E = secp256k1:make(),
    %G = pedersen:gen_point(E),
    %H = pedersen:gen_point(E),
    %(5 - r)*(7-r) = (hv1 - r)*(hv2 - r)

    %l1 = 5 - r -> 5 = l1 + r
    %l2 = 7 - r -> 7 = l2 + r
    %r1 = hv1 - r -> hv1 = r1 + r
    %r2 = hv2 - r -> hv2 = r2 + r

    %l1 * l2 = r1 * r2

    %    Ao = Al * Ar
    %l3 = l1 * l2 
    %r3 = r1 * r2
    %l3 = 1 * r3
    %s = [one, l1,l2,l3, r1,r2,r3]

    %for this example, R=2
    %S plaintext
    Base = secp256k1:order(E),
    %UnblindedWitness = [1, 3, 5, 15, 5, 3, 15],
    %R = 20,
    R = random:uniform(Base),
    Secret1 = sub(5, R, Base),
    Secret2 = sub(7, R, Base),
    Secret3 = Secret1 * Secret2,
    UnblindedWitness = 
        [1, Secret1, Secret2, 
         Secret3, Secret2, Secret1, Secret3],
    [One, L1, L2, L3, R1, R2, R3] = 
        UnblindedWitness,
    S = UnblindedWitness,
    %S = [51|tl(UnblindedWitness)],
    %if one, l1, and l2 are public, then we know that r1 and r2 are the same set.
    %(s dot a) * (s dot b) = (s dot c)
  %[0,1,0,0,0,0,0],[0,0,1,0,0,0,0],[0,0,0,1,0,0,0]
  %[0,0,0,0,1,0,0],[0,0,0,0,0,1,0],[0,0,0,0,0,0,1]
  %[1,0,0,0,0,0,0],[0,0,0,0,0,0,1],[0,0,0,1,0,0,0]
    
    %transform to polynomial syntax.
    %7 sets of 3 order-3 polynomials

    %A
    %poly(0,0,1), poly(1,0,0), poly(0,0,0) ...
    %
    P001 = evaluation_to_coefficient(
          [0,0,1], Base),
    P100 = evaluation_to_coefficient(
          [1,0,0], Base),
    P000 = [0,0,0],
    P010 = evaluation_to_coefficient(
          [0,1,0], Base),
    P101 = evaluation_to_coefficient(
          [1,0,1], Base),
    PA = [P001, P100, P000, P000, 
          P010, P000, P000, []],
    PB = [P000, P000, P100, P000, 
          P000, P010, P001, []],
    PC = [P000, P000, P000, P101, 
          P000, P000, P010, []],
    As = dot_polys_c(S ++ [0], PA, Base),
    %S = [S1, S2, S3], PA = [[P11, P12, P13] ...
    %[[S1 * P11, S1 * P12, S1 * P13], [S2 * P21 ...
    %[[S1P11 + S2P21 + S3P31, S1P12 + ...
    Bs = dot_polys_c(S ++ [0], PB, Base),
    Cs = dot_polys_c(S ++ [0], PC, Base),
    MulAB = mul_poly(As ++ [0], Bs, Base),%seems like there is no way to calculate this over the domain of pedersen commitments

    % pedersen commitments support addition, multiplication by a constant.
    % IPA
    %C = A*G + B*H + (A*B)q

    ZeroPoly = subtract_poly(MulAB, Cs, Base),
    ZD0 = lists:map(
            fun(R) ->
                    base_polynomial(R, Base)
            end, [1,2,3]),
    ZD = lists:foldl(fun(A, B) ->
                             mul_poly(A, B, Base)
                     end, [1], ZD0),
    H = div_poly(ZeroPoly, ZD, Base),
    io:fwrite({H}),

    %sanity check.
    ZeroPoly = mul_poly(H, ZD, Base),



    {Gs, Hs, Q} = pedersen:basis(length(S)+1, E),
    CommitS = pedersen:commit(S++[0], Gs, E),
    CommitH = pedersen:commit(H++[0], Hs, E),
    %commit to S.
    %commit to H. (ZeroPoly/ZD)
    %Choose an R based on those commitments.
    %
    <<Ran:256>> = pedersen:hash(
          <<(pedersen:c_to_entropy(CommitS)):256,
            (pedersen:c_to_entropy(CommitH)):256>>),
    %check polynomials match with a random point
    true = (mul(eval_poly(Ran, H, Base),
                eval_poly(Ran, ZD, Base),
                Base) ==
                eval_poly(Ran, ZeroPoly, Base)),
    true = (eval_poly(Ran, ZeroPoly, Base) ==
                sub(mul(eval_poly(Ran, As, Base),
                      eval_poly(Ran, Bs, Base), 
                     Base),
                    eval_poly(Ran, Cs, Base),
                    Base)),

    %H * ZD = ZeroPoly = (A * B) - C

    %they already know ZD, PA, PB, PC
    %if you send an encoded version of S, they can calculate encoded versions of As, Bs, and Cs.
    ES = lists:zipwith(
           fun(G, A) ->
                   pedersen:mul(G, A, E)
           end, Gs, S++[0]),
    CommitS = pedersen:sum_up(ES, E),
    ES = pedersen_encode(S++[0], Gs, E),
    EAs = dot_polys_e(ES, PA, E),
    EBs = dot_polys_e(ES, PB, E),
    ECs = dot_polys_e(ES, PC, E),

    %H(R) * ZD(R) = (As(R) * Bs(R)) - C(R)

    %CommitA = pedersen:sum_up(EAs, E),


    {Gs2, Hs2, Q2} = pedersen:basis(4, E),
    %io:fwrite({As, powers(Ran, length(As), Base), Gs2}),
    ProofA = 
        pedersen:make_ipa(
          As++[0], powers(Ran, 4, Base),
          Gs2, Hs2, Q2, E),
    %io:fwrite({element(2, ProofA),
    %           eval_poly(Ran, As, Base)}),
    ProofB = 
        pedersen:make_ipa(
          Bs++[0], powers(Ran, 4, Base),
          Gs2, Hs2, Q2, E),
    ProofC = 
        pedersen:make_ipa(
          Cs++[0], powers(Ran, 4, Base),
          Gs2, Hs2, Q2, E),

    ProofH = 
        pedersen:make_ipa(
          H ++ [0], powers(Ran, 4, Base),
          Gs2, Hs2, Q2, E),
          
    true =
        mul(element(2, ProofH),
            eval_poly(Ran, ZD, Base),
           Base) ==
        sub(
          mul(element(2, ProofA),
              element(2, ProofB),
              Base),
          element(2, ProofC),
          Base),

    %io:fwrite({EAs, As}),
    %CommitA2 = pedersen:commit(As, Gs, E),
    %GAs = matrix_application(PA, Gs, E),
    %CommitA2 = pedersen:commit(As, GAs, E),

    %io:fwrite({%matrix_application(PA, Gs, E),
    %           CommitA, CommitA2}),


    %evaluate ECs(R), decrypt this.
    %use an inner product argument to show that (A*B)(R) is the same value.


    %they choose a random number R, and you need to use an inner product argument to show that C = A*B




    %they choose a random number R, and you need to use an inner product argument to show that C = A*B.
    % IPA format: C = A*G + B*H + (A*B)q
    % A*G is the sum over the encoded As, evaluated at (r).
    % B*H is the sum over the encoded Bs, evaluated at (r).
    % (A*B)(r) is S dot PC evaluated at R.

    %send a proof of (ZeroPoly/ZD)(r).
    %send a proof of As(r) and Bs(r),
    %they can calculate ZD(r).

    %they check that ((A*B)(r) - As(r) - Bs(r))/(ZD(r)) == (ZeroPoly/ZD)(r)
    
    %so the only thing you need to send is C.

    %they check that C = A*G(R) + B*H(R) + (A*B)q

    %H(x) = ZeroPoly(x)/ZD(x)


    {H, lists:nth(5, ES)};
test(5) -> 
    %checking that pedersen commitments are deterministic, no matter whether they are created directly, or via addition, or multiplication.
    %also checks that zipwith is using the same order as pedersen:commit.
    E = secp256k1:make(),
    Base = secp256k1:order(E),
    V = [3,4,6],
    {Gs, Hs, Q} = pedersen:basis(length(V), E),
    EV = pedersen_encode(V, Gs, E),
    Commit = pedersen:commit(V, Gs, E),
    Commit = pedersen:sum_up(EV, E),
    Commit2 = pedersen:add(Commit, Commit, E),
    V2 = add_poly(V, V, Base),
    V2 = [6, 8, 12],
    Commit2 = pedersen:commit([6, 8, 12], Gs, E),
    Commit5 = pedersen:mul(Commit, 5, E),
    Commit5 = pedersen:commit([15, 20, 30], Gs, E),
    
    %check add_poly_encrypted
    EV2 = add_poly_encrypted(EV, EV, E),
    Commit2 = pedersen:sum_up(EV2, E),

    %check mul_poly_encrypted
    G1M = many(hd(Gs), length(Gs)),
    V5 = mul_poly_c(5,V,Base),
    EV5b = pedersen_encode(V5, G1M, E),
    Commit5b = pedersen:sum_up(EV5b, E),
    Commit5b = pedersen:commit(V5, G1M, E),
    EV5b = mul_poly_encrypted(
            hd(Gs), V5, E),

    C23 = mul_poly_c(hd(V), [2,3], Base),
    EC23b = pedersen:commit(C23, [hd(Gs),hd(Gs)], E),
    EC23a = mul_poly_encrypted(hd(EV), [2, 3], E),
    EC23b = pedersen:sum_up(EC23a, E),

    %check dot_polys_e
    M1 = [[3,1],[0,0],[0,2]],
    M0 = [[1,0],[0,0],[0,0]],
    As = dot_polys_c(V, M1, Base),%2
    As = [hd(V) * 3,
          hd(V) + (hd(tl(tl(V))) * 2)],
    EAs = dot_polys_e(EV, M1, E),%2
    EAs = [pedersen:mul(hd(EV), 3, E),
           pedersen:add(hd(EV), 
                        pedersen:mul(hd(tl(tl(EV))), 2, E), 
                        E)],
    EAs = [pedersen:mul(hd(Gs), hd(V) * 3, E),
           pedersen:add(
             pedersen:mul(hd(Gs), hd(V), E),
             pedersen:mul(hd(tl(tl(Gs))), 
                          hd(tl(tl(V))) * 2, E),
             E)],
    Gsd = dot_polys_e(Gs, M1, E),%2
    Gsd = [pedersen:mul(hd(Gs), 3, E),
           pedersen:add(
             hd(Gs),
             pedersen:mul(hd(tl(tl(Gs))), 2, E),
             E)],
    EAs2 = pedersen_encode(As, Gsd, E),%NOT equal to EAs.
    %EAs2 = EAs,
    %EAs2 = [pedersen:mul(hd(Gsd), hd(As), E),
    %        infinity],
    %hd(gsd) * hd(As) 
    %-> (hd(gs) * (hd(hd(M1)))) * (hd(V) * hd(hd(M1)))
    % -> (G1 * 2) * (3 * 2) -> G1 * 12
    %EAs2 = [pedersen:mul(hd(Gs), hd(V) * hd(hd(M1)) * hd(hd(M1)), E), infinity],
    %EAs2 = [pedersen:mul(hd(Gsd), hd(V) * hd(hd(M1)), E), infinity],

    %EAs3 = pedersen_encode(As, [hd(Gs), infinity], E),
    %EAs3 = pedersen_encode([hd(V), 0], Gsd, E),
    %%EAs3 = pedersen_encode(As, Gsd, E),
    %EAs3 = [pedersen:mul(hd(Gsd), hd(V), E),
    %        infinity],

    %io:fwrite({As, EAs, EAs2, EAs3}),
    ok;
test(6) -> 
    %a cleaner zk proof
    E = secp256k1:make(),
    Base = secp256k1:order(E),
    R = random:uniform(Base),

    %this time lets mix a list of 3 things.
    % 5*7*11 = s1*s2*s3

    % s
    % one = 1
    % l1 = 5
    % l2 = 7
    % l3 = 11
    % l4 = l1 * l2
    % l5 = l3 * 14
    % r1 = ?
    % r2 = ?
    % r3 = ?
    % r4 = r1 * r2
    % r5 = r3 * r4
    
    S5 = sub(5, R, Base),
    S7 = sub(7, R, Base),
    S11 = sub(11, R, Base),
    S35 = mul(S5, S7, Base),
    S35_11 = mul(S35, S11, Base),
    S55 = mul(S11, S5, Base),
    Padding = [0,0,0,0,0],
    PolyPadding = [[],[],[],[],[]],
    S = [1, 
         S5, S7, S11, S35, S35_11,
         S11, S5, S7, S55, S35_11] 
        ++ Padding,
    16 = length(S),
    %[one, 5, 7, 11, r4, r5, l1, l2, l3, l4, l5]
    
    %C = A dot B
    %l4 = l1 * l2
    %l5 = l3 * l4
    %r4 = r1 * r2
    %r5 = r3 * r4
    %l5 = 1 * r5

    %[one, 5, 7, 11, r4, r5, l1, l2, l3, l4, l5]
    %l4 = l1 * l2
    %[0,0,0,0,0,0,0,0,0,1,0] =
    %[0,0,0,0,0,0,1,0,0,0,0] *
    %[0,0,0,0,0,0,0,1,0,0,0]

    %[one, 5, 7, 11, r4, r5, l1, l2, l3, l4, l5]
    %l5 = l3 * l4
    %[0,0,0,0,0,0,0,0,0,0,1] =
    %[0,0,0,0,0,0,0,0,1,0,0] *
    %[0,0,0,0,0,0,0,0,0,1,0]
    
    %[one, 5, 7, 11, r4, r5, l1, l2, l3, l4, l5]
    %r4 = r1 * r2
    %[0,0,0,0,1,0,0,0,0,0,0] =
    %[0,1,0,0,0,0,0,0,0,0,0] *
    %[0,0,1,0,0,0,0,0,0,0,0]

    %[one, 5, 7, 11, r4, r5, l1, l2, l3, l4, l5]
    %r5 = r3 * r4
    %[0,0,0,0,0,1,0,0,0,0,0] =
    %[0,0,0,0,1,0,0,0,0,0,0] *
    %[0,0,0,1,0,0,0,0,0,0,0]

    %[one, 5, 7, 11, r4, r5, l1, l2, l3, l4, l5]
    %l5 = 1 * r5
    %[0,0,0,0,0,0,0,0,0,0,1] =
    %[1,0,0,0,0,0,0,0,0,0,0] *
    %[0,0,0,0,0,1,0,0,0,0,0]

    %A
    %[0,0,0,0,0,0,1,0,0,0,0] 
    %[0,0,0,0,0,0,0,0,1,0,0] 
    %[0,1,0,0,0,0,0,0,0,0,0] 
    %[0,0,0,0,1,0,0,0,0,0,0] 
    %[1,0,0,0,0,0,0,0,0,0,0] 

    %B
    %[0,0,0,0,0,0,0,1,0,0,0]
    %[0,0,0,0,0,0,0,0,0,1,0]
    %[0,0,1,0,0,0,0,0,0,0,0]
    %[0,0,0,1,0,0,0,0,0,0,0]
    %[0,0,0,0,0,1,0,0,0,0,0]

    %C
    %[0,0,0,0,0,0,0,0,0,1,0] 
    %[0,0,0,0,0,0,0,0,0,0,1] 
    %[0,0,0,0,1,0,0,0,0,0,0] 
    %[0,0,0,0,0,1,0,0,0,0,0] 
    %[0,0,0,0,0,0,0,0,0,0,1] 

    P0 = [0,0,0,0,0],
    Ppair = evaluation_to_coefficient(
              [0,1,0,0,1], Base),
    P1 = evaluation_to_coefficient(
              [1,0,0,0,0], Base),
    P2 = evaluation_to_coefficient(
              [0,1,0,0,0], Base),
    P3 = evaluation_to_coefficient(
              [0,0,1,0,0], Base),
    P4 = evaluation_to_coefficient(
              [0,0,0,1,0], Base),
    P5 = evaluation_to_coefficient(
              [0,0,0,0,1], Base),

    PA = [P5, P3, P0, P0, P4, P0, P1, P0, P2, P0, P0] ++ PolyPadding,
    PB = [P0, P0, P3, P4, P0, P5, P0, P1, P0, P2, P0] ++ PolyPadding,
    PC = [P0, P0, P0, P0, P3, P4, P0, P0, P0, P1, Ppair] ++ PolyPadding,
  
    Padding2 = tl(tl(Padding)),
    As = dot_polys_c(S, PA, Base) ++ Padding2,
    Bs = dot_polys_c(S, PB, Base) ++ Padding2,
    Cs = dot_polys_c(S, PC, Base) ++ Padding2,

    MulAB = mul_poly(As, Bs, Base),
    ZeroPoly = subtract_poly(MulAB, Cs, Base),
    ZD0 = lists:map(
            fun(R) ->
                    base_polynomial(R, Base)
            end, [1,2,3,4,5]),
    ZD = lists:foldl(fun(A, B) ->
                             mul_poly(A, B, Base)
                     end, [1], ZD0),
    H = div_poly(ZeroPoly, ZD, Base),
    ZeroPoly = mul_poly(H, ZD, Base),
    
    {Gs, Hs, Q} = pedersen:basis(length(S), E),
    CommitS = pedersen:commit(S, Gs, E),
    CommitH = pedersen:commit(H, Hs, E),

    <<Ran:256>> = pedersen:hash(
          <<(pedersen:c_to_entropy(CommitS)):256,
            (pedersen:c_to_entropy(CommitH)):256>>),

    true = (mul(eval_poly(Ran, H, Base),
                eval_poly(Ran, ZD, Base),
                Base) ==
                eval_poly(Ran, ZeroPoly, Base)),
    true = (eval_poly(Ran, ZeroPoly, Base) ==
                sub(mul(eval_poly(Ran, As, Base),
                      eval_poly(Ran, Bs, Base), 
                     Base),
                    eval_poly(Ran, Cs, Base),
                    Base)),

    ES = pedersen_encode(S, Gs, E),
    CommitS = pedersen:sum_up(ES, E),
    EAs = dot_polys_e(ES, PA, E),
    EBs = dot_polys_e(ES, PB, E),
    ECs = dot_polys_e(ES, PC, E),

    {Gs2, Hs2, Q2} = pedersen:basis(8, E),
    Powers = powers(Ran, 8, Base),
    %io:fwrite({As, Powers}),
    ProofA = 
        pedersen:make_ipa(
          As, Powers,
          Gs2, Hs2, Q2, E),
    ProofB = 
        pedersen:make_ipa(
          Bs, Powers,
          Gs2, Hs2, Q2, E),
    ProofC = 
        pedersen:make_ipa(
          Cs, Powers,
          Gs2, Hs2, Q2, E),
    ProofH = 
        pedersen:make_ipa(
          lists:reverse(tl(tl(lists:reverse(H)))), Powers,
          Gs2, Hs2, Q2, E),

    true =
        mul(element(2, ProofH),
            eval_poly(Ran, ZD, Base),
           Base) ==
        sub(
          mul(element(2, ProofA),
              element(2, ProofB),
              Base),
          element(2, ProofC),
          Base),

    success.
