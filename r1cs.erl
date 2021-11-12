-module(r1cs).
-export([
         mul_poly/2,
         lagrange_polynomials/1,
         test/1,
         test2/1]).

-record(encrypted, {commitment, value, blinding, g, h, e}).

encrypt(V, G, H, E) ->
    B = random:uniform(elliptic:det_pow(2, 256))-1,
    C = pedersen:commit([V, B], [G, H], E),
    #encrypted{commitment = C, value = V, 
               blinding = B, g = G, h = H, 
               e = E}.
check(V = #encrypted{commitment = C, value = V,
                  blinding = B, g = G, h = H,
                 e = E}) ->
    C == pedersen:commitment([V, B], [G, H], E).
    
add(A = #encrypted{value = AV,
                   blinding = AB,
                   commitment = AC,
                   g = G,
                   h = H,
                   e = E},
    B = #encrypted{value = BV,
                blinding = BB,
                commitment = BC,
                g = G,
                h = H,
                e = E}) ->
    C = pedersen:add(AC, BC, E),
    V2 = pedersen:fadd(AV, BV, E),
    B2 = pedersen:fadd(AB, BB, E),
    C = pedersen:commit([V2, B2], [G, H], E),
    #encrypted{
                value = V2,
                blinding = B2,
                commitment = C,
                g = G, h = H, e = E}.
mul(M, A = #encrypted{
         value = V, blinding = B,
         commitment = C, g = G,
         h = H, e = E}) ->
    C2 = pedersen:mul(C, M, E),
    V2 = pedersen:fmul(V, M, E),
    B2 = pedersen:fmul(B, M, E),
    C2 = pedersen:commit([V2, B2], [G, H], E),
    #encrypted{
                value = V2,
                blinding = B2,
                commitment = C2,
                g = G, h = H, e = E};
mul(A, B) when (is_integer(A) and
                is_integer(B)) ->
    A*B.
                
   
mul_list([], []) -> [];
mul_list([S|ST], [G|GT]) -> 
    [mul(S, G)|
     mul_list(ST, GT)].
add_up([X]) -> X;
add_up([A, B|T]) -> 
    add_up([add(A, B)|T]).

dot(S, G) ->
    add_up(mul_list(S, G)).

list_pow([], [], _E) -> 1;
list_pow([W|WT], [A|AT], E) when is_integer(W) -> 
    X = pedersen:fadd(0, elliptic:det_pow(W, A), E),
    pedersen:fmul(X, list_pow(WT, AT, E), E).

%homomorphic_list_pow([], [], _) -> 1;
%homomorphic_list_pow([W|WT], [A|AT], E) -> 
%    X = pedersen:mul(W, A, E),
%    pedersen:mul(X, 



test(1) ->
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

    %             Ao = Al * Ar
    %l3 = l1 * l2 
    %r3 = r1 * r2
    %l3 = 1 * r3
    %     public, private, intermediate
    %s = [one, l1,l2,l3, r1,r2,r3]

    %for this example, R=2
    %S plaintext
    %Base = 22953686867719691230002707821868552601124472329079,
    Base = secp256k1:order(E),
    UnblindedWitness = [1, 3, 5, 15, 5, 3, 15],
    [One, L1, L2, L3, R1, R2, R3] = UnblindedWitness,
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
    P001 = polynomial_commitments:
        evaluation_to_coefficient(
          [0,0,1], Base),
    P100 = polynomial_commitments:
        evaluation_to_coefficient(
          [1,0,0], Base),
    P000 = [0,0,0],
    P010 = polynomial_commitments:
        evaluation_to_coefficient(
          [0,1,0], Base),
    P101 = polynomial_commitments:
        evaluation_to_coefficient(
          [1,0,1], Base),
    PA = [P001, P100, P000, P000, 
          P010, P000, P000],
    PB = [P000, P000, P100, P000, 
          P000, P010, P001],
    PC = [P000, P000, P000, P101, 
          P000, P000, P010],

    As = polynomial_commitments:
        dot_polys_c(S, PA, Base),
    Bs = polynomial_commitments:
        dot_polys_c(S, PB, Base),
    Cs = polynomial_commitments:
        dot_polys_c(S, PC, Base),
    MulAB = 
        polynomial_commitments:
        mul_poly(As, Bs, Base),

    ZeroPoly = polynomial_commitments:
        subtract_poly(
          MulAB, Cs, Base),
    %Z2 = polynomial_commitments:
    %    coefficient_to_evaluation(ZeroPoly, Base),
    ZD0 = lists:map(fun(R) ->
                           polynomial_commitments:
                               base_polynomial(
                                 R, Base)
                   end, [1,2,3]),
    ZD = lists:foldl(fun(A, B) ->
                             polynomial_commitments:
                                 mul_poly(
                                   A, B, Base)
                     end, [1], ZD0),
    %ZD2 = polynomial_commitments:
    %    coefficient_to_evaluation(ZD, Base), 
    H = polynomial_commitments:
        div_poly(ZeroPoly, ZD, Base),
        %div_poly_e(Z2, ZD2, Base),
    ZeroPoly = polynomial_commitments:
        mul_poly(H, ZD, Base),

    


    {H}.
   
    %{Gs, Hs, _} = pedersen:basis(length(A), E),

    %Witness = 
    %    [encrypt(One, G, H, E),
    %     encrypt(L1, G, H, E),
    %     encrypt(L2, G, H, E),
    %     encrypt(L3, G, H, E),
    %     encrypt(R1, G, H, E),
    %     encrypt(R2, G, H, E),
    %     encrypt(R3, G, H, E)],
    %[EOne, EL1, EL2, EL3, ER1, ER2, ER3] = Witness,
    %Af = dot(A, Witness),
    %Bf = dot(B, Witness),
    %Cf = dot(C, Witness),
    %true = ((Af#encrypted.value * 
    %             Bf#encrypted.value)
    %        == Cf#encrypted.value),




    %verification
    %true = check(EOne),
    %true = check(EL1),
    %true = check(EL2),
    
    
    

    %success;


    %pi_i (A1_i - Challenge) = pi_i (A2_i - Challenge)


%(A - x) * (B - x) = (C - x) * (D - x)

%multiplicative constraints. x * y = z

%linear constraints 
%secret variables with cleartext weights
%a*x + b*y + c*z ... = 0
    %ok.


             
%coefficient format
% f(x) = 4 + 3x - 2x*x -> [4, 3, -2]

%in coefficient format 

%evaluation format
% f(1) = 5, f(2) = 2, f(3) = -5 -> [5, 2, -5]

%in either format you can add polynomials by adding the vectors.
%in evaluation format you can multiply polynomials by multiplying the points together

coefficient_to_evaluation(L) ->
    coefficient_to_evaluation(L, 0).
coefficient_to_evaluation(L, M) ->
    %ex L = [1, 2, 3] -> L(x) = 1 + 2*x + 3*x*x.
    M2 = max(length(L), M),
    R = range(1, M2+1),
    lists:map(fun(X) -> eval_poly(X, L) end, R).
evaluation_to_coefficient(L) ->
    R = range(0, length(L)),
    LP = lagrange_polynomials(length(L)),
    GCD = lists:foldl(fun({_, X}, A) ->
                             basics:gcd_euclid(X, A)
                     end, 1, LP),
    Pi = lists:foldl(fun({_, X}, A) ->
                             X*A
                     end, 1, LP),
    LCM = Pi div GCD,
    %io:fwrite(LCM),
    L3 = lists:map(fun({P, D}) ->
                           M = LCM div D,
                           mul_poly_c(M, P)
                   end, LP),
    %io:fwrite(L3),
    L4 = evaluation_to_coefficients2(L, L3),
    %io:fwrite(L4),
    P = lists:foldl(fun(X, A) ->
                           add_poly(X, A)
                   end, [], L4),
    %io:fwrite({LCM, P, L4}),
    Result = div_poly_c(LCM, P),
    remove_trailing_zeros(Result).
evaluation_to_coefficients2([], []) -> [];
evaluation_to_coefficients2([I|IT], [P|PT]) ->
    [mul_poly_c(I, P)|
     evaluation_to_coefficients2(IT, PT)].

remove_leading_zeros([0|T]) ->
    remove_leading_zeros(T);
remove_leading_zeros(X) -> X.


remove_trailing_zeros(L) ->
    L2 = lists:reverse(L),
    L3 = remove_leading_zeros(L2),
    lists:reverse(L3).

div_evaluation_polys([], []) -> [];
div_evaluation_polys([A|AT], [B|BT]) -> 
    0 = A rem B,
    [A div B|div_evaluation_polys(AT, BT)].

test2(1) ->    
    C = [-3, 7, 2],
    E0 = coefficient_to_evaluation(C),
    E = coefficient_to_evaluation(C, 4),
    %io:fwrite({E0, E}),
    %3, 5
    C20 = evaluation_to_coefficient(E),
    %io:fwrite({C, E, C2}),
    C = C20,
    %E.

    C1 = [1,2],%1 + 2x
    C2 = [2,1],%2 + x
    C3 = [2, 5, 2],%2 + 5x + 2x*x

    E1 = coefficient_to_evaluation(C1, 3),
    E2 = coefficient_to_evaluation(C2, 3),
    E3 = coefficient_to_evaluation(C3),
    E3 = mul_list(E1, E2),
    {E1, E2, E3};
test2(2) -> 
    %polynomial commitment.
    %{coefficient_to_evaluation([2,-1,1]),
    evaluation_to_coefficient([1,1,2]).
