-module(r1cs).
-export([
         mul_poly/2,
         lagrange_polynomials/1,
         test/1,
         test/0]).

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
    %[S*G|
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
    G = pedersen:gen_point(E),
    H = pedersen:gen_point(E),
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
    UnblindedWitness = [1, 3, 5, 15, 5, 3, 15],
    [One, L1, L2, L3, R1, R2, R3] = UnblindedWitness,
    %if one, l1, and l2 are public, then we know that r1 and r2 are the same set.
    %(s dot a) * (s dot b) = (s dot c)
  %[0,1,0,0,0,0,0],[0,0,1,0,0,0,0],[0,0,0,1,0,0,0]
  %[0,0,0,0,1,0,0],[0,0,0,0,0,1,0],[0,0,0,0,0,0,1]
  %[1,0,0,0,0,0,0],[0,0,0,0,0,0,1],[0,0,0,1,0,0,0]

    %This is 9 inner products. We just need to compress them.

    %sum up
    A = [1,1,0,0,1,0,0],%15
    B = [0,0,1,0,0,1,1],%15^2
    AB = [1,1,1,0,1,1,1],
    C = [0,0,0,2,0,0,1],%15^3

    %sanity check
    true = ((list_pow(A, UnblindedWitness, E)
            * list_pow(B, UnblindedWitness, E))
            %(list_pow(AB, UnblindedWitness, E)
            == list_pow(C, UnblindedWitness, E)),

    %lists


   
    {Gs, Hs, _} = pedersen:basis(length(A), E),

    Witness = 
        [encrypt(One, G, H, E),
         encrypt(L1, G, H, E),
         encrypt(L2, G, H, E),
         encrypt(L3, G, H, E),
         encrypt(R1, G, H, E),
         encrypt(R2, G, H, E),
         encrypt(R3, G, H, E)],
    [EOne, EL1, EL2, EL3, ER1, ER2, ER3] = Witness,
    Af = dot(A, Witness),
    Bf = dot(B, Witness),
    Cf = dot(C, Witness),
    true = ((Af#encrypted.value * 
                 Bf#encrypted.value)
            == Cf#encrypted.value),




    %verification
    true = check(EOne),
    true = check(EL1),
    true = check(EL2),
    
    
    

    success;


    %pi_i (A1_i - Challenge) = pi_i (A2_i - Challenge)


%(A - x) * (B - x) = (C - x) * (D - x)

%multiplicative constraints. x * y = z

%linear constraints 
%secret variables with cleartext weights
%a*x + b*y + c*z ... = 0
    %ok.

test(2) ->
    % 2 * 3 = 6
    % 4 * 5 =  20
    % 7 * 10 = 70
    % 2 * 5 = 10
    
    A = [2, 4, 7, 2],
    B = [3, 5, 10, 5],
    C = [6, 20, 70, 10],
    

    ok.

det_pow(_, 0) -> 1;
det_pow(0, _) -> 0;
det_pow(X, 1) -> X;
det_pow(1, _) -> 1;
det_pow(A, B) when (0 == (B rem 2)) -> 
    det_pow(A*A, B div 2);
det_pow(A, B) -> 
    A*det_pow(A, B-1).

range(A, A) -> [];
range(A, B) when (A < B) -> 
    [A|range(A+1, B)].

eval_poly(X, L) -> 
    eval_poly2(X, L, 0).
eval_poly2(X, [], _) -> 0;
eval_poly2(X, [H|T], N) -> 
    (H*det_pow(X, N)) +
        eval_poly2(X, T, N+1).

add_poly([], []) -> [];
add_poly([], X) -> X;
add_poly(X, []) -> X;
add_poly([A|AT], [B|BT]) ->
    [(A+B)|add_poly(AT, BT)].

mul_poly_c(_, []) -> [];
mul_poly_c(S, [A|T]) when is_integer(S) -> 
    [S*A|mul_poly_c(S, T)].

div_poly_c(_, []) -> [];
div_poly_c(S, [A|T]) -> 
    0 = A rem S,
    [A div S|div_poly_c(S, T)].

mul_poly([A], B) ->
    mul_poly_c(A, B);
mul_poly([A|AT], B) ->
    add_poly(mul_poly_c(A, B),
             mul_poly(AT, [0|B])).


all_zeros(0) -> [];
all_zeros(N) when (N > 0) -> 
    [0|all_zeros(N-1)].

base_polynomial(Length, Intercept) ->
    Rest = all_zeros(Length - 2),
    [-Intercept, 1|Rest].

remove_element(X, [X|T]) -> T;
remove_element(X, [A|T]) -> 
    [A|remove_element(X, T)].

lagrange_polynomials(Many) ->
    R = range(1, Many+1),
    lists:map(fun(X) -> 
                      R2 = remove_element(X, R),
                      lagrange_polynomial(R2, Many, X)
              end, R).
    
lagrange_polynomial(R2, Many, N) ->
    Ps = lists:map(fun(X) ->
                           base_polynomial(Many, X)
                   end, R2),
    P = lists:foldl(fun(X, A) ->
                            mul_poly(X, A)
                    end, [1],
                    Ps),
    Ds = lists:map(fun(X) ->
                           N - X
                   end, R2),
    D = lists:foldl(fun(X, A) ->
                            X * A
                    end, 1, Ds),
    if
        D > 0 -> {P, D};
        true -> {mul_poly_c(-1, P), -D}
    end.
             
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
    L2 = lagrange_polynomials(length(L)),
    GCD = lists:foldl(fun({_, X}, A) ->
                             basics:gcd_euclid(X, A)
                     end, 1, L2),
    Pi = lists:foldl(fun({_, X}, A) ->
                             X*A
                     end, 1, L2),
    LCM = Pi div GCD,
    L3 = lists:map(fun({P, D}) ->
                           M = LCM div D,
                           mul_poly_c(M, P)
                   end, L2),
    L4 = evaluation_to_coefficients2(L, L3),
    P = lists:foldl(fun(X, A) ->
                           add_poly(X, A)
                   end, [], L4),
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

test() ->    
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
    {E1, E2, E3}.
    
     
    
    

 
    
    
    
