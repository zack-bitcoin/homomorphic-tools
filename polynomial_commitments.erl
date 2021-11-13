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

-record(shuffle_proof, {s, h, a, b, c, u = 1, zp, r = 1, cross_factor}).


%basics:lrpow(B, E, N) B^E rem N

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

%ZD0 = lists:map(
%        fun(R) ->
%                base_polynomial(R, Base)
%        end, [1,2,3]),
%lists:foldl(fun(A, B) ->
%                    mul_poly(A, B, Base)
%            end, [1], ZD0);
zd(3, Base) -> 
    ZD0 = lists:map(
            fun(R) ->
                    base_polynomial(R, Base)
            end, [1,2,3]),
    lists:foldl(fun(A, B) ->
                        mul_poly(A, B, Base)
                end, [1], ZD0).
zd(4) -> [24,-50,35,-10,1];
zd(8) -> [40320,-109584,118124,-67284,
          22449,-4536,546,-36,1].
            
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

add_poly_double([], BT, _) -> BT;
add_poly_double(AT, [], _) -> AT;
add_poly_double([{A, X}|AT], [{B, Y}|BT], E) ->
    Base = secp256k1:order(E),
    [{pedersen:add(A, B, E),
      add(X, Y, Base)}|
     add_poly_double(AT, BT, E)].

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
mul_poly_double(_, [], _) -> [];
mul_poly_double({G, F}, [A|T], E) ->
    Base = secp256k1:order(E),
    [{pedersen:mul(G, A, E),
      mul(F, A, Base)}|
     mul_poly_double({G, F}, T, E)].
    

div_poly_c(_, [], _) -> [];
div_poly_c(S, [A|T], Base) -> 
    %0 = A rem S,
    [divide(A, S, Base)|
     div_poly_c(S, T, Base)].

%for coefficient form, or evaluation in the case where the polynomials are the same length.
dot_polys_c([], [], _Base) -> [];
dot_polys_c([A|AT], [P|PT], Base) ->
    %Plugging in an unblinded witness to a matrix of the circuit.
    %S = [S1, S2, S3], PA = [[P11, P12, P13] ...
    %[[S1 * P11, S1 * P12, S1 * P13], [S2 * P21 ...
    %[[S1P11 + S2P21 + S3P31, S1P12 + ...
    add_poly(mul_poly_c(A, P, Base),
             dot_polys_c(AT, PT, Base),
             Base).
%for encrypted mode. A is an elliptic point. P is a polynomial
%A is an encrypted witness value.
dot_polys_e([], _, _) -> [];
dot_polys_e([P|PT], R, E) ->
    %Pluggining in the random R value we are using to check the blinded witness. It is using the R value to simplify one of the matrices of the circuit.
    Base = secp256k1:order(E),
    [eval_poly(R, P, Base)|
     dot_polys_e(PT, R, E)].
    
        
dot_polys_e_old([], [], _) -> [];
dot_polys_e_old([A|AT], [P|PT], E) -> 
    add_poly_encrypted(
      mul_poly_encrypted(A, P, E),
      dot_polys_e_old(AT, PT, E),
      E).

dot_polys_double([], [], E) -> [];
dot_polys_double([{G1, F1}|GT], [P|PT], E) ->
    Base = secp256k1:order(E),
    add_poly_double(
      mul_poly_double({G1, F1}, P, E),
      dot_polys_double(GT, PT, E),
      E).

mul_all([], [], _) -> [];
mul_all([A|AT], [B|BT], Base) ->
    [mul(A, B, Base)|
     mul_all(AT, BT, Base)].

pedersen_encode([], [], E) ->  [];
pedersen_encode([], [H|T], E) -> 
    [infinity|pedersen_encode([], T, E)];
pedersen_encode([A|As], [G|Gs], E) ->
    [pedersen:mul(G, A, E)|
     pedersen_encode(As, Gs, E)].
pedersen_encode_double(As, Gs, R, E) ->
    %{G_i, z^r}
    Base = secp256k1:order(E),
    EllipticPoints = 
        lists:zipwith(
          fun(G, A) ->
                  pedersen:mul(G, A, E)
          end, Gs, As),
    Ints =
        lists:zipwith(
          fun(Z, A) -> mul(A, Z, Base) end, 
          powers(R, length(As), Base), 
          As),

    lists:zipwith(
      fun(A, B) -> {A, B} end,
      EllipticPoints, Ints).

add_double({G1, I1}, {G2, I2}, E) ->
    Base = secp256k1:order(E),
    {pedersen:add(G1, G2, E),
     add(I1, I2, Base)}.
sum_up_double([{G, I}], _) ->
    {G, I};
sum_up_double([A, B|T], E) ->
    sum_up_double(
      [add_double(A, B, E)|T], 
      E).

sum_up_f([A], _) -> A;
sum_up_f([A, B|T], Base) -> 
    sum_up_f([add(A, B, Base)|T], Base).
       

mul_double(C, {G, I}, E) ->
    Base = secp256k1:order(E),
    {pedersen:mul(G, C, E),
     mul(I, C, Base)}.
              
    

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
mul_poly([], _B, Base) -> [];
mul_poly(_, [], Base) -> [];
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
%this isn't for ending the recursion, it is just handling a simple case.

%div_poly([0|A], [0|B], Base) -> 
%    div_poly(A, B, Base);
%div_poly([0], _, _) -> [0];
%div_poly([0], _, _) -> [];
%div_poly(A, B, _) 
%  when (length(A) < length(B)) ->
%    fail;
div_poly(A, B, Base) -> 
    D = length(A) - length(B),
    AllZeros = is_all_zeros(A),
    if
        AllZeros -> many(0, max(0, D+1));
        true ->
            if
                D < 0 ->
                    io:fwrite("impossible division\n"),
                    io:fwrite({A, B}),
                    ok;
                true -> ok
            end,
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
            %io:fwrite({A3, B}),
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
all_zeros(N) when (N < 0) -> [];
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
    Ps = lists:map(
           fun(X) -> base_polynomial(X, Base) end, 
           R2),
    P = lists:foldl(
          fun(X, A) -> mul_poly(X, A, Base) end, 
          [1], Ps),
    Ds = lists:map(
           fun(X) -> sub(N, X, Base) end, 
           R2),
    D = lists:foldl(
          fun(X, A) -> mul(X, A, Base) end, 
          1, Ds),
    div_poly_c(D, P, Base).
coefficient_to_evaluation(L, Base) ->
    coefficient_to_evaluation(L, 0, Base).
coefficient_to_evaluation(L, M, Base) ->
    %ex L = [1, 2, 3] -> L(x) = 1 + 2*x + 3*x*x.
    M2 = max(length(L), M),
    R = range(1, M2+1),
    lists:map(fun(X) -> eval_poly(X, L, Base) end, R).
evaluation_to_coefficient(L, Base) ->
    Many = length(L),
    R = range(0, Many),
    LP = lagrange_polynomials(Many, Base),%we should memorize these.
    L4 = evaluation_to_coefficients2(L, LP, Base, Many, 1),
    P = lists:foldl(fun(X, A) ->
                           add_poly(X, A, Base)
                   end, [], L4),
    remove_trailing_zeros(P).
evaluation_to_coefficients2([], [], _, _, _) -> [];
evaluation_to_coefficients2(
  [I|IT], [P|PT], Base, Many, Counter) ->
    %P = lagrange_polynomial(range(1, Many+1), Many, Counter, Base),
    [mul_poly_c(I, P, Base)|
     evaluation_to_coefficients2(IT, PT, Base, Counter + 1, Many)].
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
  
one_polynomial(Many, 0) -> 
    [1|many(0, Many-1)];
one_polynomial(Many, Position) -> 
    [0|one_polynomial(Many-1, Position-1)].
one_one_polynomials(N, N, _) -> [];
one_one_polynomials(L, N, Base) -> 
    E2C = fun(A) -> evaluation_to_coefficient(
                      A, Base) end,
    [E2C(one_polynomial(L, N))|
     one_one_polynomials(L, N+1, Base)].

matrices_double(Base) ->
%(A - x)(B - x) = (C - x)(D - x)

%A*B - (A+B)x + x*x = C*D - (C+D)x + x*x
%-> A*B = C*D AND A+B = C+D

    % [1, 5p, 7p, b, 5d, 7d, ub, 5b, 7b, 35b, 12b, sb, tb]
    
    % 5p = b + 5d
    % 7p = b + 7d
    % 5b = ub + 5d
    % 7b = ub + 7d
    % 35b = 5b * 7b
    % 35b = sb * tb
    % 12b = 5b + 7b
    % 12b = sb + tb

    % 5p = b + 5d
    % [1, 5p, 7p, b, 5d, 7d, ub, 5b, 7b, 35b, 12b, sb, tb]
    % [0,1,0,0,0,0,0,0,0,0,0,0,0] =
    % [1,0,0,0,0,0,0,0,0,0,0,0,0] *
    % [0,0,0,1,1,0,0,0,0,0,0,0,0]

    % 7p = b + 7d
    % [1, 5p, 7p, b, 5d, 7d, ub, 5b, 7b, 35b, 12b, sb, tb]
    % [0,0,1,0,0,0,0,0,0,0,0,0,0] =
    % [1,0,0,0,0,0,0,0,0,0,0,0,0] *
    % [0,0,0,1,0,1,0,0,0,0,0,0,0]

    % 5b = ub + 5d
    % [1, 5p, 7p, b, 5d, 7d, ub, 5b, 7b, 35b, 12b, sb, tb]
    % [0,0,0,0,0,0,0,1,0,0,0,0,0] =
    % [1,0,0,0,0,0,0,0,0,0,0,0,0] *
    % [0,0,0,0,1,0,1,0,0,0,0,0,0]

    % 7b = ub + 7d
    % [1, 5p, 7p, b, 5d, 7d, ub, 5b, 7b, 35b, 12b, sb, tb]
    % [0,0,0,0,0,0,0,0,1,0,0,0,0] =
    % [1,0,0,0,0,0,0,0,0,0,0,0,0] *
    % [0,0,0,0,0,1,1,0,0,0,0,0,0]

    % 35b = 5b * 7b
    % [1, 5p, 7p, b, 5d, 7d, ub, 5b, 7b, 35b, 12b, sb, tb]
    % [0,0,0,0,0,0,0,0,0,1,0,0,0] =
    % [0,0,0,0,0,0,0,1,0,0,0,0,0] *
    % [0,0,0,0,0,0,0,0,1,0,0,0,0]

    % 35b = sb * tb
    % [1, 5p, 7p, b, 5d, 7d, ub, 5b, 7b, 35b, 12b, sb, tb]
    % [0,0,0,0,0,0,0,0,0,1,0,0,0] =
    % [0,0,0,0,0,0,0,0,0,0,0,1,0] *
    % [0,0,0,0,0,0,0,0,0,0,0,0,1]

    % 12b = 5b + 7b
    % [1, 5p, 7p, b, 5d, 7d, ub, 5b, 7b, 35b, 12b, sb, tb]
    % [0,0,0,0,0,0,0,0,0,0,1,0,0] =
    % [1,0,0,0,0,0,0,0,0,0,0,0,0] *
    % [0,0,0,0,0,0,0,1,1,0,0,0,0]

    % 12b = sb + tb
    % [1, 5p, 7p, b, 5d, 7d, ub, 5b, 7b, 35b, 12b, sb, tb]
    % [0,0,0,0,0,0,0,0,0,0,1,0,0] =
    % [1,0,0,0,0,0,0,0,0,0,0,0,0] *
    % [0,0,0,0,0,0,0,0,0,0,0,1,1]

    %C
    % [0,1,0,0,0,0,0,0,0,0,0,0,0] =
    % [0,0,1,0,0,0,0,0,0,0,0,0,0] =
    % [0,0,0,0,0,0,0,1,0,0,0,0,0] =
    % [0,0,0,0,0,0,0,0,1,0,0,0,0] =
    % [0,0,0,0,0,0,0,0,0,1,0,0,0] =
    % [0,0,0,0,0,0,0,0,0,1,0,0,0] =
    % [0,0,0,0,0,0,0,0,0,0,1,0,0] =
    % [0,0,0,0,0,0,0,0,0,0,1,0,0] =
    
    %A
    % [1,0,0,0,0,0,0,0,0,0,0,0,0] *
    % [1,0,0,0,0,0,0,0,0,0,0,0,0] *
    % [1,0,0,0,0,0,0,0,0,0,0,0,0] *
    % [1,0,0,0,0,0,0,0,0,0,0,0,0] *
    % [0,0,0,0,0,0,0,1,0,0,0,0,0] *
    % [0,0,0,0,0,0,0,0,0,0,0,1,0] *
    % [1,0,0,0,0,0,0,0,0,0,0,0,0] *
    % [1,0,0,0,0,0,0,0,0,0,0,0,0] *

    %B
    % [0,0,0,1,1,0,0,0,0,0,0,0,0]
    % [0,0,0,1,0,1,0,0,0,0,0,0,0]
    % [0,0,0,0,1,0,1,0,0,0,0,0,0]
    % [0,0,0,0,0,1,1,0,0,0,0,0,0]
    % [0,0,0,0,0,0,0,0,1,0,0,0,0]
    % [0,0,0,0,0,0,0,0,0,0,0,0,1]
    % [0,0,0,0,0,0,0,1,1,0,0,0,0]
    % [0,0,0,0,0,0,0,0,0,0,0,1,1]
    
    P0 = evaluation_to_coefficient(
           [0,0,0,0,0,0,0,0], Base),
    P1 = evaluation_to_coefficient(
           [1,0,0,0,0,0,0,0], Base),
    P2 = evaluation_to_coefficient(
           [0,1,0,0,0,0,0,0], Base),
    P3 = evaluation_to_coefficient(
           [0,0,1,0,0,0,0,0], Base),
    P4 = evaluation_to_coefficient(
           [0,0,0,1,0,0,0,0], Base),
    P5 = evaluation_to_coefficient(
           [0,0,0,0,1,0,0,0], Base),
    P6 = evaluation_to_coefficient(
           [0,0,0,0,0,1,0,0], Base),
    P7 = evaluation_to_coefficient(
           [0,0,0,0,0,0,1,0], Base),
    P8 = evaluation_to_coefficient(
           [0,0,0,0,0,0,0,1], Base),
    P12 = evaluation_to_coefficient(
           [1,1,0,0,0,0,0,0], Base),
    P13 = evaluation_to_coefficient(
           [1,0,1,0,0,0,0,0], Base),
    P24 = evaluation_to_coefficient(
           [0,1,0,1,0,0,0,0], Base),
    P34 = evaluation_to_coefficient(
           [0,0,1,1,0,0,0,0], Base),
    P56 = evaluation_to_coefficient(
            [0,0,0,0,1,1,0,0], Base),
    P57 = evaluation_to_coefficient(
            [0,0,0,0,1,0,1,0], Base),
    P68 = evaluation_to_coefficient(
            [0,0,0,0,0,1,0,1], Base),
    P78 = evaluation_to_coefficient(
            [0,0,0,0,0,0,1,1], Base),
    P123478 = evaluation_to_coefficient(
            [1,1,1,1,0,0,1,1], Base),

    A = [P123478,P0,P0,P0,P0,P0,P0,P5,P0,P0,P0,P6,P0],
    B = [P0,P0,P0,P12,P13,P24,P34,P7,P57,P0,P0,P8,P68],
    C = [P0,P1,P2,P0,P0,P0,P0,P3,P4,P56,P78,P0,P0],
    {A, B, C}.
    

matrices(4, Base) ->
    % =  [u1, u5, u7, ur, 5r1, 7r1, 35r1, 7r2, 5r2]
    %5r1 = u5 - ur
    %7r1 = u7 - ur
    %35r1 = 5r1 * 7r1
    %35r1 = 7r2 * 5r2

    %5r1 = u5 - ur -> u5 = 5r1 + ur
    % -> [0,1,0,0,0,0,0,0,0] =
    %   [0,0,0,1,1,0,0,0,0] * [1,0,0,0,0,0,0,0,0]
    
    %7r1 = u7 - ur -> u7 = 7r1 + ur
    % -> [0,0,1,0,0,0,0,0,0] =
    %   [0,0,0,1,0,1,0,0,0] * [1,0,0,0,0,0,0,0,0]

    %35r1 = 5r1 * 7r1
    % -> [0,0,0,0,0,0,1,0,0] =
    %   [0,0,0,0,1,0,0,0,0] * [0,0,0,0,0,1,0,0,0]

    %35r1 = 7r2 * 5r2
    % -> [0,0,0,0,0,0,1,0,0] =
    %   [0,0,0,0,0,0,0,1,0] * [0,0,0,0,0,0,0,0,1]

    %C
    %[0,1,0,0,0,0,0,0,0]
    %[0,0,1,0,0,0,0,0,0]
    %[0,0,0,0,0,0,1,0,0]
    %[0,0,0,0,0,0,1,0,0]

    %A
    %[0,0,0,1,1,0,0,0,0]
    %[0,0,0,1,0,1,0,0,0]
    %[0,0,0,0,1,0,0,0,0]
    %[0,0,0,0,0,0,0,1,0]

    %B
    %[1,0,0,0,0,0,0,0,0]
    %[1,0,0,0,0,0,0,0,0]
    %[0,0,0,0,0,1,0,0,0]
    %[0,0,0,0,0,0,0,0,1]

    P1000 = evaluation_to_coefficient(
              [1,0,0,0], Base),
    P0100 = evaluation_to_coefficient(
              [0,1,0,0], Base),
    P0010 = evaluation_to_coefficient(
              [0,0,1,0], Base),
    P0001 = evaluation_to_coefficient(
              [0,0,0,1], Base),
    P0011 = evaluation_to_coefficient(
              [0,0,1,1], Base),
    P1100 = evaluation_to_coefficient(
              [1,1,0,0], Base),
    P1010 = evaluation_to_coefficient(
              [1,0,1,0], Base),
    P0 = evaluation_to_coefficient(
              [0,0,0,0], Base),

    PA = [P0,    P0,    P0,    P1100, P1010, P0100, P0,    P0001, P0],
    PB = [P1100, P0,    P0,    P0,    P0,    P0010, P0,    P0,    P0001],
    PC = [P0,    P1000, P0100, P0,    P0,    P0,    P0011, P0,    P0],

    {PA, PB, PC}.


shuffle_matrices(N, Base) ->
    %shuffling N values requires order (2N+1) polynomials.
    %shuffling N values requires 4n - 1 many polynomials per matrix.

    %example for N=3, shuffling 5, 7, and 11.
    %[5, 7, 11, r4, r5, l1, l2, l3, l4, l5, one]
    %[0, 1, 2,  3,  4,  5,  6,  7,  8,  9,  10 ]

    %r4 = r1 * r2 -> 3 = 0 * 1
    %r5 = r4 * r3 -> 4 = 3 * 2
    %l4 = l1 * l2 -> 8 = 5 * 6
    %l5 = l4 * l3 -> 9 = 8 * 7
    %l5 = 1 * r5 -> 9 = 10 * 4

    %A
    %[1,0,0,0,0,0,0,0,0,0,0] 
    %[0,0,0,1,0,0,0,0,0,0,0] 
    %[0,0,0,0,0,1,0,0,0,0,0]
    %[0,0,0,0,0,0,0,0,1,0,0]
    %[0,0,0,0,0,0,0,0,0,0,1]

    %example for N=4
    % 5*7*11*13 = s1*s2*s3*s4
    %[5, 7, 11, 13, r5, r6, r7, l1, l2, l3, l4, l5, l6, l7, one]
    %[0, 1, 2,  3,  4,  5,  6,  7,  8,  9,  10, 11, 12, 13, 14 ]
    %r5 = r1 * r2 -> 4 = 0 * 1
    %r6 = r5 * r3 -> 5 = 4 * 2
    %r7 = r6 * r4 -> 6 = 5 * 3
    %l5 = l1 * l2 -> 11= 7 * 8
    %l6 = l5 * l3 -> 12= 11* 9
    %l7 = l6 * l4 -> 13= 12* 10
    %l7 = 1 *  r7 -> 13= 14* 6


    H = (2 * N) - 1,
    W = (4 * N) - 1,
    P0 = many(0, H),
    E2C = fun(A) -> evaluation_to_coefficient(
                      A, Base) end,
    Ppair = E2C(tl(tl(P0)) ++ [1,1]),
    PNs = one_one_polynomials(H, 0, Base),
    {PN1, PNR} = lists:split(N-1, PNs),
    {PN2, _} = lists:split(N-2, PNR),
    C = many(P0, N) ++ PN1 ++ 
        many(P0, N) ++ PN2 ++ [Ppair] ++ [P0],
    {PNa1, PNRa} = lists:split(N-2, tl(PNs)),
    {PNa2, PNRL} = lists:split(N-2, tl(PNRa)),
    
    A = [hd(PNs)] ++ many(P0, N-1) ++ PNa1 ++ 
        [P0] ++ [hd(PNRa)] ++ many(P0, N-1) ++
        PNa2 ++ [P0] ++ PNRL,
    {PNb1, PNRb} = lists:split(N-1, PNs),
    {PNb2, PNLb} = lists:split(N-1, PNRb),
    B = [P0] ++ PNb1 ++ many(P0, N-2) ++ PNLb ++
        [P0] ++ PNb2 ++ many(P0, N),

    Length = length(A),
    Length = length(B),
    Length = length(C),
    {A, B, C}.

shuffle_fraction(S, PA, PB, PC, Base, ZD) ->
    As1 = dot_polys_c(S, PA, Base) ++ [0],
    Bs1 = dot_polys_c(S, PB, Base) ++ [0],
    Cs1 = dot_polys_c(S, PC, Base) ++ [0],
    MulAB1 = mul_poly(As1, Bs1, Base),
    ZeroPoly1 = subtract_poly(MulAB1, Cs1, Base),
    H1 = div_poly(ZeroPoly1, ZD, Base),
    #shuffle_proof{h = H1, a = As1, b = Bs1, 
                   s = S, c = Cs1, u = 1, r = 1,
                   zp = ZeroPoly1,
                   cross_factor = []}.

%shuffle_fraction_encrypted(ES, PA, PB, PC, E, ZD) ->
%    As1 = dot_polys_e(ES, PA, E) ++ [infinity],
%    Bs1 = dot_polys_e(ES, PB, E) ++ [infinity],
%    Cs1 = dot_polys_e(ES, PC, E) ++ [infinity],
%    MulAB1 = mul_poly_encrypted(As1, Bs1, E),
%    ok.
    

add_shuffles(
  P1 = #shuffle_proof{
    s = S1, a = As1, b = Bs1, c = Cs1, u = U1,
    zp = ZeroPoly1, r = R1, cross_factor = CRA},
  P2 = #shuffle_proof{
    s = S2, a = As2, b = Bs2, c = Cs2, u = U2,
    zp = ZeroPoly2, r = R2, cross_factor = CRB},
  PA, PB, PC, ZD, R, E
 ) when is_integer(R) ->

    %Z3 = Z1 + R*Z2
    %(A dot Z3) * (B dot Z3) - (u1+ru2)*(C dot Z3) 
    % = E1 + r*r*E2 + r*(
    %    (A dot Z1)*(B dot Z2) + (A dot Z2)*(B dot Z2)
    %    - u1*(C dot Z2) - u2*(C dot Z1))


    %(A*B)-u*C=E

    Base = secp256k1:order(E),
    U3 = U1 + (R*U2),
    S3 = pedersen:fv_add(
           S1, 
           pedersen:fv_mul(R, S2, E),
           E),
    CrossFactor0 = 
        subtract_poly(
          add_poly(mul_poly(As1, Bs2, Base),
                   mul_poly(As2, Bs1, Base),
                   Base),
          add_poly(mul_poly_c(U2, Cs1, Base), 
                   mul_poly_c(U1, Cs2, Base), 
                   Base),
          Base),
    CrossFactor1 = mul_poly_c(R, CrossFactor0, Base),
    Padding2 = [0],
    As3 = dot_polys_c(S3, PA, Base) ++ Padding2,
    Bs3 = dot_polys_c(S3, PB, Base) ++ Padding2,
    Cs3 = dot_polys_c(S3, PC, Base) ++ Padding2,
    MulAB3 = mul_poly(As3, Bs3, Base),
    ZeroPoly3a = 
        add_poly(
          add_poly(CrossFactor1, ZeroPoly1, Base),
          mul_poly_c(mul(R, R, Base),
                     ZeroPoly2, Base),
          Base),
    %(A*B)-u*C=E
    ZeroPoly3 = subtract_poly(
                  MulAB3, 
                  mul_poly_c(U3, Cs3, Base), 
                  Base),

    % zp1 + r*cf + r*r*zp2 = a3*b3 - u3c3

    %io:fwrite(integer_to_list(divide(1, 2, Base))),
    [] = remove_trailing_zeros(
           subtract_poly(ZeroPoly3,
                         ZeroPoly3a, Base)),
    CFNew = add_poly(CrossFactor0,
                     add_poly(mul_poly_c(mul(R1, basics:inverse(R, Base), Base), CRA, Base),
                              mul_poly_c(mul(R, R2, Base), CRB, Base),
                              Base),
                     Base),

    H3 = div_poly(subtract_poly(ZeroPoly3, mul_poly_c(R, CFNew, Base), Base), ZD, Base),
    false = [] == remove_trailing_zeros(H3),%sanity check.

    %sanity check.
    ZeroPoly3 = 
        add_poly(
          add_poly(
            mul_poly(H3, ZD, Base),
            CrossFactor1, Base),
          add_poly(mul_poly_c(R1, CRA, Base), 
                   mul_poly_c(mul(mul(R, R, Base), R2, Base), CRB, Base), 
                   Base),
         Base),

    #shuffle_proof{s = S3, a = As3, b = Bs3, 
                   c = Cs3, h = H3, u = U3, 
                   r = R, zp = ZeroPoly3, 
                   cross_factor = CFNew}.
prove_shuffle(
  #shuffle_proof{
     s = US, a = A, b = B, c = C, h = H, u = U,
     r = R, zp = ZP, cross_factor = CF}, 
  E, Gs, Hs, Q) ->
    Base = secp256k1:order(E),
    CommitS = pedersen:commit(US, Gs, E),
    CommitH = pedersen:commit(H, Gs, E),
    <<Ran:256>> = pedersen:hash(
          <<(pedersen:c_to_entropy(CommitS)):256,
            (pedersen:c_to_entropy(CommitH)):256>>),
    ZD = zd(4),
    %sanity check
    true = (add(mul(eval_poly(Ran, H, Base),
                eval_poly(Ran, ZD, Base),
                Base),
               mul(R, eval_poly(Ran, CF, Base), Base),
               Base) ==
                eval_poly(Ran, ZP, Base)),
    true = (eval_poly(Ran, ZP, Base) ==
                sub(mul(eval_poly(Ran, A, Base),
                        eval_poly(Ran, B, Base), 
                        Base),
                    mul(
                      U, eval_poly(Ran, C, Base),
                      Base),
                    Base)),

    S = pedersen_encode(US, Gs, E),
    {PA, PB, PC} = matrices(4, Base),
    RAs = dot_polys_e(PA, Ran, E),
    RBs = dot_polys_e(PB, Ran, E),
    RCs = dot_polys_e(PC, Ran, E),
    As2 = mul_all(US, RAs, Base),
    Bs2 = mul_all(US, RBs, Base),
    Cs2 = mul_all(US, RCs, Base),
    Padding = [0,0,0,0,0,0,0],
    V = [1,1,1,1,1,1,1,1,1] ++ Padding,
    ProofA = 
        pedersen:make_ipa(As2++Padding, V, Gs, Hs, Q, E),
    ProofB = 
        pedersen:make_ipa(Bs2 ++ Padding, V, Gs, Hs, Q, E),
    ProofC = 
        pedersen:make_ipa(Cs2 ++ Padding, V, Gs, Hs, Q, E),
    
    %you send 6 values from S, commitS, ProofA, ProofB, ProofC,
    {S, ProofA, ProofB, ProofC, H, 
     eval_poly(Ran, CF, Base),
    U, R}.

verify_shuffle_instance({S, ProofA, ProofB, ProofC, H, RanCF, U, R}, E, Gs, Hs, Q) ->
    Base = secp256k1:order(E),
    {PA, PB, PC} = matrices(4, Base),
    ZD = zd(4),
    CommitS = pedersen:sum_up(S, E),
    CommitH = pedersen:commit(H, Gs, E),
    <<Ran:256>> = pedersen:hash(
          <<(pedersen:c_to_entropy(CommitS)):256,
            (pedersen:c_to_entropy(CommitH)):256>>),
    Padding = [0,0,0,0,0,0,0],
    V = [1,1,1,1,1,1,1,1,1] ++ Padding,
    true = pedersen:verify_ipa(ProofA, V, Gs, Hs, Q, E),
    true = pedersen:verify_ipa(ProofB, V, Gs, Hs, Q, E),
    true = pedersen:verify_ipa(ProofC, V, Gs, Hs, Q, E),
    RAs = dot_polys_e(PA, Ran, E),
    RBs = dot_polys_e(PB, Ran, E),
    RCs = dot_polys_e(PC, Ran, E),
    EAs = pedersen_encode(RAs, S, E),
    EBs = pedersen_encode(RBs, S, E),
    ECs = pedersen_encode(RCs, S, E),
    CommitA = pedersen:sum_up(EAs, E),
    CommitB = pedersen:sum_up(EBs, E),
    CommitC = pedersen:sum_up(ECs, E),
    CommitA = element(1, ProofA),
    CommitB = element(1, ProofB),
    CommitC = element(1, ProofC),
    (sub(mul(element(2, ProofA), 
             element(2, ProofB), 
             Base),
         mul(U, element(2, ProofC), Base),
         Base) 
     == add(mul(
              eval_poly(Ran, H, Base),
              eval_poly(Ran, ZD, Base),
              Base),
            mul(R, RanCF, Base),
            Base)).
    
    
verify_shuffle(S, B) ->
    verify_shuffle(S, B, zd(3, B)).
verify_shuffle_new(S, B) ->
    verify_shuffle(S, B, zd(4)).

verify_shuffle(
  #shuffle_proof{
     s = S, a = A, b = B, c = C, h = H, u = U,
     r = R, zp = ZP, cross_factor = CF}, 
  Base, ZD) ->
    Ran = random:uniform(Base),
    H2 = div_poly(
           subtract_poly(ZP, mul_poly_c(R, CF, Base), Base), 
           ZD, Base),
    H = H2,
    %H2 = (zp - r*CF)/zd
    % -> zp = (h2*zd) + r*CF
    
    true = add(mul(eval_poly(Ran, H, Base),
                   eval_poly(Ran, ZD, Base),
                   Base),
               mul(R, eval_poly(Ran, CF, Base), Base),
               Base) == 
        sub(mul(eval_poly(Ran, A, Base),
                eval_poly(Ran, B, Base),
                Base),
            mul(U, 
                eval_poly(Ran, C, Base), 
                Base),
            Base),

    true. 
        

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
    
test(8) -> 
    %merging R1CS proofs
    %https://vitalik.ca/general/2021/11/05/halo.html
    
    %for program with values S.
    %correct execution implies: 
    %(A dot S) * (B dot S) = (C dot S)

    %new format
    %(A dot S) * (B dot S) = E + u*(C dot S)
    %if E = 0 and u = 1, this is a proof that conforms to the old format as well.

    %given 2 proofs using the same matrices
    %(A dot S1) * (B dot S1) - u1*(C dot S1) = E1
    %(A dot S2) * (B dot S2) - u2*(C dot S2) = E2

    %take random linear combination S3 = S1 + r*S2

    %(A dot S3) * (B dot S3) - (u1 + r*u2)*(C dot S3)
    %= E1 + r*r*E2 + 
    %  r((A dot S1)*(B dot S2) + 
    %    (A dot S2)*(B dot S1) -
    %    u1*(C dot Z2) -
    %    u2*(C dot Z1)
    E = secp256k1:make(),
    Base = secp256k1:order(E),
    R = random:uniform(Base),
    %R = 1,
    % 5*7*11 = s1*s2*s3
    S5 = sub(5, R, Base),
    S7 = sub(7, R, Base),
    S11 = sub(11, R, Base),
    S35 = mul(S5, S7, Base),
    S35_11 = mul(S35, S11, Base),
    S55 = mul(S11, S5, Base),
    S77 = mul(S11, S7, Base),
    Padding = [0,0,0,0,0],
    PolyPadding = [[],[],[],[],[]],
    S = [S5, S7, S11, S35, S35_11,
         S11, S5, S7, S55, S35_11, 1] 
        ++ Padding,
    S2 = [S5, S7, S11, S35, S35_11,
         S11, S7, S5, S77, S35_11, 1] 
        ++ Padding,
    16 = length(S),
    Padding2 = tl(tl(Padding)),
    {PA0, PB0, PC0} = shuffle_matrices(3, Base),
    PA = PA0 ++ PolyPadding,
    PB = PB0 ++ PolyPadding,
    PC = PC0 ++ PolyPadding,
    ZD0 = lists:map(
            fun(R) ->
                    base_polynomial(R, Base)
            end, [1,2,3,4,5]),
    ZD = lists:foldl(fun(A, B) ->
                             mul_poly(A, B, Base)
                     end, [1], ZD0),
    As1 = dot_polys_c(S, PA, Base) ++ Padding2,
    Bs1 = dot_polys_c(S, PB, Base) ++ Padding2,
    Cs1 = dot_polys_c(S, PC, Base) ++ Padding2,
    MulAB1 = mul_poly(As1, Bs1, Base),
    ZeroPoly1 = subtract_poly(MulAB1, Cs1, Base),
    H1 = div_poly(ZeroPoly1, ZD, Base),
    ZeroPoly1 = mul_poly(H1, ZD, Base),

    As2 = dot_polys_c(S2, PA, Base) ++ Padding2,
    Bs2 = dot_polys_c(S2, PB, Base) ++ Padding2,
    Cs2 = dot_polys_c(S2, PC, Base) ++ Padding2,
    MulAB2 = mul_poly(As2, Bs2, Base),
    ZeroPoly2 = subtract_poly(MulAB2, Cs2, Base),
    H2 = div_poly(ZeroPoly2, ZD, Base),
    ZeroPoly2 = mul_poly(H2, ZD, Base),

    R2 = random:uniform(Base),
    %R2 = 1,
    S3 = pedersen:fv_add(
           S, 
           pedersen:fv_mul(R2, S2, E),
           E),

    CrossFactor0 = 
        subtract_poly(
          add_poly(mul_poly(As1, Bs2, Base),
                   mul_poly(As2, Bs1, Base),
                   Base),
          add_poly(Cs1, Cs2, Base),
          %subtract_poly(Cs1, Cs2, Base),
          Base),
    CrossFactor = mul_poly_c(R2, CrossFactor0, Base),
    As3 = dot_polys_c(S3, PA, Base) ++ Padding2,
    Bs3 = dot_polys_c(S3, PB, Base) ++ Padding2,
    Cs3 = dot_polys_c(S3, PC, Base) ++ Padding2,
    MulAB3 = mul_poly(As3, Bs3, Base),

    CrossFactor2 = 
        add_poly(
          add_poly(CrossFactor, ZeroPoly1, Base),
          mul_poly_c(mul(R2, R2, Base),
                     ZeroPoly2, Base),
          Base),

    ZeroPoly3 = subtract_poly(
                  MulAB3, 
                  mul_poly_c(R2+1, Cs3, Base), 
                  Base),
    [] = remove_trailing_zeros(
           subtract_poly(ZeroPoly3,
                         CrossFactor2, Base)),
    io:fwrite("before\n"),
    H3 = div_poly(
           subtract_poly(ZeroPoly3, CrossFactor, Base),
           ZD, Base),
    io:fwrite("after\n"),
    ZeroPoly3 = add_poly(CrossFactor, 
                         mul_poly(H3, ZD, Base),
                         Base),

    %todo. find out exactly what we need to send to verify this proof.

    success;
test(9) -> 
    %It seems like we only want to shuffle 2 things at a time, and then merge all the resultant tiny proofs. So this test is to go through that process.
    E = secp256k1:make(),
    Base = secp256k1:order(E),
    R = random:uniform(Base),
    %R = 1,
    S5 = sub(5, R, Base),
    S7 = sub(7, R, Base),
    S35 = mul(S5, S7, Base),

    S = [S5, S7, S35, S7, S5, S35, 1, 0],
    
    S11 = sub(11, R, Base),
    S13 = sub(13, R, Base),
    S143 = mul(S11, S13, Base),
    S2 = [S11, S13, S143, S11, S13, S143, 1, 0],

    S55 = mul(S11, S5, Base),
    S3 = [S11, S5, S55, S5, S11, S55, 1, 0],

    S77 = mul(S11, S7, Base),
    S4 = [S7, S11, S77, S7, S11, S77, 1, 0],

    {PA0, PB0, PC0} = shuffle_matrices(2, Base),
    PA = PA0 ++ [[]],
    PB = PB0 ++ [[]],
    PC = PC0 ++ [[]],
    ZD0 = lists:map(
            fun(R) ->
                    base_polynomial(R, Base)
            end, [1,2,3]),
    ZD = lists:foldl(fun(A, B) ->
                             mul_poly(A, B, Base)
                     end, [1], ZD0),

    H1 = shuffle_fraction(S, PA, PB, PC, Base, ZD),
    %true = verify_shuffle(H1, Base),
    H2 = shuffle_fraction(S2, PA, PB, PC, Base, ZD),
    %true = verify_shuffle(H2, Base),
    H3 = shuffle_fraction(S3, PA, PB, PC, Base, ZD),
    %true = verify_shuffle(H3, Base),
    H4 = shuffle_fraction(S4, PA, PB, PC, Base, ZD),
    %true = verify_shuffle(H4, Base),
    
    H5 = add_shuffles(H1, H2, PA, PB, PC, ZD, random:uniform(Base), E),
    true = verify_shuffle(H5, Base),
    H6 = add_shuffles(H3, H4, PA, PB, PC, ZD, random:uniform(Base), E),
    true = verify_shuffle(H6, Base),
    H7 = add_shuffles(H5, H6, PA, PB, PC, ZD, random:uniform(Base), E),
    true = verify_shuffle(H7, Base),

    H8 = add_shuffles(H1, H2, PA, PB, PC, ZD, random:uniform(Base), E),
    true = verify_shuffle(H8, Base),
    H9 = add_shuffles(H8, H3, PA, PB, PC, ZD, random:uniform(Base), E),
    true = verify_shuffle(H9, Base),
    H10 = add_shuffles(H9, H4, PA, PB, PC, ZD, random:uniform(Base), E),
    true = verify_shuffle(H10, Base),

    %Next lets go through the process of proving H1, which is evidence for S. After that we can try doing a multi-proof.


    {Gs, Hs, Q} = pedersen:basis(length(S), E),
    CommitS = pedersen:commit(S, Gs, E),
    CommitH = pedersen:commit(
                H1#shuffle_proof.h, Hs, E),
    <<Ran:256>> = pedersen:hash(
          <<(pedersen:c_to_entropy(CommitS)):256>>),
    
    success;
test(10) -> 

    %todo. maybe this should be a 3-shuffle, because 3-shuffles also fit into a 16-element vector, so it wouldn't make the ipa proofs any slower.

    %accessing a variable without telling which one.
    %R1CS r 1 constraint systems explained here https://medium.com/@VitalikButerin/quadratic-arithmetic-programs-from-zero-to-hero-f6d558cea649
    % for a computation, rewrite using only +, -, *, /
    % calculate all the intermediate values.
    % find vector s and matrices a, b, and c such that (s dot a) * (s dot b) = (s dot c),
    % vector s is the values being passed through the computation. It is a witness that the computation happened.
    % some of the s values can be un-blinded to reveal aspects of the computation.
    % s is elliptic curves. a, b, and c are matricies of integers that we multiply the curve points by.

    E = secp256k1:make(),
    Base = secp256k1:order(E),
    R = random:uniform(Base),

    %unblinded witness
    Secret5 = sub(5, R, Base),
    Secret7 = sub(7, R, Base),
    Secret35 = mul(Secret5, Secret7, Base),
    US = [1, 5, 7, R, Secret5, Secret7, Secret35, Secret7, Secret5],
    % =  [u1, u5, u7, ur, 5r1, 7r1, 35r1, 7r2, 5r2]

    %5r1 = u5 - ur
    %7r1 = u7 - ur
    %35r1 = 5r1 * 7r1
    %35r1 = 7r2 * 5r2

    {PA, PB, PC} = matrices(4, Base),

    As = dot_polys_c(US, PA, Base),
    Bs = dot_polys_c(US, PB, Base),
    Cs = dot_polys_c(US, PC, Base),
    MulAB = mul_poly(As, Bs, Base),

    ZeroPoly = subtract_poly(MulAB, Cs, Base),
    ZD = zd(4),
    H = div_poly(ZeroPoly, ZD, Base),
    3 = length(H),

    {Gs, Hs, Q} = pedersen:basis(16, E),
    CommitS = pedersen:commit(US, Gs, E),
    CommitH = pedersen:commit(H, Gs, E),

    <<Ran:256>> = pedersen:hash(
          <<(pedersen:c_to_entropy(CommitS)):256,
            (pedersen:c_to_entropy(CommitH)):256>>),
    %sanity check
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

    S = pedersen_encode(US, Gs, E),
    RAs = dot_polys_e(PA, Ran, E),
    RBs = dot_polys_e(PB, Ran, E),
    RCs = dot_polys_e(PC, Ran, E),
    As2 = mul_all(US, RAs, Base),
    Bs2 = mul_all(US, RBs, Base),
    Cs2 = mul_all(US, RCs, Base),
    Padding = [0,0,0,0,0,0,0],
    V = [1,1,1,1,1,1,1,1,1] ++ Padding,

    ProofA = 
        pedersen:make_ipa(As2++Padding, V, Gs, Hs, Q, E),
    ProofB = 
        pedersen:make_ipa(Bs2 ++ Padding, V, Gs, Hs, Q, E),
    ProofC = 
        pedersen:make_ipa(Cs2 ++ Padding, V, Gs, Hs, Q, E),

    %they already know ZD, PA, PB, PC
    %you send 6 values from S, commitS, ProofA, ProofB, ProofC,
    %It is better to send H instead of a commit or proof.
    %6 values from S.
    %1 value from commits
    %proof has 1 commit, 1 int, 9 points, 2 ints, 1 point
    %H is 3 ints.
    %around 500 bytes per proof.
    %io:fwrite({S, CommitS, ProofA, ProofB, ProofC, H}),
    %io:fwrite(size(term_to_binary({S, CommitS, ProofA, ProofB, ProofC, H}))),
    %around 1537 bytes.
    
    io:fwrite("verifying.\n"),
    {PA, PB, PC} = matrices(4, Base),
    ZD = zd(4),
    <<Ran:256>> = pedersen:hash(
          <<(pedersen:c_to_entropy(CommitS)):256,
            (pedersen:c_to_entropy(CommitH)):256>>),
    true = pedersen:verify_ipa(ProofA, V, Gs, Hs, Q, E),
    true = pedersen:verify_ipa(ProofB, V, Gs, Hs, Q, E),
    true = pedersen:verify_ipa(ProofC, V, Gs, Hs, Q, E),

    CommitS = pedersen:sum_up(S, E),
    RAs = dot_polys_e(PA, Ran, E),
    RBs = dot_polys_e(PB, Ran, E),
    RCs = dot_polys_e(PC, Ran, E),
    EAs = pedersen_encode(RAs, S, E),
    EBs = pedersen_encode(RBs, S, E),
    ECs = pedersen_encode(RCs, S, E),
    CommitA = pedersen:sum_up(EAs, E),
    CommitB = pedersen:sum_up(EBs, E),
    CommitC = pedersen:sum_up(ECs, E),
    CommitA = element(1, ProofA),
    CommitB = element(1, ProofB),
    CommitC = element(1, ProofC),
    
    true = (sub(mul(element(2, ProofA), 
                    element(2, ProofB), 
                    Base),
                element(2, ProofC),
                Base) 
            == mul(
                 eval_poly(Ran, H, Base),
                 eval_poly(Ran, ZD, Base),
                 Base)),
    success;
test(11) -> 
    %multi-proof of r1cs
    %Using four 2-shuffle circuits to privately select a value from a list of 4 elements: [5, 7, 11, 3]
    E = secp256k1:make(),
    Base = secp256k1:order(E),
    R = random:uniform(Base),
    R2 = random:uniform(Base),
    R3 = random:uniform(Base),
    ZD = zd(4),
    Secret5 = sub(5, R, Base),
    Secret7 = sub(7, R, Base),
    Secret35 = mul(Secret5, Secret7, Base),
    US = [1, 5, 7, R, Secret5, Secret7, Secret35, Secret5, Secret7],
    Secret11 = sub(11, R2, Base),
    Secret3 = sub(3, R2, Base),
    Secret33 = mul(Secret11, Secret3, Base),
    US2 = [1, 11, 3, R2, Secret11, Secret3, Secret33, Secret11, Secret3],

    Secret15 = mul(Secret5, Secret3, Base),
    US3 = [1, add(Secret5, R3, Base), 
           add(Secret3, R3, Base), 
           R3, Secret5, Secret3, Secret15, Secret5, Secret3],

    %Secret5b = sub(Secret5, R3, Base),
    %Secret3b = sub(Secret3, R3, Base),
    %Secret15b = mul(Secret5b, Secret3b, Base),
    %US3 = [1, Secret5, Secret3, R3, Secret5b, Secret3b, Secret15b, Secret5b, Secret3b],
    
    Rr = sub(0, add(R2, R3, Base), Base),
    Secret1 = add(1, Rr, Base),
    %US4 = [1, Secret3b, Secret1, Rr, 3, 1, 3, 1, 3],
    US4 = [1, 3, 1, 0, 3, 1, 3, 1, 3],
    {PA, PB, PC} = matrices(4, Base),

    SF1 = shuffle_fraction(US, PA, PB, PC, Base, ZD),
    SF2 = shuffle_fraction(US2, PA, PB, PC, Base, ZD),
    SF3 = shuffle_fraction(US3, PA, PB, PC, Base, ZD),
    true = verify_shuffle_new(SF3, Base),
    SF4 = shuffle_fraction(US4, PA, PB, PC, Base, ZD),
    true = verify_shuffle_new(SF4, Base),

    ASF1 = add_shuffles(SF1, SF2, PA, PB, PC, ZD, random:uniform(Base), E),
    ASF2 = add_shuffles(SF3, SF4, PA, PB, PC, ZD, random:uniform(Base), E),
    ASF3 = add_shuffles(ASF1, ASF2, PA, PB, PC, ZD, random:uniform(Base), E),

    true = verify_shuffle_new(ASF3, Base),
    {Gs, Hs, Q} = pedersen:basis(16, E),
    verify_shuffle_instance(
      prove_shuffle(ASF3, E, Gs, Hs, Q), 
      E, Gs, Hs, Q);
test(12) -> 
    %try attacking the mechanism
    %make it look like `27` was stored in the list.
    E = secp256k1:make(),
    Base = secp256k1:order(E),
    R = random:uniform(Base),
    ZD = zd(4),
    SharedR = random:uniform(Base),
    V = [7, 10],
    EV = [sub(7, SharedR, Base),
          sub(10, SharedR, Base)],
    [EV1, EV2] = EV,
    Secret7 = sub(EV1, R, Base),
    Secret10 = sub(EV2, R, Base),
    Attack = Secret10,
    Secret14 = %sub(14, R, Base),
        sub(sub(divide(mul(27, Secret10, Base), Attack, Base), R, Base), SharedR, Base),
    Secret70 = mul(Secret10, Secret7, Base),
    Secret5 = %sub(5, R, Base),
        divide(Secret70, Secret14, Base),
    Secret70 = mul(Secret5, Secret14, Base),
    US = [1, EV2, EV1, R, Secret10, Secret7, Secret70, Secret5, Secret14],
    {PA, PB, PC} = matrices(4, Base),
    SF1 = shuffle_fraction(US, PA, PB, PC, Base, ZD),
    true = verify_shuffle_new(SF1, Base),
    10 = add(add(Secret10, R, Base),
             SharedR, Base),
    27 = add(add(Secret14, R, Base),
             SharedR, Base),
    success;
test(13) -> 
    %fix attack from test 12
    E = secp256k1:make(),
    Base = secp256k1:order(E),
    ZD = zd(8),
    V = [7, 11],

    % [1, 5p, 7p, b, 5d, 7d, ub, 5b, 7b, 35b, 12b, sb, tb]
    R1 = random:uniform(Base),
    B5 = sub(5, R1, Base),
    B7 = sub(7, R1, Base),
    B35 = mul(B5, B7, Base),
    B12 = add(B5, B7, Base),
    SB = B7,
    TB = B5,
    US = [1,5,7,R1,B5,B7,0,B5,B7,B35,B12,SB,TB],

    R2 = random:uniform(Base),
    B11 = sub(11, R2, Base),
    B13 = sub(13, R2, Base),
    B143 = mul(B11, B13, Base),
    B24 = add(B11, B13, Base),
    SB2 = B11,
    TB2 = B13,
    US2 = [1,11,13,R2,B11,B13,0,B11,B13,B143,B24,SB2,TB2],

    R3 = random:uniform(Base),
    B5_2 = sub(5, R3, Base),
    DE13 = sub(TB2, R3, Base),
    R1DE13 = add(R1, DE13, Base),
    Mul = mul(R1DE13, B5_2, Base),
    Add = add(R1DE13, B5_2, Base),
    US3 = [1,TB,TB2,R3,
           sub(TB, R3, Base),
           DE13,
           R1,B5_2,R1DE13,
           Mul,Add,R1DE13,B5_2],


    {PA, PB, PC} = matrices_double(Base),

    SF1 = shuffle_fraction(US, PA, PB, PC, Base, ZD),
    true = verify_shuffle(SF1, Base, zd(8)),
    7 = add(SB, R1, Base),
    5 = add(TB, R1, Base),
    SF2 = shuffle_fraction(US2, PA, PB, PC, Base, ZD),
    true = verify_shuffle(SF2, Base, zd(8)),
    11 = add(SB2, R2, Base),
    13 = add(TB2, R2, Base),
    SF3 = shuffle_fraction(US3, PA, PB, PC, Base, ZD),
    true = verify_shuffle(SF3, Base, zd(8)),
    5 = add(B5_2, R3, Base),
    success.
    


    


