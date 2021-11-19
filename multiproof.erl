-module(multiproof).
-export([test/1]).

%multiproofs for pedersen IPA.
%We are trying merge IPA.

%going through this paper: https://dankradfeist.de/ethereum/2021/06/18/pcs-multiproofs.html

%vitalik wrote a little on this topic as well: https://vitalik.ca/general/2021/06/18/verkle.html

primitive_nth_root(N, E) ->
    Base = secp256k1:order(E),
    0 = N rem 2,
    X = random:uniform(Base),
    %true = (0 == ((Base - 1) rem N)),
    NI = basics:inverse(N, Base),
    G = basics:lrpow(
          X, pedersen:fmul(Base - 1, NI, E), Base),
    GP = basics:lrpow(G, N div 2, Base),
    if
        (GP == 1) ->
            %fail;
            primitive_nth_root(N, E);
        true -> G
    end.

add_polys([P], _) -> P;
add_polys([A, B|T], Base) -> 
    PC = polynomial_commitments,
    add_polys([PC:add_poly(A, B, Base)|
               T], Base).

calc_G(R, Fs, Ys, Zs, Base) ->
    %polynomials in coefficient format.
    PC = polynomial_commitments,
    GP = lists:zipwith3(
           fun(F, Y, Z) ->
                   PC:div_poly(
                     PC:subtract_poly(
                       F, 
                       [Y], %eval(Z, F)
                       Base),
                     PC:base_polynomial(Z, Base),
                     Base)
           end, Fs, Ys, Zs),
    calc_G_helper(1, R, GP, Base).
calc_G_helper(_, _, [], _) -> [];
calc_G_helper(RA, R, [P|T], Base) -> 
    PC = polynomial_commitments,
    PC:add_poly(
      PC:mul_poly_c(RA, P, Base),
      calc_G_helper(pedersen:fmul(RA, R, Base), R, T, Base),
      Base).

mod(X,Y)->(X rem Y + Y) rem Y.
sub(A, B, Base) ->
    mod(A - B, Base).
add(A, B, Base) ->
    mod(A + B, Base).
mul(A, B, Base) ->
    mod(A * B, Base).
divide(A, B, N) ->
    B2 = basics:inverse(B, N),
    mul(A, B2, N).
    

%map_i:  Commit_i * r^i / (t - z_i)
calc_E(_, _, _, _, [], _) -> [];
calc_E(R, RA, T, Zs, Commits, E) ->
    Base = secp256k1:order(E),
    [pedersen:mul(
       hd(Commits), 
       divide(RA, sub(T, hd(Zs), Base), Base),
       E)|
     calc_E(R, mul(RA, R, Base), T,
            tl(Zs), tl(Commits), E)].


%sum_i:  r^i * y_i / (t - z_i)
calc_G2(_, _, _, [], [], _) -> 0;
calc_G2(R, RA, T, Ys, Zs, Base) ->
    Top = mul(RA, hd(Ys), Base),
    Bottom = sub(T, hd(Zs), Base),
    add(divide(Top, Bottom, Base),
        calc_G2(R, mul(RA, R, Base), 
                T, tl(Ys), tl(Zs), Base),
        Base).

%sum_i: (r^i)/(t - z_i)
calc_H(_, _, _, [], [], _) -> [];
calc_H(R, RA, T, Fs, Zs, E) ->
    Base = secp256k1:order(E),
    PC = polynomial_commitments,
    PC:add_poly(
      PC:mul_poly_c(
        divide(RA, sub(T, hd(Zs), Base), Base),
        hd(Fs), Base),
      calc_H(R, mul(RA, R, Base), T, tl(Fs),
             tl(Zs), E),
      Base).
              
    


test(1) ->

    E = secp256k1:make(),
    Base = secp256k1:order(E),
    A1 = [3,4],
    A2 = [5,6],
    S = length(A1),
    {G, H, Q} = pedersen:basis(S, E),

    %first a review of doing lots of individual ipa proofs.

    B1 = [1, 0],%A1 dot B1 is 3
    B2 = [0, 1],%A2 dot B2 is 6

    Proof1 = pedersen:make_ipa(A1, B1, G, H, Q, E),
    {_, 10, _, _, _, _} = Proof1,
    true = pedersen:verify_ipa(Proof1, B1, G, H, Q, E),
    Proof2 = pedersen:make_ipa(A2, B2, G, H, Q, E),
    {_, 6, _, _, _, _} = Proof2,
    true = pedersen:verify_ipa(Proof2, B2, G, H, Q, E),

    %Now lets try combining them.
    %we have 2 commitments
    C1 = pedersen:commit(A1, G),
    C2 = pedersen:commit(A2, G),
    
    %f_0(z_0) -> y_0 
    %A1 dot B1 is 10
    %A2 dot B2 is 6

    %Root64 = primitive_nth_root(64, E),
    Root2 = primitive_nth_root(2, E),

    W1 = [Root2, 0],
    W2 = [0, Root2],

    %(A1 dot W1) + (A2 dot W2) = root2*((A1 dot B1) + (A2 dot B2)) = root2 * 9.

    %to prove:
    % A1 dot B1 = 3, A2 dot B2 = 6.
    % -> A1 dot W1 = 3*root2, A2 dot W2 = 6*root2

    %given commitments C1, C2. prove: A1 dot W1 = 3*root2, A2 dot W2 = 6*root2

    R = random:uniform(Base),

    %find polynomial g(x) = 
    % ((r^0)*(f_0(x)-y_0)/(x - z_0)) + 
    % ((r^1)*(f_1(x)-y_1)/(x - z_1))
    %->
    % (1 * ((A1 dot x) - 3*root2)/(x - 1)) + 
    % (R * ((A2 dot x) - 6*root2)/(x - root2))
    %->
    % (1 * (([3,4] dot x) - 3*root2)/(x - 1)) + 
    % (R * (([5,6] dot x) - 6*root2)/(x - root2))



    success;
test(2) ->
    %dth root of unity
    E = secp256k1:make(),
    Base = secp256k1:order(E),
    Prime = secp256k1:field_prime(E),

    R1 = random:uniform(Base),
    
    R2 = basics:lrpow(R1, Base-2, Base),
    R3 = basics:lrpow(R1, (Base-1) div 2, Base),

    
    
    {pedersen:fmul(R2, R2, E),
     pedersen:fmul(R3, R3, E),
     R3,
     (Base-1) rem 2,
     (Base-1) rem 3,
     Base-1
    },
    %prime factors of base-1:
    % 2^6, 3, 149, 631
    %basics:prime_factors(Base-1).
    Root64 = primitive_nth_root(64, E),
    Root = primitive_nth_root(2, E),
    {pedersen:fmul(Root, Root, E),
     basics:lrpow(Root64, 64, Base),
     Root, 
     Root64};
test(3) ->
    %trying to build the verkle again.

    %t(t(3, 5), t(7, 11))

    PC = polynomial_commitments,

    E = secp256k1:make(),
    Base = secp256k1:order(E),
    F1 = PC:evaluation_to_coefficient(
           [3, 5], Base),
    F2 = PC:evaluation_to_coefficient(
           [7, 11], Base),
    F3 = PC:evaluation_to_coefficient(
           [13, 17], Base),
    
    3 = PC:eval_poly(1, F1, Base),
    5 = PC:eval_poly(2, F1, Base),
    %{F1, F2}.
    R = random:uniform(Base),
    Z0 = 1,
    Z1 = 2,
    Z2 = 3,
    G = add_polys(
          [PC:div_poly(PC:subtract_poly(F1, [3], Base),
                   PC:base_polynomial(Z0, Base),
                   Base),
          PC:mul_poly_c(
            R, 
            PC:div_poly(PC:subtract_poly(F2, [11], Base),
                     PC:base_polynomial(Z1, Base),
                     Base),
            Base),
           PC:mul_poly_c(
             pedersen:fmul(R, R, E), 
             PC:div_poly(PC:subtract_poly(F3, [PC:eval_poly(Z2, F3, Base)], Base),
                         PC:base_polynomial(Z2, Base),
                         Base),
             Base)
          ],
          Base),
    Ys = lists:zipwith(
           fun(F, Z) ->
                   PC:eval_poly(Z, F, Base)
           end, [F1, F2, F3], [Z0, Z1, Z2]),
    G = calc_G(R, [F1, F2, F3], Ys, 
               [Z0, Z1, Z2], Base),
    {PC:eval_poly(Z2, F3, Base),
      G
    };
test(4) ->
    PC = polynomial_commitments,
    E = secp256k1:make(),
    Base = secp256k1:order(E),
    A1 = [1,1,2],
    A2 = [2,4,6],
    A3 = [2,3,5],
    A4 = [3,5,8],
    {Gs, Hs, Q} = pedersen:basis(4, E),
    F1 = PC:evaluation_to_coefficient(
           A1, Base),
    F2 = PC:evaluation_to_coefficient(
           A2, Base),
    F3 = PC:evaluation_to_coefficient(
           A3, Base),
    F4 = PC:evaluation_to_coefficient(
           A4, Base),
    Fs = [F1, F2, F3, F4],
    Zs = [1,2,3,4],%the spot we are looking up inside a commitment.
    Commits = [pedersen:commit(F1, Gs, E),
               pedersen:commit(F2, Gs, E),
               pedersen:commit(F3, Gs, E),
               pedersen:commit(F4, Gs, E)],
    Ys = lists:zipwith(%the value we look up in each commitment.
           fun(F, Z) ->
                   PC:eval_poly(Z, F, Base)
           end, Fs, Zs),
    R = random:uniform(Base),%hash(commits, Zs, Ys)
    G = calc_G(R, Fs, Ys, Zs, Base),

    CommitG = pedersen:commit(G, Gs, E),%in the notes it is D.

    T = random:uniform(Base),%hash(CommitG, R)

    GT = PC:eval_poly(T, G, Base),

    %E_list = calc_E(R, 1, T, Zs, Commits, E),
    %CommitE = pedersen:sum_up(E_list, E),

    %need to calculate an opening to commit E at T.

    H = calc_H(R, 1, T, Fs, Zs, E),%is summing up polynomials, H has a length based on how many variables there are, not how long Fs or Zs is.
    CommitE = pedersen:commit(H, Gs, E),
    %sumi  r^i * f_i(X)/(T - Z_i)
    %io:fwrite({Gs}),
    Powers4 = PC:powers(T, 4, Base),
    OpenE = pedersen:make_ipa(
              H++[0], PC:powers(T, 4, Base),
              Gs, Hs, Q, E),
    OpenG = pedersen:make_ipa(
              G++[0,0], PC:powers(T, 4, Base),
              Gs, Hs, Q, E),

    %send an opening to E at T.
    %send an opening to G at T.
    %send the Commits
    %they know the Gs, Hs, Q, and E as system defaults.
    %they know the Zs and Ys from processing the block and making a list of things that need to be proved.
    %They can calculate R and T.


    true = pedersen:verify_ipa(
             OpenE, Powers4, Gs, Hs, Q, E),
    true = pedersen:verify_ipa(
             OpenG, Powers4, Gs, Hs, Q, E),
    G2 = calc_G2(R, 1, T, Ys, Zs, Base),

    %they can calculate commitE
    E_list = calc_E(R, 1, T, Zs, Commits, E),%commits are related to Fs
    CommitE = pedersen:sum_up(E_list, E),
    CommitE = element(1, OpenE),

    0 = add(G2, sub(element(2, OpenG), element(2, OpenE), Base), Base),
    
    success;
test(5) ->
    E = secp256k1:make(),
    Base = secp256k1:order(E),
    success.


    
    


    
