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

calc_G_e(R, As, Ys, Zs, Domain, DA, Base) ->
    GP = lists:zipwith3(
           fun(A, Y, Z) ->
                   X = poly:sub(
                         A, %subtract Y from every element in A.
                         poly:c2e([Y], Domain, Base), 
                         Base),
                   %io:fwrite({DA, Z, Domain}),
                   poly:div_e(
                     X,
                     Domain,
                     DA,
                     Z,
                     Base)
           end, As, Ys, Zs),
    %io:fwrite({GP}),
    calc_G_e_helper(1, R, GP, Base).
calc_G_e_helper(_, _, [], _) -> [];
calc_G_e_helper(RA, R, [P|T], Base) -> 
    X = poly:mul_scalar(RA, P, Base),
    case T of
        [] -> X;
        _ ->
            poly:add(
              X,
              calc_G_e_helper(
                poly:fmul(RA, R, Base), 
                R, T, Base),
              Base)
    end.
    
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
neg_calc_E(_, _, _, _, [], _) -> [];
neg_calc_E(R, RA, T, Zs, Commits, E) ->
    Base = secp256k1:order(E),
    [pedersen:mul(
       hd(Commits), 
       sub(0, 
           divide(RA, sub(T, hd(Zs), Base), Base),
           Base),
       E)|
     neg_calc_E(R, mul(RA, R, Base), T,
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

calc_H_e(_, _, _, [], [], _) -> [];
calc_H_e(R, RA, T, As, Zs, Base) ->
    X = poly:mul_scalar(
          divide(RA, sub(T, hd(Zs), Base), Base),
          hd(As),
          Base),
    if
        (length(As) == 1) -> X;
        true ->
            poly:add(
              X,
              calc_H_e(R, mul(RA, R, Base), T, tl(As),
                       tl(Zs), Base),
              Base)
    end.
             
calc_R([], [], [], B) -> 
    <<R:256>> = pedersen:hash(B),
    R;
calc_R([{C1, C2}|CT], [Z|ZT], [Y|YT], B) -> 
    B2 = <<B/binary, Z:256, Y:256, 
           C1:256, C2:256>>,
    calc_R(CT, ZT, YT, B2).
calc_T({C1, C2}, R) ->
    B = <<C1:256, C2:256, R:256>>,
    <<R2:256>> = pedersen:hash(B),
    R2.

prove(As, %committed data
      Zs, %the slot in each commit we are reading from. A list as long as As. Made up of elements that are in the domain.
      Domain, %These are the coordinates we are using for lagrange basis. (This is probably the roots of unity)
      Gs, Hs, Q, %elliptic curve generator points for pedersen commits and inner product arguments.
      E, DA, PA, Ls) -> %the elliptic curve
    Base = secp256k1:order(E),
    Commits_e = lists:map(
                  fun(A) ->
                          poly:commit_c(A, Gs, E)
                  end, As),
    Ys = lists:zipwith(
           fun(F, Z) ->
                   poly:eval_e(Z, F, Domain, Base)
           end, As, Zs),
    R = calc_R(Commits_e, Zs, Ys, <<>>),
    G2 = calc_G_e(R, As, Ys, Zs, Domain, DA, Base),
    CommitG_e = pedersen:commit(G2, Gs, E),
    T = calc_T(CommitG_e, R),
    GT = poly:eval_outside(T, G2, Domain, PA, DA, Base),
    He = calc_H_e(R, 1, T, As, Zs, Base),
    G_sub_E_e = poly:sub(G2, He, Base),
    EV = poly:eval_outside_v(T, Domain, PA, DA, Base),
    OpenG_sub_E_e = pedersen:make_ipa(
                     G_sub_E_e, EV,
                     Gs, Hs, Q, E),
    {CommitG_e, Commits_e, OpenG_sub_E_e}.
                                
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
    {Gs, Hs, Q} = pedersen:basis(4, E),
    Base = secp256k1:order(E),
    A1 = [1,1,2],
    A2 = [2,4,6],
    A3 = [2,3,5],
    A4 = [3,5,8],
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
    R = calc_R(Commits, Zs, Ys, <<>>),
    G = calc_G(R, Fs, Ys, Zs, Base),

    CommitG = pedersen:commit(G, Gs, E),%in the notes it is D.
    
    T = calc_T(CommitG, R),

    GT = PC:eval_poly(T, G, Base),

    %E_list = calc_E(R, 1, T, Zs, Commits, E),
    %CommitE = pedersen:sum_up(E_list, E),

    %need to calculate an opening to commit E at T.

    H = calc_H(R, 1, T, Fs, Zs, E),%is summing up polynomials, H has a length based on how many variables there are, not how long Fs or Zs is.
    %CommitE = pedersen:commit(H, Gs, E),
    %sumi  r^i * f_i(X)/(T - Z_i)
    %io:fwrite({Gs}),
    Powers4 = PC:powers(T, 4, Base),
    G_sub_E = lists:zipwith(
                fun(A, B) -> sub(A, B, Base) end,
                G++[0,0], H ++ [0]),
                                     
    OpenG_sub_E = pedersen:make_ipa(
              G_sub_E, PC:powers(T, 4, Base),
              Gs, Hs, Q, E),

    %send an opening to G-E at T.
    %send a commit to G
    %send the Commits 
    %they know the Gs, Hs, Q, and E as system defaults.
    %they know the Zs and Ys from processing the block and making a list of things that need to be proved.

    %trying to verify that G is a polynomial.

    R = calc_R(Commits, Zs, Ys, <<>>),
    T = calc_T(CommitG, R),
    Powers4 = PC:powers(T, 4, Base),
    true = pedersen:verify_ipa(
             OpenG_sub_E, Powers4, Gs, Hs, Q, E),
    G2 = calc_G2(R, 1, T, Ys, Zs, Base),

    Neg_E_list = neg_calc_E(R, 1, T, Zs, Commits, E),%commits are related to Fs
    CommitNegE = pedersen:sum_up(Neg_E_list, E),
    CommitG_sub_E = pedersen:add(CommitG, CommitNegE, E),
    CommitG_sub_E = element(1, OpenG_sub_E),

    0 = add(G2, element(2, OpenG_sub_E), Base),

    {CommitG, %an elliptic point element
     Commits, %one elliptic point per IPA being proved
     OpenG_sub_E %an single IPA, as 4 + 2*log2(many variables per ipa) elliptic curve points, and one integer.
    };
    %success;
test(5) ->
    E = secp256k1:make(),
    Base = secp256k1:order(E),
    {Gs, Hs, Q} = pedersen:basis(4, E),
    A1 = [1,1,2,3],
    A2 = [2,4,6,8],
    A3 = [2,3,5,7],
    A4 = [3,5,8,13],
    As = [A1, A2, A3, A4],
    Zs = [1,2,3,2],
    Domain = [1,2,3,4],
    io:fwrite("setup parameters\n"),
    DAC = poly:calc_DA(Domain, E),
    DA = poly:c2e(DAC, Domain, Base),%todo should save this somewhere
    Ls = poly:lagrange_polynomials(Domain, Base),%todo save this somewhere
    PA = poly:calc_A(Domain, Base),%todo save this somewhere
    io:fwrite("make proof\n"),
    {CommitG_e, Commits_e, OpenG_sub_E_e} = 
        prove(As, Zs, Domain, Gs, Hs, Q, E, DA, PA, Ls),
    io:fwrite("verify proof\n"),
    
    
    %they know the Domain, Gs, Hs, Q, and E as system defaults.
    %they know the Zs and Ys from processing the block and making a list of things that need to be proved.
    Ys = lists:zipwith(
           fun(F, Z) ->
                   poly:eval_e(Z, F, Domain, Base)
           end, As, Zs),
    %trying to verify that G is a polynomial.
    R = calc_R(Commits_e, Zs, Ys, <<>>),
    T = calc_T(CommitG_e, R),
    EV = poly:eval_outside_v(T, Domain, PA, DA, Base),
    true = pedersen:verify_ipa(
             OpenG_sub_E_e, EV, Gs, Hs, Q, E),

    G2 = calc_G2(R, 1, T, Ys, Zs, Base),

    %less confident
    %Neg_E_list = neg_calc_E(R, 1, T, Zs, Commits, E),%commits are related to Fs
    %CommitNegE = pedersen:sum_up(Neg_E_list, E),
    %CommitG_sub_E = pedersen:add(CommitG, CommitNegE, E),
    %CommitG_sub_E = element(1, OpenG_sub_E),


    Neg_E_list_e = neg_calc_E(R, 1, T, Zs, Commits_e, E),%commits are related to Fs
    CommitNegE_e = pedersen:sum_up(Neg_E_list_e, E),
    CommitG_sub_E_e = pedersen:add(CommitG_e, CommitNegE_e, E),
    CommitG_sub_E_e = element(1, OpenG_sub_E_e),

    0 = add(G2, element(2, OpenG_sub_E_e), Base),
    success.
    
    


    
