-module(multiproof).
-export([test/1]).

%multiproofs for pedersen IPA.
%We are trying merge IPA.

%going through this paper: https://dankradfeist.de/ethereum/2021/06/18/pcs-multiproofs.html

%vitalik wrote a little on this topic as well: https://vitalik.ca/general/2021/06/18/verkle.html

-record(p, {e, b, g, h, q, domain, a, da, ls}).

make_parameters(Domain, E) ->
    Base = secp256k1:order(E),
    {Gs, Hs, Q} = pedersen:basis(4, E),
    DAC = poly:calc_DA(Domain, E),
    DA = poly:c2e(DAC, Domain, Base),
    Ls = poly:lagrange_polynomials(Domain, Base),
    PA = poly:calc_A(Domain, Base),
    #p{e = E, b = Base, g = Gs, h = Hs, q = Q,
       domain = Domain, a = PA, da = DA, ls = Ls}.
    

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
    Exp = sub(0, 
           divide(RA, sub(T, hd(Zs), Base), Base),
           Base),
    [pedersen:mul(hd(Commits), Exp, E)|
     neg_calc_E(R, mul(RA, R, Base), T,
                tl(Zs), tl(Commits), E)].

mul_r_powers(_, _, [], _) -> [];
mul_r_powers(R, A, [C|T], Base) ->
    [ff:mul(C, A, Base)|
     mul_r_powers(
       R, ff:mul(A, R, Base), T, Base)].

neg_calc_E2(R, T, Zs, Cs, E) ->
    %sum_i  Ci*(R^i/(T-Zi))
    Base = secp256k1:order(E),
    Zs2 = lists:map(
            fun(Z) -> ff:sub(T, Z, Base) end,
            Zs),
    %Zs3 = secp256k1:invert_batch(Zs2, Base),
    Zs3 = ff:batch_inverse(Zs2, Base),
    Zs4 = mul_r_powers(R, 1, Zs3, Base),
    Zs5 = lists:map(
            fun(Z) -> 
                    ff:neg(Z, Base) 
            end, Zs4),
    Cs2 = lists:map(
            fun(C) -> secp256k1:to_jacob(C) end,
            Cs),
    J = secp256k1:multi_exponent(Zs5, Cs2, E),%the slow part.
    secp256k1:to_affine(J, E).



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
      Commits_e,
      #p{g = Gs, h = Hs, q = Q, e = E, da = DA,
        a = PA, ls = Ls}) ->
    Base = secp256k1:order(E),
    %io:fwrite("prove 0 G\n"),
    %io:fwrite({Gs}),

    io:fwrite("prove 1 G\n"),
    %todo, this can come from the tree as well.
    Ys = lists:zipwith(
           fun(F, Z) ->
                   poly:eval_e(Z, F, Domain, Base)
           end, As, Zs),
    io:fwrite("prove 2 G\n"),
    Timestamp1 = erlang:timestamp(),
    R = calc_R(Commits_e, Zs, Ys, <<>>),
    G2 = calc_G_e(R, As, Ys, Zs, Domain, DA, Base),
    CommitG_e = pedersen:commit(G2, Gs, E),
    T = calc_T(CommitG_e, R),
    GT = poly:eval_outside(T, G2, Domain, PA, DA, Base),
    He = calc_H_e(R, 1, T, As, Zs, Base),
    G_sub_E_e = poly:sub(G2, He, Base),
    EV = poly:eval_outside_v(T, Domain, PA, DA, Base),
    Timestamp2 = erlang:timestamp(),
    OpenG_sub_E_e = pedersen:make_ipa(
                     G_sub_E_e, EV,
                     Gs, Hs, Q, E),
    Timestamp3 = erlang:timestamp(),
    io:fwrite("ipa time : "),
    io:fwrite(integer_to_list(timer:now_diff(Timestamp3, Timestamp2))),
    io:fwrite("\n"),
    io:fwrite("other proving time: "),
    io:fwrite(integer_to_list(timer:now_diff(Timestamp2, Timestamp1))),
    io:fwrite("\n"),
    {CommitG_e, Commits_e, OpenG_sub_E_e}.
verify({CommitG, Commits, Open_G_E}, Zs, Ys, 
       #p{g = Gs, h = Hs, q = Q, e = E,
         domain = Domain, da = DA, a = PA}) ->
    Base = secp256k1:order(E),
    R = calc_R(Commits, Zs, Ys, <<>>),
    T = calc_T(CommitG, R),
    EV = poly:eval_outside_v(
           T, Domain, PA, DA, Base),
    T3 = erlang:timestamp(),
    io:fwrite("verify ipa start\n"),%0.3
    true = pedersen:verify_ipa(
             Open_G_E, EV, Gs, Hs, Q, E),
    T4 = erlang:timestamp(),
    io:fwrite("verify ipa end\n"),
    io:fwrite("calc G2\n"),
    G2 = calc_G2(R, 1, T, Ys, Zs, Base),
    T5 = erlang:timestamp(),
    io:fwrite("neg e list\n"),
    CommitNegE = neg_calc_E2(R, T, Zs, Commits, E),%the slow step
    T6 = erlang:timestamp(),
    io:fwrite("calc commit g-e\n"),
    CommitG_sub_E = pedersen:add(CommitG, CommitNegE, E),
    CommitG_sub_E = element(1, Open_G_E),
    io:fwrite("calc neg e: "),
    NegE = timer:now_diff(T6, T5),
    io:fwrite(integer_to_list(timer:now_diff(T6, T5))),
    io:fwrite("\n"),
    io:fwrite("proofs per second: "),
    io:fwrite(integer_to_list(round(length(Zs) * 1000000 / NegE))),
    io:fwrite("\n"),
    %io:fwrite({timer:now_diff(T4, T3),%ipa
    %           timer:now_diff(T5, T4),
    %           timer:now_diff(T6, T5)
               %timer:now_diff(T7, T6)
%}),
    0 == add(G2, element(2, Open_G_E), Base).

range(X, X) -> [];
range(A, X) when A<X -> 
    [A|range(A+1, X)].

many(_, 0) -> [];
many(X, N) when N > 0 -> 
    [X|many(X, N-1)].
    
                          
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
    %in coefficient format. slower, but possibly easier to understand.
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
    Domain = [1,2,3,4],
    io:fwrite("setup parameters\n"),
    E = secp256k1:make(),
    P = make_parameters(Domain, E),
    Base = P#p.b,
    io:fwrite("prepare values to commit\n"),
    A1 = [1,1,2,3],
    A2 = [2,4,6,8],
    A3 = [2,3,5,7],
    A4 = [3,5,8,13],
    As = [A1, A2, A3, A4],
    Zs = [1,2,3,2],
    Ys = lists:zipwith(
           fun(F, Z) ->
                   poly:eval_e(Z, F, Domain, Base)
           end, As, Zs),
    io:fwrite("make proof\n"),
    Gs = E#p.g,
    Commits = lists:map(
                  fun(A) ->
                          poly:commit_c(A, Gs, E)
                  end, As),
    Proof = prove(As, Zs, Domain, Commits, P),
    io:fwrite("verify proof\n"),
    true = verify(Proof, Zs, Ys, P),
    success;
test(6) ->

    %10:    0.0128  781   
    %100:   0.0690  1449   6
    %500:           2229   6
    %1000:          2600   7
    %2000:  0.7669  2880   8
    %3000:          3032   9
    %4000:  1.4049  2959   9
    %5000:          2918   10, 11 is worse 2502
    %10000:         3000   11, 10: 2743, 12: 2179
    %20000:         2500   12,

    %3000:  1.3960  2149   11
    %4000:  1.7172  2329   11
    %5000:  2.6972  1853   12
    %10000: 6.596   1516   13

    Many = 1000,
    %verifies 49 per second
    %we want ~120 000 per second. a factor of 2500 short.
    %switching to jacob format saves about 5x.
    %bucket method saves about 24x
    %rewrite to C saves around 5x
    E = secp256k1:make(),
    Base = secp256k1:order(E),
    Root4 = primitive_nth_root(4, E),
    Root4b = mul(Root4, Root4, Base),
    Root4c = mul(Root4b, Root4, Base),
    Domain = [1, Root4, Root4b, Root4c],
    io:fwrite("setup parameters\n"),
    P = make_parameters(Domain, E),
    %Base = P#p.b,
    io:fwrite("prepare values to commit\n"),
    As = lists:map(fun(R) -> [sub(0, R, Base),
    %As = lists:map(fun(_R) -> [sub(0, 4, Base),
                              sub(0, R+3, Base),
                              sub(0, R+2, Base),
                              sub(0, R+1, Base)] end,
                   range(0, Many)),
    Zs = many(hd(tl(Domain)), Many),
    Ys = lists:zipwith(
           fun(F, Z) ->
                   poly:eval_e(Z, F, Domain, Base)
           end, As, Zs),
    Gs = P#p.g,
%    Commits = lists:map(
%                fun(A) ->
                        %poly:commit_c(A, Gs, E)
%                        pedersen:commit_old(A, Gs, E)
%                end, As),
    Commit1 = pedersen:commit(hd(As), Gs, E),
    Commits = lists:map(
      fun(A) ->
                                                %poly:commit_c(A, Gs, E)
              
              pedersen:commit(A, Gs, E)
              %Commit1
      end, As),
    io:fwrite("make proof\n"),
    %T1 = erlang:timestamp(),
    Proof = prove(As, Zs, Domain, Commits, P),
    T2 = erlang:timestamp(),
    io:fwrite("verify proof\n"),
    true = verify(Proof, Zs, Ys, P),
    T3 = erlang:timestamp(),
    io:fwrite("\n"),
    {%timer:now_diff(T2, T1),
     verify_time, timer:now_diff(T3, T2)}.
%success.
    
                          
    

    
    


    
