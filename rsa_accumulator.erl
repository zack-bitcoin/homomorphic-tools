-module(rsa_accumulator).
-export([test/1]).

-record(acc, {p1, p2, mod, phi, g, l,
              v, expt = 1}).

% nice example code https://github.com/oleiba/RSA-accumulator/blob/master/main.py

mod(X,Y)->(X rem Y + Y) rem Y.

gcd(A, B) when
      ((A < 0) or (B < 0)) ->
    undefined;
gcd(A, 0) -> A;
gcd(A, B) when A < B -> 
    gcd(B, A);
gcd(A, B) -> 
    %gcd(B, A rem B).
    gcd(B, mod(A, B)).

to_bits_list(0) -> [0];
to_bits_list(N) ->
    B = N rem 2,
    [(N rem 2)|to_bits_list(N div 2)].
rlpow(B, E, N) ->
    % math:pow(B, E) rem N
    E2 = to_bits_list(E),
    rlpow2(1, B, E2, N).
%rlpow2(A, _, [], _) -> A;
rlpow2(A, _, [0], _) -> A;
rlpow2(A, C, [1], N) -> 
    (A * C) rem N;
rlpow2(A, C, [1|T], N) -> 
    rlpow2((A*C) rem N,
           (C*C) rem N, 
           T, N);
rlpow2(A, C, [0|T], N) -> 
    rlpow2(A,
           (C*C) rem N, 
           T, N).

lcm(A, B) ->
    A * B div gcd(A, B).
carmichael(P1, P2) ->
    %lcm(((P1 - 1) div 2),
    %    ((P2 - 1) div 2)).
    lcm(((P1 - 1)),
        ((P2 - 1))).

new(P1, P2) ->
    %created from 2 prime numbers.
    N = P1 * P2,
    F = (P1-1)*(P2-1),%euler's phi.
    %choose random G coprime to N.
    L = carmichael(P1, P2),
    G = choose_random_star(N),
    if
        false ->
            io:fwrite("G: "),
            io:fwrite(integer_to_list(rlpow(G, L+5, N))),
            io:fwrite("\n"),
            io:fwrite(integer_to_list(rlpow(G, (2*L)+5, N))),
            io:fwrite("\n"),
            io:fwrite(integer_to_list(rlpow(G, (20*L)+5, N))),
            io:fwrite("\n");
        true -> ok
    end,
    #acc{p1 = P1, p2 = P2, 
         phi = F, mod = N, 
         l = L, v = G,
         g = G}.

store([], A) -> A;
store(Ps, A) when is_list(Ps) -> 
    P = lists:foldl(
          fun(C, B) -> C * B end,
          1, 
          Ps),
    store(P, A);
store(P, A) ->
    %P is a prime number that are not already in A.
    #acc{
       v = V1,
       expt = E,
       g = G,
       mod = N
      } = A,
    E2 = (E*P),
    V2 = rlpow(V1, P, N),
    A#acc{v = V2, expt = E2}.

prove(P, A) ->
    %V ^ (1/P) mod N
    %Pth root of V mod N.
    #acc{
       v = V,
       g = G,
       mod = N,
       expt = E
      } = A,
    %B = E rem P,
    B = mod(E, P),
    if
        B == 0 ->
            rlpow(G, (E div P), N);
        true -> 
            %io:fwrite("cannot prove what is not accumulated."),
            false
    end.
%bezout coefficients for A and B are S and T
%  such that (S*A) + (T*B) = gcd(A, B)
% Extended Euclidean Algorithm finds S and T.
eea(A, B)
  when ((A < 1) 
        or (B < 1)) ->
    undefined;
eea(A, B) ->
    eea_helper(A, 1, 0, B, 0, 1).
eea_helper(G, S, T, 0, _, _) ->
    {G, S, T};
eea_helper(G0, S0, T0, G1, S1, T1) ->
    Q = G0 div G1,
    eea_helper(G1, S1, T1, 
               G0 - (Q*G1),
               S0 - (Q*S1),
               T0 - (Q*T1)).
prove_empty(P, A) ->
    %V = G^E
    %find a, b such that ((a*P)+(b*E)) mod N = 1
    %bezout coefficients
    %proof = [G^a, b]
    #acc{
          v = V,
          g = G,
          expt = E,
          mod = N
        } = A,
    {1, X0, Y0} = eea(P, E),
    D = if
            (X0 < 0) -> 
                X = -X0,
                IG = inverse(G, N),
                rlpow(IG, X, N);
            true -> rlpow(G, X0, N)
        end,
    {D, Y0}.
verify_empty({D, B}, P, A) ->
    %D^P * V^B 
    % = G ^ (a*P + E*B)
    % = G ^ 1 = G
    #acc{
          v = V,
          g = G,
          mod = N
        } = A,
    BPart = 
        if
            (B > 0) -> rlpow(V, B, N);
            true ->
                B_positive = -B,
                IV = inverse(V, N),
                %1 = mod((V * IV),N),
                rlpow(IV, B_positive, N)
        end,
    G == mod(rlpow(D, P, N) 
              * BPart,
              N).

inverse(A, N) ->    
    {G, S, T} = eea(A, N),
    case G of
        1 -> S;
        _ -> 
            io:fwrite("inverse does not exist"),
            does_not_exist
    end.
    
verify(false, _, _) -> false;
verify(Proof, P, A) ->
    #acc{
        v = V,
        mod = N} = A,
    R = rlpow(Proof, P, N),
    R == V.

choose_random_star(N) ->
    R = random:uniform(N),
    B = gcd(R, N),
    if
        (B == 1) -> R;
        true -> choose_random_star(N)
    end.
            

test(1) ->
    %A = new(13, 17),
    A = new(7727, 7741),
    Prime = 5,
    A2 = store(Prime, A), 
    P = prove(Prime, A2),
    false = prove(Prime, A),
    true = verify(P, Prime, A2),
    false = verify(P, 3, A2),
    false = verify(45, Prime, A2),
    false = verify(45, 3, A2),
    P2 = prove_empty(3, A2),
    true = verify_empty(P2, 3, A2),
    false = verify_empty(P2, 7, A2),
    success;
   
test(2) -> 
    %A = new(13, 17),
    A = new(7727, 7741),
    Primes = [3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37],
    %Primes = [3],
    A2 = store(Primes, A),
    P2 = prove_empty(43, A2),
    true = verify_empty(P2, 43, A2),
    false = verify_empty(P2, 47, A2),
    {lists:map(fun(X) ->
                      P = prove(X, A2),
                       %io:fwrite(integer_to_list(P)),
                      %io:fwrite("\n"),
                      true = verify(P, X, A2)
              end, Primes),
     A,
     A2}.
    
