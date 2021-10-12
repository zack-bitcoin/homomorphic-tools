-module(rsa_accumulator).
-export([test/0]).

-record(acc, {p1, p2, mod, phi, g, 
              v = 1, expt = 1}).

gcd(A, B) when
      ((A < 0) or (B < 0)) ->
    undefined;
gcd(A, 0) -> A;
gcd(A, B) when A < B -> 
    gcd(B, A);
gcd(A, B) -> 
    gcd(B, A rem B).

to_bits_list(0) -> [];
to_bits_list(N) ->
    B = N rem 2,
    [(N rem 2)|to_bits_list(N div 2)].
rlpow(B, E, N) ->
    % math:pow(B, E) rem N
    E2 = to_bits_list(E),
    rlpow2(1, B, E2, N).
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

new(P1, P2) ->
    %created from 2 prime numbers.
    N = P1 * P2,
    F = (P1-1)*(P2-1),%euler's phi.
    %choose random G coprime to N.
    G = choose_random_star(N),
    #acc{p1 = P1, p2 = P2, 
         phi = F, mod = N, 
         g = G}.

store(P, A) ->
    %P is a prime number that are not already in A.
    #acc{
       expt = E,
       g = G,
       mod = N
      } = A,
    E2 = (E*P) rem N,
    V = rlpow(G, E2, N),
    A#acc{v = V, expt = E2}.

inverse(P, A) ->
    #acc{
         phi = F,
         mod = N
        } = A,
    rlpow(P, F-1, N).

prove(P, A) ->
    %V ^ (1/P) mod N
    #acc{
       v = V,
       g = G,
       mod = N,
       expt = E
      } = A,
    rlpow(G, E div P, N).
    %IP = inverse(P, A),
    %1 = (P*IP) rem N,
%rlpow(V, IP, N).

verify(Proof, P, A) ->
    #acc{
        v = V,
        mod = N} = A,
    R = rlpow(Proof, P, N),
    R == V.
    

choose_random_star(N) ->
    R = random:uniform(N),
    B = gcd(R, N),
    case B of
        1 -> R;
        _ -> choose_random_star(N)
    end.
            

test() ->
    A = new(13, 17),
    Prime = 2,
    A2 = store(Prime, A), 
    P = prove(Prime, A2),
    true = verify(P, Prime, A2),
    false = verify(P, 3, A2),
    false = verify(45, 2, A2),
    false = verify(45, 3, A2),
    success.
    
