-module(elgamal).
-export([test/1]).

-record(curve, {a, b, g, mod}).

commit([V1, V2], [G1, G2], E) ->
    #curve{
        mod = N
       } = E,
      elliptic:addition(
        elliptic:multiplication(G1, V1, E),
        elliptic:multiplication(G2, V2, E),
        E);
commit(V, G, E) ->
    #curve{
        mod = N
       } = E,
      elliptic:addition(
        elliptic:multiplication(hd(G), hd(V), E),
        commit(tl(V), tl(G), E),
        E).
    
test(1) ->
    A = 0,
    B = 7,
    P = 13,
    E = elliptic:make(A, B, P),
    #curve{
            g = G
          } = E,
    H = elliptic:addition(G, G, E),
    I = elliptic:addition(G, H, E),

    %G, and H, and I need to be generators of a prime ordered group.
    %we are making 3 generators because we want to be able to store 3 variables in this accumulator.
    GroupOrder = 7,
    infinity = elliptic:multiplication(H, GroupOrder, E),
    H = elliptic:multiplication(H, GroupOrder+1, E),
    infinity = elliptic:multiplication(G, GroupOrder, E),
    G = elliptic:multiplication(G, GroupOrder+1, E),
    [V1, V2, V3] = [2, 2, 3],
    C = commit([V1, V2, V3], [G, H, I], E),
    Proof1 = commit([V2, V3], [H, I], E),
    C = commit([V1, 1], [G, Proof1], E),%verify V1
    Proof2 = commit([V1, V3], [G, I], E),
    C = commit([1, V2], [Proof2, H], E),%verify V2

 
    success.
    



