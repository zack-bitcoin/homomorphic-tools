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
    GroupOrder = 7,
    infinity = elliptic:multiplication(H, GroupOrder, E),
    H = elliptic:multiplication(H, GroupOrder+1, E),
    infinity = elliptic:multiplication(G, GroupOrder, E),
    G = elliptic:multiplication(G, GroupOrder+1, E),
  
    C = commit([1, 2, 3], [G, H, I], E),
    C23 = commit([2, 3], [H, I], E),%proof of 1
    C = commit([1, 1], [G, C23], E),%verify 1
    C13 = commit([1, 3], [G, I], E),%proof of 2
    C = commit([1, 2], [C13, H], E),%verify 2
 
    success.
