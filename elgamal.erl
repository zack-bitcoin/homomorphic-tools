-module(elgamal).
-export([test/1]).

-record(curve, {a, b, g, mod}).

commit(V, H, GO, E) ->
    #curve{
        g = G,
        mod = N
       } = E,
    R = random:uniform(GO-1),
    {R, elliptic:addition(
          elliptic:multiplication(G, V, E),
          elliptic:multiplication(H, R, E),
          E)}.

verify(V, R, Commitment, H, E) ->
    #curve{
        g = G,
        mod = N
       } = E,
    Commitment ==
        elliptic:addition(
          elliptic:multiplication(G, V, E),
          elliptic:multiplication(H, R, E),
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

    %G and H need to be generators of a prime ordered group.
    GroupOrder = 7,
    infinity = elliptic:multiplication(H, GroupOrder, E),
    H = elliptic:multiplication(H, GroupOrder+1, E),
    infinity = elliptic:multiplication(G, GroupOrder, E),
    G = elliptic:multiplication(G, GroupOrder+1, E),
   
    V = 2,
    {R, C} = commit(V, H, GroupOrder, E),
    true = verify(V, R, C, H, E),

    %partially homomorphic over addition.
    true = verify(V+V, R+R, 
                  elliptic:addition(C, C, E), 
                  H, E),
    F = 5,
    M = elliptic:multiplication(C, F, E), 
   
    true = verify((V*F) rem GroupOrder, (R*F) rem GroupOrder, 
                  M,
                  H, E),
    success;
test(2) ->    
    A = 0,
    B = 7,
    P = 13,
    E = elliptic:make(A, B, P),
    #curve{
            g = G
          } = E,
    H = elliptic:addition(G, G, E),
    GroupOrder = 7,

    V1 = 1,
    V2 = 2,
    V3 = 4,
    V4 = 8,
    %multi-commit
    V = V1 + V2 + V3 + V4,
    {R, C} = commit(V, H, GroupOrder, E),
    true = verify(V, R, C, H, E),
    %V, R, C
  
    %membership proof
    {R1, C1} = commit(V1, H, GroupOrder, E),
    VA = (V - V1) rem P,
    %R1, V1, C1, 

    %verify membership
    true = verify(V1, R1, C1, H, E),
    VA = (V - V1) rem P,
    {_, CA} = commit(VA, H, GroupOrder, E),
    C = elliptic:addition(C1, CA, E),

    success.
