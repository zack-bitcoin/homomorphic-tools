-module(pedersen_tree).
-export([test/1]).

%we need to remember a linear hierarchy structure of values commited, organized in order of generator size, so we can keep track of which one needs to point at which other.
%we need a tree structure that keeps track of partially computed commitments to values in the accumulator.
%we want to be able to quickly generate proofs for this accumulator, so walking down this tree and multiplying the values should calculate the commitment.
% commiting to A B C D
% (stem (ABCD) 
%   (stem (AB) (leaf A) (leaf B)) 
%   (stem (CD) (leaf C) (leaf D)))

%A proof of element C is AB * D
%so the pattern here is that you walk down the tree, and you keep grabbing elliptic curve values from the path that you do not take. So all together you need to read 2*log2(# elements in the tree) elements to build a proof.

-record(leaf, {commitment = infinity, %pedersen commit to only this one element. "infinity" is the zero element.
               value, %value we had accumulated over.
               g, %group generator for this variable. it acts as a key if you think of this as a key-value storage.
               next %group generator of the next higher ranked element
              }).
-record(stem, {commitment, %a pedersen commitment to all the elements in this branch of the tree.
               a, b}).%a and b can be a stem or a leaf.

%pedersen vector commit.
commit([V1, V2], [G1, G2], E) ->
      secp256k1:addition(
        secp256k1:multiplication(G1, V1, E),
        secp256k1:multiplication(G2, V2, E),
        E);
commit(V, G, E) ->
      secp256k1:addition(
        secp256k1:multiplication(hd(G), hd(V), E),
        commit(tl(V), tl(G), E),
        E).
verify(G, V, C, Root, E) ->
    Root == commit([V, 1], [G, C], E).
hash(G) -> crypto:hash(sha256, G).

make_pre_image(E) ->
    G0 = crypto:strong_rand_bytes(32),
    G = hash(G0),
    B = secp256k1:on_curve(G, E),
    if
        B -> {G0, G};
        true -> make_pre_image(E)
    end.
            
add(G0, V, A, E) ->
    %G0 is the pre-image of a generator. we hash it to make the generator.
    G = hash(G0),

    %verify that the generator is valid
    true = secp256k1:on_curve(G, E),

    %V is the value to be stored
    %E is the elliptic curve
    %should update log2(#elements in accumulator) values in the binary tree. updating the partial multiplications. Can be up to double, if we are adding a node near the border between two branches of the tree.
    %it needs a pointer to the next-highest element, and the next lower element needs to point to it. So an add triggers an update.
    
    ok.
update(G, V, A, E) ->
    %G is the generator. it acts as a key.
    %V is the new value to store.
    %E is the elliptic curve

    %should update log2(#elements in accumulator) values in the binary tree. updating the partial multiplications. 
    ok.
prove(G, A, E) ->
    #stem{
       commitment = Root
      } = A,
    %G is the generator, which acts as a key in the tree.
    %E is the elliptic curve.
    %V is the value that was stored.

    %while walking down the tree, we should multiply the values along the paths that we do not walk.
    %root is the root of the tree now.
    V = 0,
    C = 0,
    {V, C, Root}.


test(1) ->
    E = secp256k1:make(),
    Ps = lists:map(fun(_) ->
                           secp256k1:gen_point(E)
                   end, [1,2,3,4,5]),
    [P1, P2, P3, P4, P5] = Ps,

    %storing some prime numbers in the accumulator. we can store any numbers modulus E#curve.p, the prime base of the finite field that the elliptic curve is defined over.
    [V1, V2, V3, V4, V5] =
        [5, 7, 11, 13, 17],
    V = [V1, V2, V3, V4, V5],
    C = commit(V, Ps, E),
    Proof = commit([V1, V2, V3, V5],
                    [P1, P2, P3, P5],
                    E),
    C = commit([V4, 1], [P4, Proof], E),
    success;
test(2) ->
    E = secp256k1:make(),
    A0 = #leaf{},

    {G0, G} = make_pre_image(E),
    
    A1 = add(G0, 17, A0, E),
    A2 = update(G, 18, A1, E),

    {17, C1, Root1} = prove(G, A1, E),
    true = verify(G, 17, C1, Root1, E),

    {18, C2, Root2} = prove(G, A2, E),
    true = verify(G, 18, C2, Root2, E),

    ok.
        

