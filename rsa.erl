-module(rsa).
-export([test/0]).

#record(gen, {p1, p2}).

make(P1, P2) ->
    %created from 2 prime numbers.
    N = P1 * P2,
    F = (P1-1)*(P2-1),%euler's phi.
    #gen{p1 = P1, p2 = P2, mod = N, phi = F}.

make_keys(Gen) ->
    %choose e. between 1 and phi.
    % e must be coprime to N and phi.
    % e is the public key, used for encrypting messages.

    % d * e mod F should be 1.
    ok.
    

encrypt(Msg, Priv, Gen) ->
    ok.
    

test() ->
    G = make(2, 7),
    success.
