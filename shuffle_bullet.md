shuffle bullet.
==============

How to include in a bullet proof a variable shuffling, so verifiers of the proof can't know which of the shuffled variables is which.


Starting with variables A, B.
Ending with variables C, D.

Use the constraint:
(A - x) * (B - x) = (C - x) * (D - x)

if this holds for random x, then {A, B} must equal {C, D} in some order.

First do a multiplicative constraint on each side, then compare both sides as a linear constraint.

multiplicative constraints
===============

x * y = z

secret-secret multiplication

linear constraints
==============

secret variables with cleartext weights

a*x + b*y + c*z ... = 0















