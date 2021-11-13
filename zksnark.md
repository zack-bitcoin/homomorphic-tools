One interesting aspect of zksnarks.
If you build a program as a zksnark, that makes it more expensive for the prover and verifier based on how many variables are in that program. And the variables are immutible, so there are a lot.
But once you have built this program, it is almost free for the prover and verifier to run that program on more data.

So it creates this puzzle, where you want to find the smallest zksnark circuit that can be iterated on different data many times in order to calculate the result of your program.

For a private oracle verkle tree, in order to prove some data is in the tree, without revealing where we are reading from, every time we read from the tree, we will look at nodes of the tree iteratively. we are going to be privately selecting one of the 256 children of a node, in order to choose which path we want to walk down.

So our private zksnark circuit is going to need the ability to privately select 1 value from a list of 256 values.

But if we put 256 selectible values into a circuit, that is 256 variables. So the program will take 256 steps to be proven or verified. It will be slow.

Im looking into building a 2-shuffle circuit that can combine with itself, so we can make a very short program for this.

So, I came up with a circuit that can mix a list of 2 values, and I set it up so it can be iterated on itself.
In order to be able to select any of the 256 elements, we need to run the 2-shuffle circuit 256 times.
But since the 2-shuffle circuit only has 12 elements, it only takes 12 elliptic curve steps to make or verify a proof.

These zksnark programs are set up so that every computation can happen at the same time.
You provide something called a witness, which is a list of numbers that indicate the values of every variable in the zksnark program. And proof is checking whether this list of variables is a valid way of running the program.
Since it knows all the values ahead of time, it can calculate all parts of the program in parallel, and then check that all the values match what the witness says they should be.

The values in my 2-shuffle circuit, if we are choosing an element from the list [5, 7]:
[1, 5, 7, R, 5-R, 7-R, 0, 5-R, 7-R, (5-R)*(7-R), 7-R, 5-R]

All zksnark programs that include an addition or subtraction need a "1" element at the start.

When you run a zksnark program, any of the values in the witness can potentially be encrypted.
the 7th element, `R` for example, we would want this value to be encrypted. So the person running the program wouldn't know the R value, they would know an elliptic curve point that has a mathematical relationship with R. But it is impossible to guess what R is, just from looking at that elliptic curve point.

In order to maintain the privacy of circuit values, you have to mix your numbers with blinding factors. Without the blinding factor, there are very values that a variable could possibly have. So an attacker can check all those possibilities and decrypt the program. In this program, `R` is the blinding factor. It is a private value, and when the program calculates (5-R) for example, it is blinding the 5. 

So, why does my circuit need 12 elements?
The zero is an un-blinding factor. We want the inputs of the program to potentially have already been blinded. 
So now we need to un-blind them to be able to use them in the next circuit.
In this example witness, the unblinding factor is zero, because the input variables are already unblinded.

It is important to apply the next blinding before removing the previous, so that the variable is not completely unblinded at any moment.

The R is there is blind the 5 and 7.

We calculate (5-R)*(7-R), because this calculation has the property that if we switch the 5 and 7 in it, it is the same thing. The final 2 values can be in either order, they just need to be able to multiply together to calculate the same (5-R)*(7-R) as the other pair.

We can apply this circuit to itself 256 times to select one value out of a list of 256.

An advantage of this circuit's design is that it is reversible.
These circuits can be tricky for taking a value out of one circuit and feeding it as intput to the next.
In order to reuse the circuit, it needs to be connected to the same basis point of the elliptic curve. So, the variable needs to be in the same location of the circuit.

This program is "reversible" in the sense that you can look at the first 2 and last 2 elements of the witness, and either pair can be the input or output of the program.
Swapping the 2 variables, and changing blinding factor, we can do these things in either order.
So this means when we are connecting the results of one circuit to inputs of the next circuit, we can always copy to the exact same position in the circuit, so we never need to change the basis points.