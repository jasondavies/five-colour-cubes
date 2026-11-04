# Adding an opposite source to a butterfly failure

**Theorem.** Every pool obtained by adding one opposite-repeat cube to
a fourteen-cube butterfly failure has an assembly.

This is an elementary fifteen-cube result. It uses the already proved
butterfly classification and repeated-colour refinement, and does not
require a classification of failures having an own-loop triple.

Normalize the pivot to0 and the two blocks to P={1,2}, Q={3,4}.
The four high classes are

    C1=C(01), C2=C(02), C3=C(124), C4=C(123),

with three cubes in each. The low classes C(12), C(012) occur once.
By the elementary refinement theorem, all three cubes in each high
class have the same repeated colour; the four high repeats form a
derangement of {1,2,3,4}. Both low cubes repeat0.

The private-corner pairs of the high classes are

| Class | Private corners |
|---|---|
| C1 | 02,12 |
| C2 | 01,21 |
| C3 | 40,43 |
| C4 | 30,34 |

If the added opposite source meets one of these pairs, reserve two
same-repeat copies of that high class for its bicoloured corners. Its
third copy fills the other private corner, and the opposite source
fills the chosen private corner. The standard butterfly pools fill
the four remaining positions. For example, for C1, two C2 fill03,04,
while C3 and C4
fill13,14. The other high classes are symmetric.

It remains to consider an opposite source avoiding all eight private
corners. Because an opposite source is symmetric under arc reversal,
it must avoid every undirected edge in the two triangles012 and034.
The only remaining edges are the four between P and Q. Therefore
the unique avoiding opposite variety is O=opposite12|34, omitting0.

For this source assemble the opposite target02|13, omitting4:

    O:32;
    C2:01,21,23;
    C1:03,12;
    C4:10,30.

These are its eight distinct corner types. Hence every opposite source
completes the butterfly failure.

## Scope

For a hypothetical fifteen-cube failure with exactly one opposite
source, delete that source. If the fourteen adjacent cubes have no
own-loop triple, the pure private-column theorem places them in this
butterfly family, so the result above gives a contradiction.

The remaining exactly-one-opposite fifteen-cube branch must therefore
have a pure fourteen-cube predecessor with a unique own-loop triple.
That branch is not settled by this note.
