# Mathieu tower: sharp-transitivity boundary

The exact products are explained by a standard permutation-group theorem, not by a grid decomposition:

```text
|M11| = 11 falling 4 = 11 * 10 * 9 * 8 = 7920
|M12| = 12 falling 5 = 12 * 11 * 10 * 9 * 8 = 95040.
```

`M11` is sharply 4-transitive on 11 points. Fix an ordered 4-tuple of distinct points. Every ordered 4-tuple is its image under exactly one group element. Hence the group is in bijection with the `11 * 10 * 9 * 8` ordered distinct 4-tuples.

Likewise, sharp 5-transitivity of `M12` gives `12 * 11 * 10 * 9 * 8` directly.

The displayed stabilizer chain

```text
8 --x9--> 72 --x10--> 720 --x11--> 7920 --x12--> 95040
```

is the same falling-factorial count read through successive point stabilizers. In `M11`, after fixing three ordered points, eight images remain for the fourth point. That is the structural source of the factor `8`.

It is therefore incorrect to derive this factor from `|D4| = 8`, from a nine-cell grid, or from the number of irreducible `D4` channels. Those are different objects whose cardinalities happen to reuse some numerals.

The Agda module now contains:

- `fallingFactorial`;
- exact ordered-tuple counts for `(11,4)` and `(12,5)`;
- `SharpTransitivityOrderWitness`;
- the `M11` sharp-4 and `M12` sharp-5 order witnesses;
- the successive stabilizer-order chain;
- an explicit boundary theorem that the Mathieu factor `8` does not come from square-grid `D4` symmetry;
- an explicit boundary that divisor lattices are not required to derive either order.

The module stores the textbook sharp-transitivity theorem as source-bounded order data. It still does not manufacture the full permutation actions.

Primary sources:

- John H. Conway, Robert T. Curtis, Simon P. Norton, Richard A. Parker, and Robert A. Wilson, *Atlas of Finite Groups*, Oxford University Press, 1985. No DOI assigned.
- John D. Dixon and Brian Mortimer, *Permutation Groups*, Springer, 1996. DOI `10.1007/978-1-4612-0731-3`.
