# Wikidata/JMD ternary-native fibre and Boolean consumer boundary

This note records the theorem layer now materialized directly on PR #582.  It is not a claim that Boolean checkers are invalid.  It separates a Boolean **decision surface** from the signed/contextual carrier on which that decision is evaluated.

## 1. Native signed/neutral minimality

`DASHI.Foundations.TernaryNativeMinimalityExact` works on the repository's canonical SSP carrier

```text
{-1, 0, +1}
```

with strict antipode

```text
-1 <-> +1
 0  -> 0.
```

It proves by exhaustive finite cases that there is no injective map from all three states to one Boolean bit.

For the positive-only observer

```text
-1 -> false
 0 -> false
+1 -> true
```

the negative pole and the fixed centre collide, and no exact decoder from the bit back to the trit can exist.

The same module also proves the complementary fact: binary storage can simulate the full ternary geometry with two bits.  The explicit codec round-trips, preserves the strict antipode, and leaves one two-bit codeword outside the semantic image.  Hence the exact statement is:

```text
one bit: collapse;
extra structured binary state: lossless simulation.
```

This is about semantic geometry, not transistor technology.  Thomas M. Cover and Joy A. Thomas, *Elements of Information Theory*, second edition, Wiley (2006), DOI `10.1002/047174882X`, is recorded in the Agda header as coding/information-theory calibration; the finite proofs are local.

## 2. Strict inverse is not every kind of opposition

`DASHI.Algebra.BalancedTernaryOppositionEvidenceBridgeExact` connects the strict antipode to the existing operator-indexed evidence calculus as an **orientation reversal**.  It reuses existing DASHI theorems to block automatic promotion to either logical negation or algebraic inverse.

Thus the handoff keeps these distinct:

```text
not positively observed
strict geometric antipode
logical negation
algebraic inverse
contextual counterposition
```

The fixed centre is not the opposing pole.

## 3. Exact 27^3 carrier and variable-rank residual fibre

The carrier is not invented for this handoff.  `Base369InteractionAppraisalCubeExact` already has three semantically named 27-state blocks:

```text
interaction cube        27
appraisal A cube        27
appraisal B cube        27
--------------------------
one round            27^3 = 3^9 = 19683.
```

`BalancedTernaryAntipodalOrbitExact` proves for one block

```text
27 = 1 + 13*2
```

and constructs its 14 orientation-forgotten classes.  Applying the quotient independently to the three existing blocks gives

```text
27^3 = 19683
  ->
14^3 = 2744.
```

The coarse base stratifies by the number of noncentral blocks:

```text
2744 = 1 + 39 + 507 + 2197,
```

while the corresponding fine states are

```text
19683 = 1 + 78 + 2028 + 17576.
```

The residual orientation ranks are therefore

```text
1, 2, 4, 8.
```

This is a dependent residual fibre, not a uniform three-bit attachment.

Jean-Pierre Serre, *Linear Representations of Finite Groups*, Springer (1977), DOI `10.1007/978-1-4684-9458-7`, is attached to the antipodal-action module as representation/action calibration.

## 4. Quotient + residual is literally lossless

`BalancedTernaryAntipodalResidualCodecExact` closes the most important gap left by the earlier quotient arithmetic.

For one 27-state block it defines

```text
AntipodalCode27 =
  coarse antipodal class
  + residual whose type depends on that class.
```

The centre class carries a singleton residual.  Every noncentral class carries `direct | counter` orientation.  Both round-trip laws are proved:

```text
decode27 (encode27 x) = x
encode27 (decode27 c) = c.
```

The codec is then lifted to all three semantic blocks, again with both exact round-trip laws.  Therefore symmetry reduction itself is not information loss when the dependent residual is retained.  Discarding the residual is the information-losing operation.

## 5. Aggregate zero is not structural zero

`BalancedTernaryNineZeroFibreCountExact` computes the coefficient row of

```text
(x^-1 + 1 + x)^9
```

by literal repeated convolution.  The exact scalar-sum-zero fibre has

```text
3139
```

fine states, and the complete row sums to `19683`.

`Base369NineCoordinateAggregateBridgeExact` proves that the three semantic 27-state blocks and the flattened nine labelled trits are the same carrier presentation and that the existing aggregate is the nine-coordinate sum.

So

```text
aggregate = 0
```

cannot be read as

```text
all coordinates = 0.
```

## 6. Binary decisions remain legitimate consumer projections

`BinaryBalancedTernaryAggregateLossExact` reuses the existing 3/6/9/27 comparison geometry.  Two directed disagreements remain distinct after a declared per-coordinate binary decision but collapse under an accept-count aggregate:

```text
(1,0) != (0,1)
count(1,0) = count(0,1) = 1.
```

The theorem is not "Boolean is bad".  It is:

```text
a Boolean or scalar observer is sufficient exactly for the questions that factor through it;
it is not automatically an exact inverse of the fine carrier.
```

This is the same observer/factorisation discipline already used elsewhere in #582.

## 7. Five antipodal classes are not five D4 irrep species

`TernaryNineAntipodalD4SeparationExact` keeps a nearby numerical coincidence from being promoted into representation theory.  The 9-state antipodal plane has five orbit classes; the repository also names five D4 irrep species.  Equal cardinality does not identify them.  The module uses the stronger existing multiplicity witness to separate the raw nine-cell permutation representation from the j=4 restriction.

The Agda source records:

- Jean-Pierre Serre, *Linear Representations of Finite Groups*, DOI `10.1007/978-1-4684-9458-7`;
- William Fulton and Joe Harris, *Representation Theory: A First Course*, DOI `10.1007/978-1-4612-0979-9`.

## 8. Positive feature bundles versus dependent object construction

`DASHI.Ontology.DependentDefinitionFibreExact` formalizes the Ford/Fiesta-style issue as a finite dependent type.

A flat carrier first constructs

```text
Make x FlatModel
```

with 6 combinations.  Three are invalid and require a post-hoc Boolean validator.  The dependent carrier instead constructs

```text
Sigma (make : Make), Model make
```

with exactly the three valid values.  In particular the flat `Toyota x Fiesta` pair exists and is rejected after construction, whereas there is no dependent section having Toyota as make and Fiesta as model.

This does not prove that every ontology must use that exact hierarchy.  It proves the more precise point: when a child coordinate genuinely depends on a parent coordinate, a dependent/fibred representation can remove invalid Cartesian combinations from the carrier rather than discovering them only after a Boolean check.

The same module reuses `Base369SignedMembershipExact` to exhibit a contextual bundle which is retained globally while its local orientation is `tri-mid/zeroOpen`.  Thus local neutral/non-determinant status does not erase contextual relevance.

## Focused review

The new public regression is:

```text
DASHI/Ontology/WikidataTernaryFibreRegression.agda
```

and it is imported by:

```text
DASHI/Ontology/WikidataWorkingGroupEverything.agda
```

alongside the existing `WikidataWorkingGroupRegression`.

The important boundary remains: these are finite formal theorems about carriers, quotients, fibres, encodings and dependent construction.  They do not by themselves assert that every concrete Wikidata relation has the same active fibre, that every SSP has a particular representation-theoretic decomposition, or that a specific hardware ternary implementation outperforms binary hardware.
