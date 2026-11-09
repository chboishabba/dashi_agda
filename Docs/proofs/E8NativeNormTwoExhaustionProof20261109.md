# E8 norm-two exhaustion — exact mathematical classification

**Evidence level:** complete mathematical proof for the standard coordinate definition; **not yet** an Agda-checked theorem about the repository's selected original carrier.

## Carrier and normalization

Define
\[
L=\{x\in\mathbb Z^8:\sum_{i=1}^8x_i\in2\mathbb Z\}
\;\cup\;
\{x\in(\mathbb Z+\tfrac12)^8:\sum_{i=1}^8x_i\in2\mathbb Z\}.
\]
Let \(\|x\|^2=\sum_i x_i^2\). In doubled coordinates \(d_i=2x_i\), membership means all entries have the same parity and \(\sum_i d_i\equiv0\pmod4\); norm two is \(\sum_i d_i^2=8\).

## Theorem — exactly 240 norm-two vectors

Every \(x\in L\) of squared norm 2 belongs to precisely one family:

1. **Integral:** two nonzero coordinates, each \(\pm1\), remaining six zero. Their sum is always even. There are \(\binom82 2^2=112\).
2. **Half integral:** all eight coordinates equal \(\pm\tfrac12\), with an even number of negative signs. There are \(\sum_{k\text{ even}}\binom8k=2^7=128\).

These two families are disjoint. Their union is the entire norm-two shell, of cardinality **240**.

### Proof

For integral \(x\), every squared coordinate is a nonnegative integer. The only decomposition of 2 as a sum of integer squares is \(1+1\): an integer square cannot equal 2. Thus exactly two coordinates are \(\pm1\). All four sign patterns have even coordinate sum, so every selection of two positions is admitted.

For half-integral \(x\), each \(|x_i|\ge\tfrac12\); hence \(\sum_i x_i^2\ge8(\tfrac12)^2=2\). Equality forces all eight absolute values to be \(\tfrac12\). With \(k\) negative signs, the coordinate sum is \(4-k\), which is an even integer precisely when \(k\) is even. Flipping the sign of the first coordinate is a bijection between even- and odd-\(k\) sign strings; therefore exactly half of the \(2^8\) strings qualify. This yields 128. No third family exists by the all-integer/all-half-integer definition. QED.

**Important:** this theorem does not infer that 240 E8 roots equal a selected 240-subset of any independent 243-state triadic carrier. Nor does the norm-two shell determine all Fourier coefficients of \(\Theta_{E8}\).

## Exact original-Agda bridge obligations (proposed names)

- \`originalNativeE8MembershipIffDoubledParityAndSumModFour\`: independently selected E8 lattice membership iff the doubled-coordinate conditions.
- \`originalIntegerNormEightImpliesTwoUnitCoordinates\`: classification of all even doubled-coordinate vectors with squared norm 8 as two entries \(\pm2\), six zeros.
- \`originalHalfNormEightImpliesAllUnitCoordinates\`: classification of all odd doubled-coordinate vectors with squared norm 8 as eight entries \(\pm1\).
- \`originalHalfLatticeSumEvenIffEvenNegativeSigns\`: match half-integer membership to even number of negative signs.
- \`originalE8GeneratedRootsExhaustNativeNormTwoLattice\`: explicit two-way match between this shell and the original indexed 112+128 root generator, including no duplicates.
- \`originalE8NativeNormTwoRootsComplete\`: conclude exactly 240 for the independently selected source carrier.

These declarations are **not claimed to exist or to compile**. In particular, it would be incorrect to close P2e.04c at the repository/kernel level without the map to the original carrier.

## Connection to existing all-index Agda developments

\`AbelE8HalfOddShellInvolutionExact\` already defines a sign flip on arbitrary odd doubled-coordinate magnitudes and establishes its involutivity, norm preservation, parity flip, and coordinate-level two-sided transports for all shell indices. \`AbelE8ThetaParityProjectorExact\` supplies the all-index signed coefficient equation conditional on actual counts satisfying half-family parity cancellation. Neither theorem is merely an \(n\le8\) regression.

The unresolved chain is: original E8 shell equivalence → finite shell cardinality transport → identification with genuine Jacobi theta coefficients → Bishop analytic convergence and Jacobi/Eisenstein identity (or source-native modular uniqueness) → original \(\Theta_{E8}=E4\) → nonvanishing discriminant / same-source \(j\). No promotion to Agda-kernel completion is justified without exact-head Agda 2.9 \`--safe\` acceptance.
