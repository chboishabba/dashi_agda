# DuPont–DASHI arithmetic-geometry bridge

## Scope

This theorem family records the precise relationship between the DuPont-facing arithmetic surface (genus, finite prime windows, local-global reasoning, Monster-prime coordinates) and the broader DASHI architecture.

The result is deliberately asymmetric:

- DASHI supplies the general **lens → search → obstruction → invariant lift** architecture.
- DuPont-style arithmetic geometry supplies the domain-specific content needed to decide rational-point questions: Hasse closure in genus zero, and descent/Selmer/Cassels–Tate data in genus one.
- Therefore DASHI is only a mathematical superset after those arithmetic structures are instantiated. Architecture alone is not promoted to containment.

## Experimental findings recorded

The Python experiments motivating the formal boundary found:

1. **Genus zero:** sampled conics behaved consistently with local-global closure. This supports the genus-zero lens interpretation but does not replace Hasse–Minkowski.
2. **Genus-one elliptic curves:** local residue sieves pruned bounded rational search substantially, often reducing surviving candidates to a small fraction of the original grid.
3. **Genus-one torsors:** Selmer's diagonal cubic exhibited the expected locally-soluble / globally-unresolved-by-search pattern. Persistent bounded-search failure is explicitly not a proof of insolubility.
4. **Cube-density lenses:** cube-coset density at primes congruent to 1 modulo 3 showed a weak signal for bounded search difficulty. It did not certify a Tate–Shafarevich obstruction.
5. **Height:** chain depth and antichain width remain DASHI structural height coordinates. They have not yet been validated against canonical elliptic-curve height, so the formalization requires comparison bounds rather than identifying the two notions.

## Formal modules

### `DASHI.ArithmeticGeometry.ChainAntichainHeight`

Defines:

- `OrderProfile` with `chainDepth` and `antichainWidth`;
- a weighted `structuralHeight`;
- `ArithmeticHeightValidation`, requiring lower and upper comparison bounds against an externally supplied canonical height;
- `FiniteHeightFibre`, preventing a finite proxy height from being mistaken for finite arithmetic search without a coverage witness;
- `HeightLiftPolicy`, recording the point at which search depth should stop increasing and stronger invariants should be invoked.

### `DASHI.ArithmeticGeometry.LocalGlobalObstruction`

Defines:

- an abstract local-global problem;
- an `H1Class` obstruction interface;
- a Selmer layer separating locally admissible, Mordell–Weil-image, and Sha-candidate classes;
- a Cassels–Tate-style pairing certificate interface;
- a three-way decision: global witness, certified obstruction, or invariant lift required;
- bounded-search receipts that cannot be promoted to obstruction certificates.

### `DASHI.ArithmeticGeometry.DupontDASHIBridge`

Defines:

- genus and finite prime-window lenses;
- genus-zero closure through an explicit Hasse bridge;
- genus-one closure through a sound obstruction classifier;
- `DASHISubsumesDupont`, which requires the arithmetic closures as fields rather than claiming them from the generic architecture;
- an experiment receipt with open gates for Sha certification and chain/antichain-to-canonical-height validation.

## Next mathematical bridges

The next non-receipt work should instantiate the interfaces for diagonal cubic 3-coverings:

1. define the Jacobian map for `A x³ + B y³ + C z³ = 0`;
2. define the covering class in an abstract 3-Selmer carrier;
3. import a certified external 3-descent result through a conformance boundary;
4. define the Cassels–Tate pairing receipt and prove that a nonzero pairing prevents promotion to the Mordell–Weil image;
5. encode rational points and test chain/antichain structural height against canonical height bounds.

This replaces unbounded coordinate search with invariant depth: local scan → 3-descent → Selmer classification → pairing certificate.
