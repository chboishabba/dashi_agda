# Symmetry-first 369 / balanced sheet / Pin / colour / rings cross-pollination (2026-10-22)

## Correct carrier vocabulary — do not use cardinality shorthand
- **3** = one ternary line (three compatible slots).
- **6** = two ternary lines with an explicit compatibility/gluing witness.
- **9** = 3×3 sheet, two balanced axes. Nine addresses; separately, a nine-*coordinate* ternary state has 3^9 values.
- **18** = two compatible 9-sheets, with interface/witness; not simply 18 scalar physical states.
- **27** = a ternary 3D cube (3×3×3) in the spatial chart; independently, a T27 graph-completion in PR #1133 describes 27 *coordinates* under a completion policy. Cardinality does not identify them.
- **12** is the *temporal sampling period* of the selected moving mark, not a 12-site sheet. Six samples then spatial mirror; the 3×3 site set never changes.

The central mathematical structure is a **diagram of geometries, gluing maps, phase symmetries, projections and observers**, not numerology, state-count identity or claim that response/opposite argument is the spatial antipode. Existing `ArgumentResponseNonGeometricOppositeBidiExact` explicitly separates response-space from geometric negation.

## New concrete chart -> Clifford generator cut
`DASHI/Geometry/C3ReflectionCliffordPinBridgeExact.agda` supplies:
- balanced chart involution `(row,column)->(row,-column)`;
- casewise commuting square with the exact nine-site `mirror`;
- selected generator `e1` in concrete `Cl(3,1)`, with `e1²=+1`, anti-commutation with `e0,e2,e3` inherited via exact theorem applications.

In an associative Clifford algebra, the Pin twisted adjoint of unit generator e1 is `rho_e1(v)=-e1*v*e1`. Algebraically this negates e1 and fixes other generators; its orthogonal image reflects the x axis and preserves the metric. This follows by generator anticommutation and associativity. **BUT** the canonical `ConcreteCl31Basis` owner explicitly leaves full multivector linear extension, associativity and universal-product adapter as an open boundary; therefore our Agda implementation proves the selected generator identities and chart commuting map, not a globally constructed typed Pin homomorphism on the full Clifford algebra. Do not silently promote it.

## Relation to 720-degree SU2 sign
Spatial mirror is det(-1), hence outside SO3 and Spin3~SU2. It has a Pin lift e1. An even product of two unit reflections represents a proper rotation and lies in Spin. An appropriate 120-degree proper rotation can be lifted to SU2 with cubic power -1 and sixth power +1, but constructing and identifying that rotation with the users' six-step mirrored **path** requires physical angular parametrization. Finite orbit and spinorial return are different actions with potential compatible covering structure, not automatically one action.

## Existing specific ring/complex/quaternion/octonion receipts
- `DASHI/Mathematics/Algebra/CayleyDicksonRationalComplexQuaternionExact.agda` is exact over ℚ: literal rational complex multiplication, conjugation and norm; explicit Cayley–Dickson equality to the source quaternion multiplication. It explicitly does not claim real Hurwitz classification/analytic completion.
- `DASHI/Mathematics/Algebra/CayleyDicksonRationalOctonionExact.agda` extends the rational algebra route.
- `DASHI/Algebra/Clifford/ConcreteCl31Basis.agda` supplies literal Cl(3,1) 16-blade generator calculus.
- `DASHI/Analysis/ConcreteComplex.agda`, `DASHI/Algebra/Clifford/UniversalProperty.agda`, Dirac/Spin/Fourier modules form further independent consumers.
- ℝ,ℂ,ℍ,𝕆 are **not a nested chain of associative field extensions**: ℍ is noncommutative and 𝕆 is nonassociative. Cayley–Dickson is the structural common route, not a proof that i generates all mathematics.

## 3+1 derivation status
`DASHI/Algebra/Quantum/LorentzSignatureUniqueness.agda` proves canonical sign assignment at **arbitrary selected spatial dimension d** given one timelike arrow and homogeneous spacelike axes. Thus uniqueness of signature *for a fixed d* is inhabited. It is not a proof that physical consistency forces d=3. `DASHI/Foundations/CausalOrderLorentzClosure.agda` has explicit 3+1 result contracts, but these are separate from a uniquely physically selected dimension.

## Strong colour sector: actual located receipts
- `DASHI/Physics/QFT/ColourFromNcThreeLanesReceipt.agda` and `ColourSU3FromCoprimeLanesReceipt.agda` identify a three-lane/S3 Weyl candidate with a specific obstruction: unequal carrier lane metric is not invariant under continuous SU3, so exact SU(3)_c and G_DHR~G_SM flags are false.
- `DASHI/Physics/QFT/BulkBoundarySU3Receipt.agda` records conditional SU3_1 Chern–Simons boundary / bulk interpretation; explicitly does not promote full physical SU3c.
- This is *real derivational prior art* and should be reused as the owner for colour, but it does not license saying colour gauge dynamics are already established.
- Classical 5D KK S1 fibre supplies U1. SU3 colour requires extra nonabelian realization, e.g. independent principal SU3 bundle and fields. Higher-dimensional compactification may produce SU3 under separately proved isometry/reduction hypotheses, not merely by adding ternary spatial z.

## Physics and semantic evidence boundaries
Formalising a ring action, finite Weyl symmetry, C3 phase, spinor lift, or Möbius reflection does not create same-object relations between charged physical particles, topological knots, or observer-relative argument negation. Require explicit realization and comparison maps, conserved quantities, dynamically generated trajectories and empirical discriminators.

## Compile commands (not observed)
```sh
agda -i . -i /path/to/agda-stdlib DASHI/Geometry/C3ReflectionCliffordPinBridgeExact.agda
```
No claimed exact-head kernel receipt.
