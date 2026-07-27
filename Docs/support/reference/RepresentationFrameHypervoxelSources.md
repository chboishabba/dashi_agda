# Representation/frame/hypervoxel provenance ledger

## Purpose

This ledger records sources and precedents named in the representation,
radix, SU(2)/SO(3), logistic, primorial and situated-frame intake.  It is not a
claim that every interpretive use in DASHI is stated or endorsed by the cited
source.  The repository distinguishes:

1. source content;
2. cross-source synthesis;
3. DASHI formal extension;
4. empirical hypothesis;
5. interpretive analogy.

## Lie groups and exponential coordinates

### Rodrigues and SU(2)/SO(3) background

- Jean Gallier and Jocelyn Quaintance, *Notes on Differential Geometry and Lie
  Groups*, chapter material on rotations and the exponential map:
  <https://www.cis.upenn.edu/~cis6100/geombchap14.pdf>

The intake uses the standard axis-angle/quaternion presentation

```text
q(theta,v) = (cos(theta/2), sin(theta/2) v)
```

and the two-to-one projection from unit quaternions/SU(2) to SO(3).  DASHI's
new finite `Axis x LiftPolarity` carrier is an indexing adapter for this shape;
it is not asserted by the source to be `HexTruth`.

### Left/right SO(3) Jacobian conventions

- Math StackExchange discussion of left/right SO(3) Jacobian identities:
  <https://math.stackexchange.com/questions/4957440/how-do-i-prove-these-left-and-right-jacobian-properties-of-so3>
- Timothy D. Barfoot, *State Estimation for Robotics* identity reference:
  <http://asrl.utias.utoronto.ca/~tdb/bib/barfoot_ser17_identities.pdf>

The convention locked by the new receipt is

```text
J_r(theta)
  = I
  - (1 - cos r)/r^2 [theta]_x
  + (r - sin r)/r^3 [theta]_x^2.
```

The receipt fixes sign and denominator powers.  It is not itself a kernel proof
of the analytic formula or of the downstream operator bound.

### Haar density

The intake uses the SU(2) exponential-coordinate density

```text
(sin(r/2)/(r/2))^2
```

under the stated generator/radius convention.  Because normalisations of the
Lie-algebra norm differ, downstream analytic use must retain the convention
receipt rather than copying only the displayed scalar expression.

## p-adic and ultrametric reading

- General p-adic background named in the intake:
  <https://arxiv.org/abs/1710.08835>

DASHI's finite prefix metric is proved in the existing
`DASHI.Geometry.SSP369Ultrametric`.  The new bridge interprets the prefix as
starting from a selected radix/valuation origin.  It does not promote the
finite address carrier into an analytic p-adic completion.

## Primorial-base sequences

- OEIS A276086, primorial-base exp-function:
  <https://oeis.org/A276086>
- OEIS A276087, second iterate of A276086:
  <https://oeis.org/A276087>

The existing module `DASHI.Foundations.PrimorialBaseSequences` tabulates the
finite values and defines

```text
A276087(n) = A276086(A276086(n)).
```

The new situated-frame module imports that implementation and proves the
second-iterate identity definitionally.  Neither OEIS sequence by itself proves
systemic rebirth, logistic branching, cognition, or manifold reconstruction.
Those are separate optional interpretation maps.

## Logistic map

- Introductory logistic-map reference named in the intake:
  <https://math.osu.edu/sites/math.osu.edu/files/Logistic_Model.pdf>

The formal intake keeps distinct:

- `x = 1/2`, the critical state coordinate of the logistic parabola;
- `r = 3`, the first period-doubling parameter;
- the period-doubling accumulation parameter near `3.5699456`;
- period-three chaos results;
- a DASHI phase projection used diagnostically.

The numeral `3` occurring in a dynamical theorem does not prove a universal
3/6/9 dialectic.  The existing `TlureyPhase` mapping remains a selected
interpretive diagnostic.

## Situated knowledge and critical distance

The intake names the following philosophical precedents:

- Georg Lukacs and later standpoint traditions;
- Patricia Hill Collins and Black feminist standpoint epistemology;
- Michel Foucault's subjugated knowledges and eventalisation;
- Tyson Yunkaporta's pattern-thinking/pattern-mind work;
- Marxian/materialist attention to production and feedback structures;
- Lacanian and Zizekian symptom/ideology readings.

The Agda module records these as `InterpretivePrecedent` values with
`formalEquivalenceClaimed = false`.  It does not derive their philosophical
claims, diagnose a person, or establish that distress has one universal cause.

## Harmonic and manifold analogy

The exact arithmetic statement is simply

```text
3/6 = 1/2 = 0.5 = 0.1 base 2 = 50%.
```

The harmonic reading of `3:6` as `1:2` applies when the terms are frequency or
period ratios.  The manifold/chart analogy applies to multiple lawful
presentations of one invariant.  Neither role is inherent in the glyphs `3`
and `6`; both are selected contexts carried by typed evidence.

## Repository extension

The following are DASHI constructions rather than claims copied from the
sources above:

- `PresentationFibre` and `FramedAtlas`;
- rank/depth-separated recursive ternary hypervoxels;
- address, sibling and common-interface join types;
- the distinction between spatial refinement and configuration-space
  exponentiation;
- `Axis x LiftPolarity <-> HexTruth` as a finite adapter;
- `Axis x Axis <-> NonaryTruth` as a matrix-slot adapter;
- the Stage-1/Stage-10 same-unit-role witness and Stage-11 carry join;
- plural situated-explanation and authority-boundary records.

These extensions are assessed by Agda typechecking and repository boundary
receipts, not by attributing them to the external references.
