# SSP15 modular character and coarse-fine projection — Round 5

## Purpose

This tranche integrates the supplied modular, coarse/fine, character, and
relational notes into the existing SSP15 stack without promoting numerical
coincidences into Monster representation theorems.

The implementation has six exact cores:

1. the corrected Monster prime-exponent function and the Duncan--Swisher
   modular contribution split for every prime above three;
2. an exact rational ten-sector common-mode/fine-residual projection;
3. the actual nine-cell D4 orbit quotient with a lossless residual codec;
4. the C3 representation-ring evaluation yielding dimension `196883`, 3B
   trace `53`, and weight-two trace `54` from one balanced character;
5. type-safe separation of block multiplicity, representation dimension, and
   whole-space share ratios;
6. the exact relational cardinality ladder and pointed phase expansion
   `729 = (8 * 10 + 1) * 9 = 8 * 90 + 9`.

## Corrected Monster exponent authority

`MonsterOrderExponentCorrectionExact.agda` installs

```text
p:     2  3  5  7  11 13 17 19 23 29 31 41 47 59 71
v_p:  46 20  9  6   2  3  1  1  1  1  1  1  1  1  1
```

and records the exact Duncan--Swisher Theorem 1.1 contributions:

```text
p=5  : 3 + 5 + 1 = 9
p=7  : 2 + 4 + 0 = 6
p=11 : 2 + 0 + 0 = 2
p=13 : 1 + 2 + 0 = 3
p>=17: 1 + 0 + 0 = 1
```

The paper's right-hand side gives `36` at `p=2` and `18` at `p=3`, while the
Monster exponents are `46` and `20`; those exceptional gaps are represented
rather than hidden.

The module also regression-tests two older repository receipts. They record
`2` at `p=13,17,19,23`; the new authority proves those values disagree with
the exact Monster order. The old modules are retained for dependency stability
but are no longer authoritative.

## Ten-sector coarse/fine projection

`CoarseFineTenSectorProjectionExact.agda` uses the existing
`DecimalCompletionState = {0,...,8,j}` carrier and constructs a rational field
with ten coordinates.

```text
B(x) = (x,...,x)
A(phi) = (1/10) sum_i phi_i
P_coarse = B A
P_fine = I - B A
```

The module proves `A(B(x)) = x`, projection idempotence, exact reconstruction,
zero residual sum, common/residual orthogonality, squared-norm splitting, and
a nine-coordinate parametrization of the zero-sum residual space.

Thus `1/10` is the normalized averaging coefficient and `10 = 1 + 9` is one
common mode plus nine relative degrees. This is finite linear algebra, not a
claim that there are ten independent modular `j`-invariants.

## Typed ratio correction

`C3CoarseFineRatioTypingExact.agda` makes the conceptual correction explicit.
The following are different typed quantities:

```text
macro block multiplicity     = 10 / 1
regular copy multiplicity    = 65610 / 1
fine/coarse dimension ratio  = 196830 / 53
coarse share of whole        = 53 / 196883
fine share of whole          = 196830 / 196883
```

The hierarchy is

```text
10 macro blocks
* 3^8 regular copies per macro block
= 65610 regular C3 copies
* 3 dimensions per regular copy
= 196830 fine dimensions.
```

The module separately types augmentation and nonidentity character evaluation.
At the identity the fine contribution is `196830`; at a nonidentity generator
it is exactly `0`, leaving `53`. Character cancellation is not represented as
ten-sector averaging, and neither operation derives the coefficient ten.

## D4 nine-cell compression

`D4NineCellOrbitCompressionExact.agda` constructs the centre, four edge cells,
and four corner cells. Rotation and reflection preserve

```text
9 = 1 centre + 4 edges + 4 corners.
```

A dependent quotient-plus-residual code is lossless in both directions. The
module separately imports the five D4 irreducible labels and the existing
permutation decomposition

```text
R^9 = 3 A1 + B1 + B2 + 2 E,
```

with `A2` absent. It explicitly blocks the unsupported inference that the five
irrep types explain `v_5(|M|)=9`.

## C3 character evaluation

`Monster3BC3RepresentationRingEvaluationExact.agda` represents

```text
[W] = 53 * 1 + (10 * 3^8) * (1 + x + x^2)
```

as a balanced C3 character. The common regular multiplicity is `65610`, so

```text
m_1       = 65663
m_zeta    = 65610
m_zeta^2  = 65610.
```

The two evaluations give

```text
dim W       = 196883
chi_W(3B)   = 53
dim V_2^#   = 196884
Tr(3B|V_2#) = 54.
```

The coefficient ten remains an input multiplicity. The representation-ring
packaging explains why dimension and trace are two evaluations of one object;
it does not derive ten or construct the actual Monster restriction.

## Relational appraisal and pointed phase expansion

`RelationalAppraisalPointedPhaseExact.agda` formalizes the exact ternary axis
ladder:

```text
3 axes  : initial A-B-outcome event       -> 3^3  = 27
6 axes  : bilateral appraisal fibre       -> 3^6  = 729
9 axes  : event plus both appraisal cubes -> 3^9  = 19683
12 axes : synthesis re-entered             -> 3^12 = 531441.
```

It proves

```text
3^9 = 3^3 * 3^6 = 27 * 729 = 27^3,
729 = 27 * 27.
```

The pointed phase constructor has general cardinality

```text
PointedPhaseExpand(n,m,k) = (n*m + 1)*k.
```

For `n=8`, `m=10`, and `k=9`, it proves

```text
729 = (8*10 + 1)*9
    = 8*(10*9) + 9
    = 10*(8*9) + 9.
```

It also proves the recursive arithmetic

```text
90 = 10*9
65610 = 90*729
      = (10*9)*(8*(10*9)+9).
```

These are exact finite cardinality constructions. The module explicitly marks
as unproved that this partition is canonical for every six-trit fibre, derives
ten, constructs a Monster module, or identifies the twelve relational axes
with the Monster's twelve-dimensional symplectic quotient. `3^(1+12)` is
retained only as a group-order pattern.

## Modular `j` / Fricke interface

`ModularCurveJFrickeInterfaceExact.agda` types a point of `X_0(N)` abstractly
as a fine point with source and target elliptic curves. It proves that Fricke
reversal swaps the two coarse `j`-values, and therefore every symmetric
observation of the pair is Fricke invariant. A genus-zero coordinate is kept
as a proof-bearing interface rather than postulated or fabricated.

The finite SSP address fibration is reused only as an internal model. It is
not identified with a literal modular curve or Hauptmodul.

## Sources

- John F. R. Duncan and Holly Swisher, *Modular Functions and the Monstrous
  Exponents*, arXiv:2602.09135, DOI `10.48550/arXiv.2602.09135`.
- Nicholas M. Katz and Barry Mazur, *Arithmetic Moduli of Elliptic Curves*,
  DOI `10.1515/9781400881710`.
- Andrew P. Ogg, *Automorphismes de courbes modulaires*, Séminaire
  Delange--Pisot--Poitou 1974/75, no DOI assigned.
- John F. R. Duncan and Ken Ono, *The Jack Daniels Problem*,
  DOI `10.1016/j.jnt.2015.06.001`.
- Jean-Pierre Serre, *Linear Representations of Finite Groups*,
  DOI `10.1007/978-1-4684-9458-7`.
- John H. Conway and Simon P. Norton, *Monstrous Moonshine*,
  DOI `10.1112/blms/11.3.308`.
- Thomas M. Cover and Joy A. Thomas, *Elements of Information Theory*,
  DOI `10.1002/047174882X`.
- Roger A. Horn and Charles R. Johnson, *Matrix Analysis*,
  DOI `10.1017/CBO9781139020411`.
- Fan R. K. Chung, *Spectral Graph Theory*, DOI `10.1090/cbms/092`.

## Validation

```bash
bash scripts/check_ssp15_modular_character_projection_round5.sh
```

The checker chains the complete Round-4 validation, rejects holes, postulates,
and trust escapes, checks all ratio and pointed-phase boundaries, emits a
substance audit, and invokes pinned Agda 2.9 on the validation and aggregate
roots.
