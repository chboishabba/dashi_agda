# UBP epistemic and Leech-lattice boundary

## Purpose

This tranche formalises the strongest mathematically defensible reading of the supplied UBP v5.4.1 checkpoint and repository assessment.

It does not reproduce UBP as a physical theory. It separates:

1. established Golay, Hexacode, MOG, Gray-map and Leech-lattice mathematics;
2. finite implementation checks;
3. quantities introduced by UBP;
4. internal consequences of those definitions;
5. empirical fits and future predictions;
6. physical or semantic interpretations;
7. the exact bridge obligations still missing.

The formalisation is fail-closed: importing these modules does not promote scientific, empirical, metaphysical, semantic, physical, theorem or external-verification authority.

## Repository attachment points

The tranche reuses existing DASHI boundaries rather than creating a parallel evidence system:

- `DASHI.Core.AuthorityNonPromotionCore` closes authority-bearing interpretations by default;
- `DASHI.Core.FibreRestrictionCore` records that evidence may restrict a fibre without recovering its carrier or promoting truth;
- `DASHI.Core.SourceProcessEvidenceCore` separates implementation traces and batch statistics from source-wide authority;
- `DASHI.Core.HiddenLiftProjectionCore` separates public projections from hidden-lift recovery;
- `DASHI.Core.OperatorShapeNonAuthorityCore` prevents operator-shaped vocabulary from creating theorem authority;
- `DASHI.Foundations.CarrierPromotionBoundaryCore` keeps carrier promotion explicit;
- `DASHI.Reasoning.MetaphorAlignmentMisunderstanding` requires declared invariant alignment before an analogy or translation can be treated as correct.

## Files

### `DASHI/Foundations/UBP/SourceAtlas.agda`

Records attributed mathematical sources with authors, exact titles, publication context and DOI state. Citation is provenance, not proof import.

### `DASHI/Foundations/UBP/ExactnessAndLatticeBoundary.agda`

Separates the irrational target

\[
Y=\frac{1}{\pi+2/\pi}
\]

from the exact rational model constant obtained from a finite rational convergent \(\pi_{50}\):

\[
Y_{50}=\frac{1}{\pi_{50}+2/\pi_{50}}\in\mathbb Q.
\]

The generic theorem proves that no rational embedding can equal a supplied irrational observer constant. The module also exposes a rational interval-certificate interface for rigorous lower and upper bounds.

For the stated integer Leech normalisation, it separates a single-bit address \(4e_i\) from lattice membership. The address has integer squared norm 16. Under a supplied rootlessness/minimum-norm witness excluding norm 16, the module proves that the address is not a Leech-lattice member. A genuine member requires explicit Golay-coset, parity and glue witnesses.

Closure under addition is available only after membership of both summands is supplied.

### `DASHI/Foundations/UBP/ObservableAlgebraBoundary.agda`

Retains the exact algebra which genuinely follows from the declared UBP observables.

For

\[
T_Y(s,n)=sY+\frac{n}{8},
\]

it proves the generic activation and de-excitation differences

\[
T_Y(s+1,n+k^2)-T_Y(s,n)=Y+\frac{k^2}{8},
\]

\[
T_Y(s-1,n-k^2)-T_Y(s,n)=-\left(Y+\frac{k^2}{8}\right).
\]

It instantiates the unit, Class A, Class B and Class C coordinate-square cases and proves the UBP long-cycle cancellation independently of the value of \(Y\):

\[
2\left(Y+\frac18\right)-2\left(Y+\frac48\right)=-\frac34.
\]

It also proves

\[
\operatorname{NRCI}(10)=\frac{10}{10+10}=\frac12.
\]

The associated status explicitly records that this is a normalization identity. It does not establish an independently emergent physical phase threshold.

Finally, `endpointTaxExtensional` proves that states with equal support and squared norm have equal endpoint TAX. Path-sensitive discrimination is therefore a separate observer property rather than a hidden dependency of the endpoint functional.

### `DASHI/Foundations/UBP/RepresentationAndObserverBoundary.agda`

Formalises four distinctions.

#### Shadow containment is not code equivalence

The reported `0/4096` Golay-to-Hexacode-shadow failures establish exhaustive containment for the selected implementation. They do not establish reverse characterisation. The formalisation records the cardinality seam:

\[
2^{18}=262144=64\cdot4096=64\cdot2^{12}.
\]

The remaining parity and tetrad conditions must be represented separately.

#### Systematic-coordinate observations are not invariant meanings

A syndrome weight such as 11 is a valid observation relative to a selected presentation. An intrinsic interpretation requires either a canonical coordinate labelling or a transport/equivariance theorem, such as an appropriate statement under the relevant Mathieu-group action.

#### Gray isometry is not semantic calibration

The Gray map may preserve Lee and Hamming distance. Semantic closeness additionally requires a concept carrier, a semantic metric, an encoding and a control theorem relating semantic distance to Lee distance.

#### A trajectory codec is not a Leech-to-3D projection

The module gives a concrete toy theorem: two trajectories can have the same endpoint and endpoint state cost while a path-sensitive observer distinguishes them. This establishes the logical possibility of endpoint-state/path-observer separation.

A genuine structural projection still requires a specified map plus compatibility or preservation laws for the relevant algebra, metric, adjacency or symmetry.

### `DASHI/Foundations/UBP/EvidenceInterpretationLedger.agda`

Introduces the eight-way claim ledger:

| Status | Meaning |
|---|---|
| `standardTheorem` | established external mathematics, locally attributed but not automatically imported |
| `implementationVerified` | code-level or finite-domain verification relative to an implementation/specification |
| `ubpDefinition` | a quantity or threshold introduced by UBP |
| `derivedInternalTheorem` | a consequence proved from UBP definitions |
| `empiricalFit` | retrospective comparison with observed data |
| `outOfSamplePrediction` | a future-facing claim requiring prior freezing and evaluation protocol |
| `interpretiveConjecture` | proposed physical or semantic meaning |
| `formalGap` | an explicitly unresolved bridge or theorem obligation |

Every canonical row is non-promoting.

The `InterpretationBridge` interface requires model state, observable, external target, interpretation and prediction maps, together with calibration, invariance, uncertainty, held-out-protocol and external-replication receipts.

### `DASHI/Foundations/UBP/Regression.agda`

Aggregates the tranche and checks that:

- seven attributed source entries are present;
- eight evidence rows are present;
- the `[24,18]` shadow-preimage cardinality is 64 times the `[24,12]` Golay cardinality;
- activation, long-cycle and NRCI normalization identities are exported through the aggregate;
- exact-Fraction-as-exact-irrational, ambient-address membership, independently emergent NRCI threshold, MOG-equivalence, intrinsic mass meaning, automatic semantic transport, genuine Leech-to-3D projection and external replication all remain closed;
- every focused receipt remains non-promoting.

## Source atlas

| Author(s) | Title | DOI state | Formal relationship |
|---|---|---|---|
| Marcel J. E. Golay | *Notes on Digital Coding* | no DOI recorded in this atlas | historical coding provenance |
| R. T. Curtis | *A new combinatorial approach to M24* | `10.1017/S0305004100052075` | MOG and Mathieu-group provenance |
| John Leech | *Notes on Sphere Packings* | `10.4153/CJM-1967-017-0` | historical Leech-lattice provenance |
| J. H. Conway and N. J. A. Sloane | *Sphere Packings, Lattices and Groups*, 3rd ed. | `10.1007/978-1-4757-6568-7` | standard lattice/code reference |
| A. R. Hammons, P. V. Kumar, A. R. Calderbank, N. J. A. Sloane and P. Solé | *The Z4-Linearity of Kerdock, Preparata, Goethals, and Related Codes* | `10.1109/18.312154` | Gray-map and Z4-code provenance |
| Marc Daumas, David Lester and César Muñoz | *Verified Real Number Calculations: A Library for Interval Arithmetic* | `10.1109/TC.2008.213` | rational interval-certification provenance |
| Henry Cohn, Abhinav Kumar, Stephen D. Miller, Danylo Radchenko and Maryna Viazovska | *The sphere packing problem in dimension 24* | `10.4007/annals.2017.185.3.8` | dimension-24 optimality provenance |

## What is proved here

The tranche proves generic logical boundaries and exact identities:

- rational images cannot equal a supplied irrational target;
- a supplied norm-16 exclusion prevents `4e_i` membership;
- lattice closure requires membership premises;
- activation and de-excitation differences follow exactly from the TAX definition;
- the long-cycle cancellation is exactly `-3/4` and independent of `Y`;
- `NRCI(10)=1/2` is a normalization identity;
- endpoint TAX is extensional in support and squared norm;
- `262144 = 64 * 4096`;
- endpoint state cost and path-sensitive observation can differ in discriminating power;
- all canonical UBP evidence and interpretation rows remain non-promoting.

These are real theorem advances over the supplied critique because the distinctions and surviving algebra are now typed and compositional rather than prose-only.

## Remaining frontier

The formal cut exposes the next genuine mathematical tasks.

1. Instantiate the observer-constant boundary on DASHI's constructive-real package and prove irrationality of the exact target.
2. Produce certified rational intervals for the exact target and transport TAX/NRCI inequalities through them.
3. Define a full Leech construction and membership decision surface with Golay, parity and glue proofs.
4. State and prove the exact MOG/Hexacode/Golay reverse-characterisation theorem intended by the implementation.
5. Determine which claimed coordinate observables are invariant, equivariant, gauge-fixed or merely presentation-specific.
6. Supply a semantic carrier and metric with a verified Gray-encoding distortion bound.
7. Define a genuine Leech-to-spatial-scene functor or representation and prove its compatibility laws.
8. Freeze empirical formulas, degrees of freedom, datasets, uncertainty and held-out protocols for any prediction lane.
9. Obtain independent implementation or experimental replication before promoting external verification.

## Validation

Focused static audit:

```text
python3 scripts/check_ubp_epistemic_lattice_boundary.py
```

Focused Agda aggregate:

```text
nix develop .# --command bash scripts/run_agda29_parallel_check.sh \
  DASHI/Foundations/UBP/Regression.agda
```

No repository-wide theorem or physical promotion follows from a successful focused check.
