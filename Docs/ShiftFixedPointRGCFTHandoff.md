# Shift fixed-point RG/CFT handoff

## Scope

This lane cross-pollinates the bounded shift dynamics, finite perturbation
classification, quadratic/MDL descent, finite operator algebra, and the
balanced-ternary continuous-depth interface.

The repo now contains two distinct layers:

```text
A. exact shift-native finite layer

fixed point
  -> three-state perturbation carrier
  -> Nat-indexed semigroup
  -> finite normed idempotent additive algebra
  -> 2,1,0 scaling rank
  -> finite OPE/fusion/crossing
  -> finite correlation and held Ward analogues

B. inhabited heterogeneous reference layer

complete GF(2) valued-field tangent
  -> exact zero-remainder derivative and discrete generator
  -> engineering/anomalous-dimension reference
  -> non-constant position-dependent finite OPE
  -> non-singleton injective stream-valued depth envelope
  -> exact tail/finite-step RG intertwining
  -> finite stress insertion and conformal-site Ward identities
```

Neither layer is promoted as a physical continuum CFT.

## Reused theorem surfaces

The implementation reuses rather than duplicates:

- `DashiDynamicsShiftInstance` for the exact shift step, held fixed point, and
  strict held-potential descent;
- `ShiftFixedPointPerturbationClassification` for the finite
  relevant/marginal/irrelevant classification;
- `ShiftPotentialQuadraticEnergy` and the collapse-depth/MDL receipt chain for
  the existing descent evidence;
- `ShiftFiniteTangentSemigroup`, `ShiftFiniteScalingFusionWard`,
  `ShiftFiniteNormedTangent`, and `ShiftFiniteLocalOPECrossing` for the exact
  finite algebra;
- `BalancedTernaryContinuousEnvelope` for the typed continuous-depth target.

## Exact finite shift layer

### Perturbation semigroup

The exact induced step is

```text
startPerturbation -> nextPerturbation -> zeroPerturbation -> zeroPerturbation
```

and its Nat-indexed iteration satisfies the semigroup composition law. Every
finite perturbation is absorbed at zero from time two onward.

### Additive/normed algebra

The existing fusion/join is an idempotent commutative additive monoid. The
existing `2,1,0` rank is a norm-like scalar with triangle inequality, and the
finite derivative preserves addition and is norm non-expansive.

This carrier is not a vector space because the idempotent addition has no
additive inverses.

### Finite OPE and crossing

The finite OPE coefficient is proof-relevant equality with the finite fusion
output. Exchange locality follows from commutativity and crossing follows from
associativity.

## Inhabited reference route

### Complete vector/Banach reference

`ShiftGF2BanachTangentReference.agda` supplies a one-dimensional vector model
over the finite complete valued field GF(2):

- additive inverses;
- scalar multiplication;
- distributivity and scalar associativity;
- a discrete norm and distance;
- norm separation and homogeneity;
- constructive completeness for the discrete eventual-constancy Cauchy
  presentation.

This is a mathematically legitimate finite non-Archimedean complete reference,
not an R- or C-valued physical tangent space.

### Fréchet derivative and generator reference

`ShiftGF2FrechetGeneratorReference.agda` uses the absorbing map `F(x)=0`.
Its derivative is the zero linear map and the Fréchet remainder vanishes
exactly. The Nat-indexed flow is identity at time zero and zero afterwards,
with an exact semigroup law and discrete generator equation.

This is not a real-time `C0` semigroup or sectorial analytic generator.

### Scaling and anomalous-dimension reference

`ShiftScalingDimensionReference.agda` retains the exact engineering spectrum

```text
start : 2
next  : 1
zero  : 0
```

and supplies zero anomalous correction. The finite RG transform obeys the
existing non-expansive eigen/order equation.

External physical normalization and measured anomalous-dimension authority
remain explicitly false.

### Position-dependent OPE

`ShiftPositionDependentOPEReference.agda` adds three explicit insertion
positions and the non-constant coefficient

```text
C(p,q;r;x,y)
  = positionWeight(x,y) * selection(fusion(p,q),r).
```

Coincident positions have weight `2`; separated positions have weight `1`.
Exchange locality follows from coefficient-kernel symmetry and fusion
commutativity. Channel crossing follows from fusion associativity.

This is genuine finite position dependence, but not a singular analytic OPE,
conformal-block expansion, or continuum locality theorem.

### Inhabited depth envelope and RG compatibility

`ShiftInhabitedDepthEnvelopeRG.agda` supplies a non-singleton stream-valued
instance of `ContinuousDepthEnvelope`:

- scalar carrier is the balanced-ternary stream carrier;
- embedding is identity and therefore injective;
- all-negative and all-positive streams give an explicit non-vacuity witness;
- coarse graining is stream tail;
- finite perturbations are encoded as depth-two, depth-one, and zero streams;
- tail exactly intertwines the finite derivative step pointwise;
- every encoded perturbation reaches the zero stream after two tail steps;
- the `2,1,0` scale rank is non-increasing across depth.

The analytic predicates in this reference model are symbolic proof tokens. This
inhabits the interface and closes exact combinatorial RG compatibility; it does
not establish real-number convergence or continuum universality.

### Stress tensor and Ward reference

`ShiftStressTensorConformalWardReference.agda` supplies:

- one finite stress insertion represented by the zero perturbation;
- exact finite divergence-free and trace-zero identities;
- explicit translation, dilation, and special-conformal permutations of the
  three insertion positions;
- invariant normalized correlation under those maps;
- compatibility with the position-dependent finite OPE.

The normalized correlation is identically zero. There is no nontrivial stress
correlator, central charge, anomaly calculation, or continuum tensor field.

## Integrated route

`ShiftAnalyticRGCFTRouteReference.agda` packages all inhabited references.
`ShiftFixedPointRGCFTHandoff.agda` records them as constructed and narrows the
remaining frontier to one unified physical continuum model.

## Remaining physical gates

The unresolved claims are now specific:

1. one R- or C-valued Banach tangent identified with the physical shift limit;
2. a real-time strongly continuous/analytic semigroup and generator estimates;
3. externally normalized measured physical and anomalous scaling dimensions;
4. singular analytic OPE coefficients, convergence regions, and conformal
   blocks;
5. a real/complex analytic instance of the continuous-depth envelope;
6. continuum RG universality and finite-to-continuum convergence across depth;
7. a nontrivial stress tensor, central charge/anomaly data, and physical
   conformal Ward identities.

No physical continuum RG fixed point, conformal symmetry, or CFT is promoted by
this work.
