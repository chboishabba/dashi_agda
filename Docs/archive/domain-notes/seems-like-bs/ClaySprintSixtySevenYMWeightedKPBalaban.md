# Clay Sprint Sixty Seven YM Weighted KP / Balaban Algebra

Sprint 67C keeps the Yang-Mills lane algebraic and fail-closed. The key
reframe is that the live obstruction is the entropy/incompatibility factor,
not the beta gap.

The current obstruction is:

```text
q = 0.23178189475262734
generic entropy eta = 8
8q = 1.8542551580210187 > 1
weighted KP requires eta q < 1
```

At current `q`, the entropy threshold is:

```text
1 / q = 4.31440083388422038
```

So the correct live target is:

```text
eta < 4.31440083388422038
```

The generic Holley-Stroock factor `eta = 8` fails. A spatial-only anisotropic
Balaban `L = 2` entropy count gives:

```text
eta_eff = 8 / 2 = 4
4q = 0.9271275790105094 < 1
margin = 0.07287242098949064
```

## Branches

The beta/k path is now secondary diagnostic context. The main route is:

```text
prove spatial-only anisotropic Balaban L=2 reduces eta from 8 to 4
while preserving:
  partition identity
  temporal transfer-matrix factorization
  small-field polymer bounds
  reflection positivity
```

Then the arithmetic already closes weighted KP conditionally:

```text
eta_eff q = 4q = 0.9271275790105094 < 1
```

## Eriksson Calibration

The Eriksson February 2026 lattice mass-gap series is recorded as a conditional
calibration target, not as a discharged DASHI theorem.  The useful map is:

```text
Balaban constructive RG
Holley-Stroock/orbit-Ricci spectral gap
transfer-matrix trace identity
```

The caveat aligns exactly with the DASHI open gate:

```text
Balaban partition identity
-> temporal transfer-matrix factorization
-> RG-invariant physical mass-gap scale
```

The missing compatibility is anisotropic: Balaban-style spatial coarsening must
remain compatible with the distinguished temporal direction needed by the
transfer matrix. This is now the load-bearing theorem target.

## Paper II Large-Field Status

Eriksson Paper II proves the large-field suppression hypothesis for isotropic
Balaban blocking.  DASHI may use that as a calibration target, but not as a
closed anisotropic theorem.

For spatial-only blocking, the following must be rechecked:

```text
spatial slab partition of unity
spatial slow-field identification modulo blockwise gauge transformations
temporal link factorization from spatial block integration
small-field bounds under anisotropic blocking
large-field suppression transfer to the spatial-only sigma algebra
```

The temporal factorisation lemma is first in dependency order:

```text
TemporalIntegralFactors:
  admissibility forbids any polymer from crossing
  both a spatial block boundary and a temporal link
  =>
  temporal and spatial functional integrals commute
```

This is where DASHI may add something not present in Eriksson: the carrier
support non-creation/admissibility rules might rule out the mixed
spatial-boundary-plus-temporal-link polymers.

## Supervoxel Face Geometry

The anisotropic partition problem is a face-level problem.

For `L = 3`:

| Object | Count |
| --- | ---: |
| spatial sites | `L^3 = 27` |
| plaquettes per spatial face | `L^2 = 9` |
| six spatial faces | `6 * 9 = 54` |
| plaquettes per temporal face | `L^3 = 27` |
| top plus bottom temporal faces | `2 * 27 = 54` |

So the anisotropic partition must split the temporal faces from the spatial
faces.  The sharpened first condition is:

```agda
TemporalFaceSupport :
  AdmissibleCarrier C ->
  (p : Polymer C) ->
  Not (InTopTemporalFace p And InBottomTemporalFace p)
```

If support non-creation and the kernel range prevent a polymer from occupying
both temporal faces of one spatial block, then temporal face integrals factor.

For `L = 2`, the same structure is smaller:

```text
spatial sites = 8
spatial face plaquettes = 4
temporal face plaquettes = 8
```

This is the concrete geometry behind the `TemporalIntegralFactors` gate.

## Beta 33/2 Calibration

The current blocked beta is near the natural SU(3) one-loop unit:

```text
N_c = 3
beta_bare = 2 N_c = 6
11 N_c / 2 = 33/2 = 16.5
beta_current ~= 16.7
```

The weighted KP threshold sits just above that plateau:

```text
beta_required - 33/2 = 2.7515829890895525
(beta_required - 33/2) / N_c = 0.9171943296965175
```

This is calibration only.  It says the current blocked coupling is structurally
meaningful; it does not close weighted KP or Balaban transfer.

## Entropy Threshold

The current entropy factor is `8`.  For the current activity,

```text
1 / q = 4.31440083388422038
4.31 * q = 0.9989799663838237
```

So the useful target is not merely "below 8"; it is:

```text
eta < 4.31440083388422038
```

The spatial-only `L=2` count gives `eta = 4.0`, which is safely below this
threshold.

## Anisotropic L Table

If spatial-only blocking gives `eta_eff = 8 / L`, then:

| L | eta_eff | eta_eff q | Status |
| ---: | ---: | ---: | --- |
| 1 | 8.0000 | 1.8542551580210187 | fail |
| 2 | 4.0000 | 0.9271275790105094 | pass |
| 3 | 2.6667 | 0.6180850526736729 | pass |
| 4 | 2.0000 | 0.4635637895052547 | pass |
| 5 | 1.6000 | 0.37085103160420375 | pass |
| 8 | 1.0000 | 0.23178189475262734 | pass |

`L = 2` is therefore the first and minimal anisotropic entropy closure.

## Beta / k Translation

Current diagnostic calibration:

```text
beta(k) = 6 + 0.1355488 k
k_required = 97.7624515236546
first safe integer target: k = 98
```

| k | beta(k) | q(beta) | 8q | Status |
| --- | ---: | ---: | ---: | --- |
| 67 | 15.0817696 | 0.3428896164570517 | 2.7431169316564135 | fail |
| 70 | 15.488416 | 0.3107535482480182 | 2.4860283859841457 | fail |
| 80 | 16.843904 | 0.22384907504811435 | 1.7907926003849148 | fail |
| 90 | 18.199392 | 0.16124806517061532 | 1.2899845213649226 | fail |
| 98 | 19.2837824 | 0.12402975293679427 | 0.9922380234943542 | pass |
| 100 | 19.55488 | 0.11615387964269382 | 0.9292310371415505 | pass |
| 120 | 22.265856 | 0.06027151889347521 | 0.48217215114780165 | strong pass |

So the clean diagnostic target is:

```text
k >= 98
```

under this one-loop beta-running law.

## Entropy Factor Table

At fixed `q_current = 0.23178189475262734`:

| entropy eta | eta q at beta=16.7 | beta needed | Status |
| ---: | ---: | ---: | --- |
| 8.0000 | 1.8542551580210187 | 19.251582989089552 | fail now |
| 7.0000 | 1.6224732632683914 | 18.699800374938636 | fail now |
| 6.0000 | 1.390691368515764 | 18.06281409466071 | fail now |
| 5.0000 | 1.1589094737631367 | 17.309419231875772 | fail now |
| 4.31440083388422038 | 1.0000 | 16.7 | boundary |
| 4.0000 | 0.9271275790105094 | already safe | pass |
| 3.0000 | 0.695345684257882 | already safe | pass |

This table now reads as follows:

```text
Running/beta closure is not the preferred route.
Entropy sharpening is the preferred route.
```

## Conditional Lemma Stack

The lemmas that can be inhabited now are conditional arithmetic/logic gates:

```agda
WeightedKPConverges :
  eta * q < 1 ->
  (forall d -> KPActivity d <= A * q ^ d) ->
  Summable (lambda d -> eta ^ d * KPActivity d)
```

```agda
AllDiameterKPFromRatio :
  KPActivity 0 <= A ->
  (forall d -> KPActivity (d + 1) <= q * KPActivity d) ->
  forall d -> KPActivity d <= A * q ^ d
```

```agda
EntropySharpeningClosesKP :
  q = 0.23178189475262734 ->
  eta < 4.31440083388422038 ->
  eta * q < 1
```

```agda
BetaThresholdClosesWeightedKP :
  beta >= 19.251582989089552 ->
  q beta <= 1 / 8 ->
  8 * q beta < 1
```

```agda
KScaleThresholdClosesWeightedKP :
  k >= 98 ->
  beta(k) = 6 + 0.1355488 k ->
  8 * q(beta(k)) < 1
```

```agda
AnisotropicL2EntropyClosesKP :
  q = 0.23178189475262734 ->
  etaEff = 4 ->
  etaEff * q < 1
```

The structural anisotropic lemma is the real gate:

```agda
TemporalIntegralFactors :
  AdmissibleCarrier C ->
  SpatialBlockBoundary B ->
  PolymerCrossesTemporalLink p -> Bottom ->
  TemporalIntegral (SpatialIntegral f) == SpatialIntegral (TemporalIntegral f)
```

```agda
SpatialOnlyCoarseningHalvesEntropyAtL2 :
  IsotropicBalabanEntropy L etaIso ->
  SpatialOnlyBalabanEntropy L etaSpatial ->
  L = 2 ->
  etaIso = 8 ->
  etaSpatial = etaIso / L
```

The constructive/analytic gates remain open:

```agda
AnisotropicBalabanPartitionIdentity
TemporalTransferMatrixCompatibleWithSpatialBlocking
SmallFieldBoundsSurviveAnisotropicBlocking
AnisotropicWeightedKPCertificate
LatticeMassGapFromAnisotropicKP
TransferSpectralGapImpliesLatticeMassGap
ContinuumMassGapTransfer
```

## Open Gates

```text
sharpened_entropy_bound_below_4_3144
holley_stroock_oscillation_tightening
temporal_integral_factorization
carrier_support_temporal_boundary_exclusion
spatial_slab_partition_of_unity
spatial_slow_field_identification
paper_II_large_field_suppression_transfer
spatial_only_coarsening_halves_entropy_at_L2
anisotropic_balaban_partition_identity
temporal_transfer_matrix_compatible_with_spatial_blocking
small_field_bounds_survive_anisotropic_blocking
anisotropic_weighted_kp_certificate
lattice_mass_gap_from_anisotropic_kp
balaban_bare_6_to_blocked_19_2516
activity_leakage_preservation
all_diameter_kp_certificate
continuum_rho_leakage
os_wightman_reconstruction
mass_gap_survival
```

## Governance

Sprint 67C records that weighted KP arithmetic is conditionally closed at
`eta_eff = 4`, but it does not prove anisotropic Balaban compatibility,
partition identity, temporal transfer-matrix compatibility, small-field bound
survival, all-diameter KP data, continuum reconstruction, mass gap, or Clay/YM
promotion.
