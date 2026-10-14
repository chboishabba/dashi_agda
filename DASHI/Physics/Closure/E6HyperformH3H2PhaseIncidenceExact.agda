module DASHI.Physics.Closure.E6HyperformH3H2PhaseIncidenceExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Physics.Closure.E6HyperformH3PhaseOrderParameterExact as Phase
import DASHI.Physics.Closure.E6HyperformH3ResidualReopeningMetricExact as Residual

------------------------------------------------------------------------
-- H3 PHASE LINE = INCIDENT H2 FACE
--
-- The earlier local phase construction selected a projective covector line
-- [ell] nonzero on the unique H3 radical.  Its kernel is therefore a 2-plane
-- complementary to that radical.
--
-- The exhaustive E6 finite-geometry producer now checks globally that these
-- complementary planes are EXACTLY the already-owned H2 incidence family:
--
--   120 H3 patches;
--   270 H2 patches;
--   9 incident H2 faces per H3;
--   4 incident H3 patches per H2;
--   1080 incidence flags in total.
--
-- For every H3 patch, its nine radical-complement 2-planes equal its nine H2
-- faces as literal projective subspaces.  Thus
--
--   [ell]  <->  ker ell = incident H2 face
--
-- is a same-object construction, not a cardinality match.
--
-- Moreover the H2 face determines the projective annihilator [ell] uniquely.
-- Since the only nonzero projective rescaling over F3 is ell -> -ell and
-- (-ell)^T(-ell)=ell^T ell, the lifted metric
--
--   G_tilde(H3,H2) = G_H3 + ell_H2^T ell_H2
--
-- is well-defined on the incidence flag without choosing a phase orientation.
--
-- The producer checks all 1080 metrics have determinant 1 mod 3 and all
-- 1080*6 = 6480 simple-reflection chart transitions obey
--
--   T^T G_tilde(g.H3,g.H2) T = G_tilde(H3,H2).
--
-- A selected H3 has stabilizer 432; a selected H3-H2 flag has stabilizer 48,
-- giving orbit size 9, independently matching the phase-line orbit.
------------------------------------------------------------------------

h3Count : Nat
h3Count = 120

h2Count : Nat
h2Count = 270

h3h2IncidenceCount : Nat
h3h2IncidenceCount = 1080

h2PerH3 : Nat
h2PerH3 = 9

h3PerH2 : Nat
h3PerH2 = 4

selectedH3StabilizerOrder : Nat
selectedH3StabilizerOrder = 432

selectedH3H2FlagStabilizerOrder : Nat
selectedH3H2FlagStabilizerOrder = 48

simpleReflectionTransitionChecks : Nat
simpleReflectionTransitionChecks = 6480

record H3H2PhaseIncidenceLocalReceipt : Set where
  constructor h3-h2-phase-incidence-local-receipt
  field
    all120H3PatchesEnumerated : Bool
    all270H2PatchesEnumerated : Bool
    all1080IncidenceFlagsEnumerated : Bool
    everyH3HasNineIncidentH2 : Bool
    everyH2HasFourIncidentH3 : Bool
    everyH3HasThirteenProjectiveTwoPlanes : Bool
    exactlyNineAvoidItsRadical : Bool
    radicalComplementPlanesEqualIncidentH2Exactly : Bool
    phaseLineKernelMapIsSameObjectBijection : Bool
    h2FaceDeterminesProjectivePhaseLineUniquely : Bool
    projectiveSignDropsOutOfOuterSquare : Bool
    all1080LiftedMetricsNondegenerate : Bool
    all1080LiftedMetricDeterminantsAreOne : Bool
    all6480SimpleReflectionTransitionsChecked : Bool
    decoratedMetricWeylCovariant : Bool
    selectedH3Stabilizer432Checked : Bool
    selectedFlagStabilizer48Checked : Bool
    orbitStabilizerNineChecked : Bool
    undecoratedH3MetricGloballyNondegenerate : Bool
    decoratedH3H2FiniteMetricDescentPaidLocally : Bool
    continuumLorentzMetricDerivedFromThisAlone : Bool
    physicalOrderParameterDynamicsPaid : Bool
    boundary : String
open H3H2PhaseIncidenceLocalReceipt public

canonicalH3H2PhaseIncidenceLocalReceipt : H3H2PhaseIncidenceLocalReceipt
canonicalH3H2PhaseIncidenceLocalReceipt =
  h3-h2-phase-incidence-local-receipt
    true true true true true true true true true true true true true true true
    true true true
    false true false false
    "The radical-resolving projective phase line is the annihilator of an already-owned incident H2 face. Exhaustive finite geometry proves this for every H3 patch and every incidence flag. The resulting H3-H2-decorated rank-three metric is nondegenerate and Weyl-covariant on all 6480 simple-reflection transitions. Bare H3 remains degenerate: selecting an H2 face is genuine symmetry-breaking/order-parameter data. This pays finite decorated metric descent, not continuum Lorentz dynamics, a physical selection law, or Einstein equations."

phaseOrderParameterReceipt : Phase.H3PhaseOrderParameterLocalReceipt
phaseOrderParameterReceipt = Phase.canonicalH3PhaseOrderParameterLocalReceipt

residualReopeningReceipt : Residual.H3ResidualReopeningLocalReceipt
residualReopeningReceipt = Residual.canonicalH3ResidualReopeningLocalReceipt

record DecoratedH3H2MetricAtlas : Set₁ where
  field
    H3 H2 : Set
    Incident : H3 → H2 → Set
    Metric : {h3 : H3} → {h2 : H2} → Incident h3 h2 → Set
    nondegenerateReceipt : Set
    WeylAction : Set
    incidenceEquivarianceReceipt : Set
    metricTransitionReceipt : Set
open DecoratedH3H2MetricAtlas public

data FiniteDecoratedMetricCreatesContinuumGR : Set where

data H2SelectionCreatesPhysicalOrderParameterDynamics : Set where

finiteMetricDoesNotCreateContinuumGR :
  FiniteDecoratedMetricCreatesContinuumGR → {A : Set} → A
finiteMetricDoesNotCreateContinuumGR ()

h2SelectionDoesNotCreateDynamics :
  H2SelectionCreatesPhysicalOrderParameterDynamics → {A : Set} → A
h2SelectionDoesNotCreateDynamics ()
