module DASHI.Physics.Closure.E6HyperformH3PhaseOrderParameterExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Physics.Closure.E6HyperformH3PhaseMetricLiftExact as Lift
import DASHI.Physics.Closure.E6HyperformH3ResidualReopeningMetricExact as Residual

------------------------------------------------------------------------
-- H3 PHASE LINE AS A NINE-STATE SYMMETRY-BREAKING ORDER PARAMETER
--
-- The full selected-H3 Weyl stabilizer has order 432 and induces a local
-- 72-element linear image.  The executable producer acts on the projective
-- covector line [ell] used to resolve the radical.
--
-- Results:
--   * the orbit of [ell] has size 9;
--   * it is exactly the set of all projective covector lines nonzero on the
--     H3 radical;
--   * the local line stabilizer has order 8;
--   * its full Weyl preimage has order 48;
--   * 432 / 48 = 9.
--
-- Therefore bare H3 quadratic geometry does not canonically select the added
-- phase direction. Choosing a radical-resolving line is genuine extra data and
-- breaks the selected H3 stabilizer from 432 to 48. This turns the previous
-- 'extra field required' boundary into an explicit finite order-parameter
-- space rather than an unspecified socket.
------------------------------------------------------------------------

selectedH3StabilizerOrder : Nat
selectedH3StabilizerOrder = 432

selectedH3LocalImageOrder : Nat
selectedH3LocalImageOrder = 72

radicalResolvingPhaseLineCount : Nat
radicalResolvingPhaseLineCount = 9

phaseLineStabilizerOrder : Nat
phaseLineStabilizerOrder = 48

localPhaseLineStabilizerOrder : Nat
localPhaseLineStabilizerOrder = 8

record H3PhaseOrderParameterLocalReceipt : Set where
  constructor h3-phase-order-parameter-local-receipt
  field
    fullE6WeylOrderChecked : Bool
    selectedH3StabilizerOrderChecked : Bool
    selectedH3LocalImageOrderChecked : Bool
    phaseLineOrbitHasNineStates : Bool
    phaseOrbitEqualsAllRadicalResolvingProjectiveCovectors : Bool
    phaseLineStabilizerOrder48Checked : Bool
    localPhaseLineStabilizerOrder8Checked : Bool
    orbitStabilizerNineChecked : Bool
    bareH3QuadraticGeometrySelectsUniquePhaseLine : Bool
    phaseLineIsAdditionalOrderParameter : Bool
    phaseChoiceBreaksH3Stabilizer : Bool
    phaseMetricLiftRemainsValidAfterChoice : Bool
    physicalDynamicalOrderParameterPaid : Bool
    globalFieldEquationPaid : Bool
    interpretation : String
open H3PhaseOrderParameterLocalReceipt public

canonicalH3PhaseOrderParameterLocalReceipt : H3PhaseOrderParameterLocalReceipt
canonicalH3PhaseOrderParameterLocalReceipt =
  h3-phase-order-parameter-local-receipt
    true true true true true true true true
    false true true true false false
    "There are exactly nine projective phase-covector lines capable of resolving the selected H3 radical, and the full H3 Weyl stabilizer acts transitively on them. Choosing one breaks the stabilizer from 432 to 48. The local nondegenerate phase-metric lift is therefore a symmetry-broken/order-parameter construction, not an invariant already selected by bare E6 H3 geometry. Dynamics, continuum field equations and physical order-parameter interpretation remain open."

phaseLiftReceipt : Lift.H3PhaseMetricLiftLocalReceipt
phaseLiftReceipt = Lift.canonicalH3PhaseMetricLiftLocalReceipt

residualReceipt : Residual.H3ResidualReopeningLocalReceipt
residualReceipt = Residual.canonicalH3ResidualReopeningLocalReceipt

record H3PhaseOrderParameterDynamics : Set₁ where
  field
    SpacetimeCarrier : Set
    PhaseLineState : Set
    phaseField : SpacetimeCarrier → PhaseLineState
    nineStateFibreReceipt : Set
    stabilizerBreakingReceipt : Set
    kineticOrConnectionTermReceipt : Set
    potentialOrSelectionLawReceipt : Set
    continuumLimitReceipt : Set
    empiricalCalibrationReceipt : Set
open H3PhaseOrderParameterDynamics public

data NineStateOrbitCreatesDynamics : Set where

data SymmetryBreakingCreatesPhysicalGravity : Set where

nineStateOrbitDoesNotCreateDynamics : NineStateOrbitCreatesDynamics → {A : Set} → A
nineStateOrbitDoesNotCreateDynamics ()

symmetryBreakingDoesNotCreateGravity : SymmetryBreakingCreatesPhysicalGravity → {A : Set} → A
symmetryBreakingDoesNotCreateGravity ()
