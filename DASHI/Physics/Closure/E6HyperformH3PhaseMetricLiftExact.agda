module DASHI.Physics.Closure.E6HyperformH3PhaseMetricLiftExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.Physics.Closure.E6HyperformTwoH3NondegenerateCandidateExact as H3Pair

------------------------------------------------------------------------
-- H3 PHASE-FIBRE METRIC LIFT
--
-- The earlier no-go proves that another Weyl-transported copy of the same
-- degenerate H3 quadratic form cannot supply the missing third direction.
-- The additional datum used here is a phase covector on the three-point H3
-- fibre.  Locally
--
--   G~ = G + ell^T ell.
--
-- On the selected plus chart ell+=(1,0,-1); on the actual Weyl-related minus
-- chart ell-=(2,0,0).  The executable producer checks
--
--   ell- T = ell+
--   det(G~+) = det(G~-) = 1 mod 3
--   T^T G~- T = G~+.
--
-- The three-point fibre has full affine symmetry Aff(1,F3)=S3.  Translation
-- changes only the phase origin, while inversion multiplies the differential
-- covector by -1.  Because (-1)^2=1, ell^T ell is orientation-independent.
-- Thus a canonical orientation of the C3 fibre is not required for the metric
-- term, even though identifying the fibre with the E8/zeta phase still requires
-- a same-action receipt.
------------------------------------------------------------------------

plusPhaseCovector : String
plusPhaseCovector = "ell_plus=(1,0,2) mod 3"

minusPhaseCovector : String
minusPhaseCovector = "ell_minus=(2,0,0) mod 3"

plusLiftedGram : String
plusLiftedGram = "Gtilde_plus=diag(2,1,2) mod 3"

weylLiftIdentity : String
weylLiftIdentity = "T^T Gtilde_minus T = Gtilde_plus"

record H3PhaseMetricLiftLocalReceipt : Set where
  constructor h3-phase-metric-lift-local-receipt
  field
    transportedQuadraticAloneStillDegenerate : Bool
    additionalPhaseCovectorUsed : Bool
    phaseCovectorNonzeroOnRadical : Bool
    plusLiftDeterminantNonzero : Bool
    minusLiftDeterminantNonzero : Bool
    actualWeylTransitionTransportsCovector : Bool
    actualWeylTransitionTransportsLiftedMetric : Bool
    fullAffineThreePointFibreSymmetryChecked : Bool
    fibreTranslationLeavesDifferentialTermInvariant : Bool
    fibreInversionLeavesQuadraticTermInvariant : Bool
    canonicalC3OrientationRequiredForMetric : Bool
    radicalResolvingAdditionalStructurePaidLocally : Bool
    globalPhaseBundleCocyclePaid : Bool
    e8ZetaSameActionIdentificationPaid : Bool
    physicalContinuumMetricPromotionPaid : Bool
    boundary : String
open H3PhaseMetricLiftLocalReceipt public

canonicalH3PhaseMetricLiftLocalReceipt : H3PhaseMetricLiftLocalReceipt
canonicalH3PhaseMetricLiftLocalReceipt =
  h3-phase-metric-lift-local-receipt
    true true true true true true true true true true
    false true false false false
    "The selected H3 radical is resolved by an extra phase-covector square rather than by another copy of the transported quadratic field. The lift is covariant under the paid Weyl chart transition and invariant under orientation reversal of the three-point fibre, so lack of a canonical C3 orientation is not an obstruction to the local metric term. A global fibre-bundle cocycle and same-action identification with the E8/zeta phase remain separate obligations before physical continuum promotion."

record GlobalH3PhaseMetricBundle : Set₁ where
  field
    Chart : Set
    Transition : Chart → Chart → Set
    PhaseCovector : Chart → Set
    phaseTransitionReceipt : Set
    affineFibreCocycleReceipt : Set
    liftedMetricTransitionReceipt : Set
    globalNondegenerateMetricReceipt : Set
open GlobalH3PhaseMetricBundle public

data LocalPhaseLiftCreatesGlobalBundle : Set where

data AffineThreePointFibreCreatesE8ZetaIdentity : Set where

localLiftDoesNotCreateGlobalBundle : LocalPhaseLiftCreatesGlobalBundle → {A : Set} → A
localLiftDoesNotCreateGlobalBundle ()

fibreDoesNotCreateE8ZetaIdentity : AffineThreePointFibreCreatesE8ZetaIdentity → {A : Set} → A
fibreDoesNotCreateE8ZetaIdentity ()
