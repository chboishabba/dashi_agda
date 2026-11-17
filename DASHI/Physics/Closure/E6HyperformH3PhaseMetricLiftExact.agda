module DASHI.Physics.Closure.E6HyperformH3PhaseMetricLiftExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.Physics.Closure.E6HyperformTwoH3NondegenerateCandidateExact as H3Pair

------------------------------------------------------------------------
-- H3 LOCAL PHASE-QUOTIENT METRIC LIFT
--
-- The earlier no-go proves that another Weyl-transported copy of the same
-- degenerate H3 quadratic form cannot supply the missing third direction.
-- The additional datum used here is a nonzero linear phase covector
--
--   ell : H3_local -> F3
--
-- on the 27-state local H3 chart. Its kernel has 9 points, so it gives a
-- three-valued quotient coordinate. This quotient is NOT identified here with
-- the separate three-H3-patches-per-A2^3-class fibre; that requires a same-
-- object theorem and is explicitly left open.
--
-- The lifted local form is
--
--   G~ = G + ell^T ell.
--
-- On the selected plus chart ell+=(1,0,-1); on the actual Weyl-related minus
-- chart ell-=(2,0,0). The executable producer checks
--
--   ell- T = ell+
--   det(G~+) = det(G~-) = 1 mod 3
--   T^T G~- T = G~+.
--
-- The three-valued quotient coordinate may be relabelled by any affine
-- automorphism x |-> a*x+b of F3. Translation changes only the origin, while
-- inversion multiplies the differential covector by -1. Because (-1)^2=1,
-- ell^T ell is invariant. Thus no choice of orientation is needed for this
-- local metric term, without claiming that the quotient is the E8/zeta phase.
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
    localPhaseKernelHasNineStates : Bool
    localPhaseQuotientHasThreeStates : Bool
    phaseCovectorNonzeroOnRadical : Bool
    plusLiftDeterminantNonzero : Bool
    minusLiftDeterminantNonzero : Bool
    actualWeylTransitionTransportsCovector : Bool
    actualWeylTransitionTransportsLiftedMetric : Bool
    fullAffineThreeValueRelabellingChecked : Bool
    quotientTranslationLeavesDifferentialTermInvariant : Bool
    quotientInversionLeavesQuadraticTermInvariant : Bool
    canonicalC3OrientationRequiredForMetric : Bool
    radicalResolvingAdditionalStructurePaidLocally : Bool
    localQuotientEqualsThreeH3PatchFibrePaid : Bool
    globalPhaseBundleCocyclePaid : Bool
    e8ZetaSameActionIdentificationPaid : Bool
    physicalContinuumMetricPromotionPaid : Bool
    boundary : String
open H3PhaseMetricLiftLocalReceipt public

canonicalH3PhaseMetricLiftLocalReceipt : H3PhaseMetricLiftLocalReceipt
canonicalH3PhaseMetricLiftLocalReceipt =
  h3-phase-metric-lift-local-receipt
    true true true true true true true true true true true true
    false true false false false false
    "The selected H3 radical is resolved by an extra local phase-covector square rather than by another copy of the transported quadratic field. The 27-state chart maps to a three-valued quotient with nine-state kernel; its lifted metric is covariant under the paid Weyl transition and invariant under all affine relabellings of that quotient. This local quotient is not identified with the distinct three-H3-patch A2^3 fibre or the E8/zeta phase. Global bundle cocycles, those same-object identifications, and physical continuum promotion remain separate obligations."

record GlobalH3PhaseMetricBundle : Set₁ where
  field
    Chart : Set
    Transition : Chart → Chart → Set
    PhaseCovector : Chart → Set
    phaseTransitionReceipt : Set
    affineQuotientCocycleReceipt : Set
    liftedMetricTransitionReceipt : Set
    globalNondegenerateMetricReceipt : Set
open GlobalH3PhaseMetricBundle public

data LocalPhaseLiftCreatesGlobalBundle : Set where

data ThreeValuedQuotientCreatesH3PatchFibreIdentity : Set where

data ThreeValuedQuotientCreatesE8ZetaIdentity : Set where

localLiftDoesNotCreateGlobalBundle : LocalPhaseLiftCreatesGlobalBundle → {A : Set} → A
localLiftDoesNotCreateGlobalBundle ()

quotientDoesNotCreatePatchFibreIdentity :
  ThreeValuedQuotientCreatesH3PatchFibreIdentity → {A : Set} → A
quotientDoesNotCreatePatchFibreIdentity ()

quotientDoesNotCreateE8ZetaIdentity :
  ThreeValuedQuotientCreatesE8ZetaIdentity → {A : Set} → A
quotientDoesNotCreateE8ZetaIdentity ()
