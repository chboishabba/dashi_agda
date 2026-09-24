module DASHI.Analysis.RiemannQuarticSignedPoleVerticalRvMHorizontalRecutExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

open import DASHI.Analysis.RiemannQuarticSignedPoleBidiMarkedFourthExact
open import DASHI.Analysis.RiemannG2NormalizedZeroMeasureStieltjesLeanDonorExact
open import DASHI.Analysis.RiemannG2NormalizedRvMAbelCompilerLeanDonorExact
open import DASHI.Analysis.RiemannG2RvMConstantDensityCancellationLeanDonorExact
open import DASHI.Analysis.RiemannG2NormalizedHorizontalCorrectionLeanDonorExact

------------------------------------------------------------------------
-- POST-BIDI RH LOCAL ANALYTIC RECUT
--
-- This owner supersedes the older interpretation in
--
--   RiemannQuarticSignedPoleBidiMarkedFourthExact
--
-- that treated a localized one-centre marked Montgomery producer as the
-- fundamental next theorem.
--
-- The live Lean branch now owns the stronger decomposition
--
--   A4_local
--     =
--   [ sum m_rho delta_rho^4 - integral delta^4 mu ]
--     +
--   [ sum m_rho a_rho^2 (a_rho^2 - 6 delta_rho^2) ].
--
-- The first bracket is an ordinary one-dimensional Riemann--von Mangoldt
-- discrepancy.  It no longer needs target/reflection pair-correlation
-- machinery.
--
-- Companion Lean owner:
--
--   Synthesis/
--   RiemannProjectiveQuarticFourWindowSignedPoleRvMFourth.lean
--
-- source-writes the exact Abel specialization for
--
--   phi_t(x) = (x-t)^4,
--   phi_t'(x) = 4 (x-t)^3,
--
-- on the literal symmetric zeta window (t-r,t+r], and compiles a uniform
-- cumulative discrepancy bound E into
--
--   |V4(t,r)| <= 9 r^4 E.
--
-- It then instantiates E from the already-proved arbitrary-endpoint literal
-- N-mu discrepancy theorem.
--
-- This is a source-written Lean theorem surface only.  No exact-head Lean
-- Actions/kernel receipt is claimed here, and the analytic donor modules
-- imported above remain donor/status owners rather than Agda-native proofs of
-- the analytic estimates.
--
-- The genuinely new local analytic obstruction is now H4:
--
--   H4 =
--   sum_local m_rho a_rho^2 (a_rho^2 - 6 delta_rho^2).
--
-- Its A-independence is important.  The target/reflection mark is an
-- algebraic reconstruction device, not the fundamental analytic variable
-- after the split.
--
-- Therefore the current min-cut is:
--
--   V4      ordinary RvM + Abel fourth-moment specialization
--   H4      signed off-line horizontal estimate
--   ABSORB  V4 + H4 + sixth/local remainder + FarExact < target margin
--
-- A localized marked Montgomery theorem remains a valid optional alternate
-- route, but it is no longer the required producer in the authoritative cut.
------------------------------------------------------------------------

data QuarticLocalAnalyticCoordinate : Set where
  exactVerticalHorizontalSplit : QuarticLocalAnalyticCoordinate
  verticalFourthWeightAbelSpecialization : QuarticLocalAnalyticCoordinate
  arbitraryEndpointRvMFeedsVerticalFourth : QuarticLocalAnalyticCoordinate
  verticalFourthNineR4ECompiler : QuarticLocalAnalyticCoordinate

  horizontalExactPolynomial :
    QuarticLocalAnalyticCoordinate
  horizontalSupportedOffCriticalLine :
    QuarticLocalAnalyticCoordinate
  horizontalSignedLocalQuantitativeEstimate :
    QuarticLocalAnalyticCoordinate

  finalVerticalHorizontalAbsorption :
    QuarticLocalAnalyticCoordinate

  localizedMarkedMontgomeryProducer :
    QuarticLocalAnalyticCoordinate

data QuarticLocalAnalyticStatus : Set where
  theoremOwned : QuarticLocalAnalyticStatus
  leanSourceWrittenNotKernelCertified : QuarticLocalAnalyticStatus
  openAnalyticObstruction : QuarticLocalAnalyticStatus
  optionalAlternateRoute : QuarticLocalAnalyticStatus

quarticLocalAnalyticStatus :
  QuarticLocalAnalyticCoordinate -> QuarticLocalAnalyticStatus
quarticLocalAnalyticStatus exactVerticalHorizontalSplit =
  theoremOwned
quarticLocalAnalyticStatus verticalFourthWeightAbelSpecialization =
  leanSourceWrittenNotKernelCertified
quarticLocalAnalyticStatus arbitraryEndpointRvMFeedsVerticalFourth =
  leanSourceWrittenNotKernelCertified
quarticLocalAnalyticStatus verticalFourthNineR4ECompiler =
  leanSourceWrittenNotKernelCertified

quarticLocalAnalyticStatus horizontalExactPolynomial =
  theoremOwned
quarticLocalAnalyticStatus horizontalSupportedOffCriticalLine =
  theoremOwned
quarticLocalAnalyticStatus horizontalSignedLocalQuantitativeEstimate =
  openAnalyticObstruction

quarticLocalAnalyticStatus finalVerticalHorizontalAbsorption =
  openAnalyticObstruction

quarticLocalAnalyticStatus localizedMarkedMontgomeryProducer =
  optionalAlternateRoute

record QuarticLocalAnalyticBoundary : Set where
  constructor quartic-local-analytic-boundary
  field
    exactVerticalHorizontalSplitPaid : Bool
    verticalFourthAbelSourceWritten : Bool
    arbitraryEndpointRvMProducerAvailable : Bool
    verticalFourthNineR4ECompilerSourceWritten : Bool

    horizontalExactPolynomialPaid : Bool
    horizontalOffLineSupportPaid : Bool
    horizontalSignedEstimatePaid : Bool

    finalAbsorptionPaid : Bool

    localizedMontgomeryStillFundamental : Bool

    exactVerticalHorizontalSplitPaidIsTrue :
      exactVerticalHorizontalSplitPaid ≡ true
    verticalFourthAbelSourceWrittenIsTrue :
      verticalFourthAbelSourceWritten ≡ true
    arbitraryEndpointRvMProducerAvailableIsTrue :
      arbitraryEndpointRvMProducerAvailable ≡ true
    verticalFourthNineR4ECompilerSourceWrittenIsTrue :
      verticalFourthNineR4ECompilerSourceWritten ≡ true

    horizontalExactPolynomialPaidIsTrue :
      horizontalExactPolynomialPaid ≡ true
    horizontalOffLineSupportPaidIsTrue :
      horizontalOffLineSupportPaid ≡ true
    horizontalSignedEstimatePaidIsFalse :
      horizontalSignedEstimatePaid ≡ false

    finalAbsorptionPaidIsFalse :
      finalAbsorptionPaid ≡ false

    localizedMontgomeryStillFundamentalIsFalse :
      localizedMontgomeryStillFundamental ≡ false

    leanBranch : String
    leanV4Path : String
    interpretation : String
    nextResearchCut : String

canonicalQuarticLocalAnalyticBoundary :
  QuarticLocalAnalyticBoundary
canonicalQuarticLocalAnalyticBoundary =
  quartic-local-analytic-boundary
    true
    true
    true
    true
    true
    true
    false
    false
    false
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    "agent/rh-marked-cluster-target-reflection"
    "Synthesis/RiemannProjectiveQuarticFourWindowSignedPoleRvMFourth.lean"
    "The marked 0/2/4 target-reflection interface remains an exact algebraic representation, but it is no longer the analytic min-cut.  The exact fourth-angular obstruction splits into an ordinary vertical zero-minus-mu fourth moment plus the A-independent off-line polynomial a^2(a^2-6*delta^2).  Existing literal RvM/Abel machinery now directly attacks the vertical term."
    "Treat V4 as a specialization/constant-optimization lane.  Attack H4 with signed local geometry before taking absolute values, reusing the existing cone/good/far and horizontal-strip machinery.  Then prove the final absorption inequality with SixthDebt and FarExact preserved.  A localized marked Montgomery theorem is optional fallback machinery, not a prerequisite."

verticalFourthIsNoLongerMontgomeryBlocked :
  quarticLocalAnalyticStatus verticalFourthWeightAbelSpecialization
    ≡ leanSourceWrittenNotKernelCertified
verticalFourthIsNoLongerMontgomeryBlocked = refl

horizontalFourthIsTheNewLocalAnalyticMinCut :
  quarticLocalAnalyticStatus horizontalSignedLocalQuantitativeEstimate
    ≡ openAnalyticObstruction
horizontalFourthIsTheNewLocalAnalyticMinCut = refl

localizedMontgomeryIsOptional :
  quarticLocalAnalyticStatus localizedMarkedMontgomeryProducer
    ≡ optionalAlternateRoute
localizedMontgomeryIsOptional = refl

finalAbsorptionRemainsOpen :
  quarticLocalAnalyticStatus finalVerticalHorizontalAbsorption
    ≡ openAnalyticObstruction
finalAbsorptionRemainsOpen = refl
