module DASHI.Physics.Closure.NSTriadKNDirectResolventPairCompanionRound496Exact where

------------------------------------------------------------------------
-- ROUND496 / DIRECT NONSEPARABLE RESOLVENT PAIR COMPANION
--
-- The shortest R423 route does not need a Laplace/heat factorization.  R380,
-- R388, R389 and R384 already give the literal physical unordered pair with:
--
--   * exact double-mixed cells D_alpha, D_beta;
--   * exact product-rule forcings G_alpha, G_beta;
--   * exact positive pair rate lambda_alpha + lambda_beta;
--   * exact rational resolvent w = 1 / (lambda_alpha + lambda_beta).
--
-- R291's nonlinear Gram remainder is
--
--   2 ( Re<G_alpha,D_beta> + Re<D_alpha,G_beta> ).
--
-- Define the normalized direct companion contribution by
--
--   C_{alpha,beta}
--     = (1/2) w
--         ( Re<G_alpha,D_beta> + Re<D_alpha,G_beta> ).
--
-- Then the literal R290 weighted nonlinear remainder is EXACTLY 4*C.  This is
-- finite rational algebra on the nonseparable Cauchy-resolvent carrier; no
-- exponential, improper integral, sign estimate, or operator majorant is used.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base as ℚ using (ℚ; _+_; _*_; _/_; Positive)
open import Data.Rational.Tactic.RingSolver using (solve)

import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNLiteralViscousQuadraticCoefficientRound30Exact as Field30
import DASHI.Physics.Closure.NSTriadKNRawCurlFibreGramRound179Exact as R179
import DASHI.Physics.Closure.NSTriadKNPhysicalGramPairTangentRound291Exact as R291
import DASHI.Physics.Closure.NSTriadKNWeightedGramFluxCompilerRound290Exact as R290
import DASHI.Physics.Closure.NSTriadKNDoubleMixedGramPairToResolventRound389Exact as R389
import DASHI.Physics.Closure.NSTriadKNHeatFactorizedPairRemainderRound299Exact as R299

F : C3.RealField _
F = Rational.rationalRealField

half : ℚ
half = + 1 / 2

module DirectPair
    (physicalSystem : Field30.PhysicalFiniteComplex3GalerkinSystem F)
    (S : Helical.HelicalModeScalars F) where

  module P = R389.DoubleMixedPair physicalSystem S

  pairCrossBracket :
    Physical.PhysicalTriadIncidence →
    Physical.PhysicalTriadIncidence → ℚ
  pairCrossBracket alpha beta =
    let Q = P.physicalDoubleMixedPair alpha beta in
    R179.realHermitianCross (R291.forcingA Q) (R291.cellB Q)
      + R179.realHermitianCross (R291.cellA Q) (R291.forcingB Q)

  directResolventPairCompanion :
    (alpha beta : Physical.PhysicalTriadIncidence) →
    Positive (R291.pairRate (P.physicalDoubleMixedPair alpha beta)) → ℚ
  directResolventPairCompanion alpha beta positive =
    let R = P.pairRatePositiveBuildsR290 alpha beta positive in
    half * R290.resolventWeight R * pairCrossBracket alpha beta

  weightedRemainderIsFourDirectCompanion :
    (alpha beta : Physical.PhysicalTriadIncidence) →
    (positive : Positive
      (R291.pairRate (P.physicalDoubleMixedPair alpha beta))) →
    R290.weightedNonlinearRemainder
      (P.pairRatePositiveBuildsR290 alpha beta positive)
    ≡ R299.four * directResolventPairCompanion alpha beta positive
  weightedRemainderIsFourDirectCompanion alpha beta positive =
    let
      Q = P.physicalDoubleMixedPair alpha beta
      R = P.pairRatePositiveBuildsR290 alpha beta positive
      left = R179.realHermitianCross (R291.forcingA Q) (R291.cellB Q)
      right = R179.realHermitianCross (R291.cellA Q) (R291.forcingB Q)
      w = R290.resolventWeight R
    in
    solve (w ∷ left ∷ right ∷ [])

------------------------------------------------------------------------
-- Boundary.
------------------------------------------------------------------------

round496DirectPairUsesLiteralR380R388Forcing : Bool
round496DirectPairUsesLiteralR380R388Forcing = true

round496LaplaceFactorizationRequired : Bool
round496LaplaceFactorizationRequired = false

round496PairRemainderIsFourDirectCompanionClosed : Bool
round496PairRemainderIsFourDirectCompanionClosed = true

round496FiniteOutputPairSummationClosed : Bool
round496FiniteOutputPairSummationClosed = false

round496IntegratedCompanionWeldClosed : Bool
round496IntegratedCompanionWeldClosed = false

round496SignedSpacetimeEstimateClosed : Bool
round496SignedSpacetimeEstimateClosed = false

round496ClayPromotion : Bool
round496ClayPromotion = false

round496PairRemainderIsFourDirectCompanionClosedIsTrue :
  round496PairRemainderIsFourDirectCompanionClosed ≡ true
round496PairRemainderIsFourDirectCompanionClosedIsTrue = refl

round496LaplaceFactorizationRequiredIsFalse :
  round496LaplaceFactorizationRequired ≡ false
round496LaplaceFactorizationRequiredIsFalse = refl

round496ClayPromotionIsFalse : round496ClayPromotion ≡ false
round496ClayPromotionIsFalse = refl
