{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNA3CauchyForcingMismatchRound604Exact where

------------------------------------------------------------------------
-- ROUND604 / CANONICAL PHYSICAL A3 <-> CAUCHY-FORCING MISMATCH
--
-- R602 proves
--
--   Full(R601Residual)
--     = 2 * ( R * (4 * ForcingFull) - 4 * (4 * A3) ).
--
-- Pure rational normalization therefore gives
--
--   Full(R601Residual)
--     = 8 * ( R * ForcingFull - 4 * A3 ).
--
-- Thus every exact route that tries to identify the centered A3 carrier with
-- the weighted Cauchy/R567 consumer has one literal fixed-output scalar left:
--
--   R * ForcingFull = 4 * A3.
--
-- R603 proves that R291 + Cauchy inversion alone do not force this mismatch to
-- vanish.  Consequently this is not another finite-reindexing lemma hidden in
-- the generic algebra.  It must be paid by additional literal NS structure or
-- replaced by a genuine estimate.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ; Positive; _-_; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNHelicitySignNormalizedCurlRound142Exact as R142
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNLiteralViscousQuadraticCoefficientRound30Exact as Field30
import DASHI.Physics.Closure.NSTriadKNMixedHelicityFixedOutputCollapseRound225Exact as R225
import DASHI.Physics.Closure.NSTriadKNSymmetricUnorderedOrderedOffDiagonalRound539Exact as R539
import DASHI.Physics.Closure.NSTriadKNFullSquareDiagonalOffDiagonalRound543Exact as R543
import DASHI.Physics.Closure.NSTriadKNA3CenteredKernelNormalFormExact as Kernel
import DASHI.Physics.Closure.NSTriadKNA3CenteredRemainderReconciliationRound602Exact as R602
import DASHI.Physics.Closure.NSTriadKNA3CauchyAlgebraVanishingNoGoRound603Exact as R603

F : C3.RealField _
F = Rational.rationalRealField

module FixedOutput
    (physicalSystem : Field30.PhysicalFiniteComplex3GalerkinSystem F)
    (S : Helical.HelicalModeScalars F)
    (L : Helical.PeriodicHelicalProjectorLaws F
      (Field30.physicalEmbedding physicalSystem)
      (Field30.physicalInverseSquare physicalSystem) S)
    (H : R142.HelicalHalfCalibration S)
    (P : R225.PhysicalFixedOutputHelicityData
      (Field30.physicalEmbedding physicalSystem)
      (Field30.physicalInverseSquare physicalSystem)
      S L H
      (Audit.velocityAt (Field30.finiteSystem physicalSystem)))
    (viscosityPositive : Positive (Field30.viscosity physicalSystem))
    (output : Z3.FourierMode)
    (outputNonzero : Z3.NonZeroMode output) where

  module R = R602.FixedOutput
    physicalSystem S L H P viscosityPositive output outputNonzero

  eight : ℚ
  eight = R539.two * Kernel.four

  canonicalPhysicalMismatch : ℚ
  canonicalPhysicalMismatch =
    R.Base.rateTotal * R.Mismatch.forcingFull
      - Kernel.four * R.Base.A3.signedA3

  r601ResidualIsEightTimesCanonicalMismatch :
    R543.fullSquareSum
      R.R.centeredDynamicRemainderPair R.R.fibre
    ≡ eight * canonicalPhysicalMismatch
  r601ResidualIsEightTimesCanonicalMismatch =
    trans
      R.r601FullIsTwiceR598Mismatch
      (solve
        ( R.Base.rateTotal
        ∷ Kernel.four
        ∷ R.Mismatch.forcingFull
        ∷ R.Base.A3.signedA3
        ∷ []))

------------------------------------------------------------------------
-- Status / exact source-facing frontier.
------------------------------------------------------------------------

round604R601ResidualIsEightTimesCanonicalMismatch : Bool
round604R601ResidualIsEightTimesCanonicalMismatch = true

round604CanonicalIdentityIsRateTotalForcingEqualsFourA3 : Bool
round604CanonicalIdentityIsRateTotalForcingEqualsFourA3 = true

round604CanonicalPhysicalMismatchClosed : Bool
round604CanonicalPhysicalMismatchClosed = false

round604PureR291CauchyAlgebraSuffices : Bool
round604PureR291CauchyAlgebraSuffices =
  R603.round603PureFiniteAlgebraForcesMismatchVanishing

round604AdditionalLiteralNSStructureOrEstimateRequired : Bool
round604AdditionalLiteralNSStructureOrEstimateRequired =
  R603.round603AdditionalPhysicalStructureOrEstimateRequired

round604IntroducesEstimate : Bool
round604IntroducesEstimate = false

round604R601ResidualIsEightTimesCanonicalMismatchIsTrue :
  round604R601ResidualIsEightTimesCanonicalMismatch ≡ true
round604R601ResidualIsEightTimesCanonicalMismatchIsTrue = refl

round604CanonicalIdentityIsRateTotalForcingEqualsFourA3IsTrue :
  round604CanonicalIdentityIsRateTotalForcingEqualsFourA3 ≡ true
round604CanonicalIdentityIsRateTotalForcingEqualsFourA3IsTrue = refl

round604CanonicalPhysicalMismatchClosedIsFalse :
  round604CanonicalPhysicalMismatchClosed ≡ false
round604CanonicalPhysicalMismatchClosedIsFalse = refl

round604PureR291CauchyAlgebraSufficesIsFalse :
  round604PureR291CauchyAlgebraSuffices ≡ false
round604PureR291CauchyAlgebraSufficesIsFalse =
  R603.round603PureFiniteAlgebraForcesMismatchVanishingIsFalse

round604AdditionalLiteralNSStructureOrEstimateRequiredIsTrue :
  round604AdditionalLiteralNSStructureOrEstimateRequired ≡ true
round604AdditionalLiteralNSStructureOrEstimateRequiredIsTrue =
  R603.round603AdditionalPhysicalStructureOrEstimateRequiredIsTrue

round604IntroducesEstimateIsFalse :
  round604IntroducesEstimate ≡ false
round604IntroducesEstimateIsFalse = refl
