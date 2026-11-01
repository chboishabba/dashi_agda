module DASHI.Physics.Closure.NSTriadKNFixedOutputTwoChannelNormalizedChargeRound76Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: Augustin-Louis Cauchy; Hermann Amandus Schwarz.
-- Classical finite-dimensional Cauchy--Schwarz inequality; DOI not applicable.
--
-- Author: Jean Leray.
-- Title: "Sur le mouvement d'un liquide visqueux emplissant l'espace".
-- DOI: 10.1007/BF02547354.
--
-- Author: Ole Christensen.
-- Title: "An Introduction to Frames and Riesz Bases".
-- DOI: 10.1007/978-3-319-25613-9.
--
-- ROUND76 / LITERAL FIXED-OUTPUT NORMALIZATION -> CANONICAL SQUARE CHARGE
--
-- Round75 proves on the exact rational Galerkin output fibre
--
--   W_k <= ||u_k||^2 E_N
--
-- with no fibre-cardinality loss.  Therefore at any physical critical event
-- where the SAME output satisfies
--
--   ||u_k||^2 E_N <= 1,
--
-- the canonical two-channel effective complexity is normalized:
--
--   W_k <= 1.
--
-- Combining this directly with the Round74 two-channel Cauchy theorem gives
--
--   (signed triadic remainder)^2 <= Q_k.
--
-- No arbitrary frame bound, phase choice, factor rescaling, square root or
-- division is introduced.  The remaining concentration theorem is therefore
-- dynamic/physical: transport this exact static overlay to the selected
-- trajectory at the critical event, prove the physical normalization there,
-- and identify canonical Q_k with the actual charge admitted by the finite
-- budget ledger.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ; 1ℚ; _*_; _≤_)
import Data.Rational.Properties as ℚP
open import Relation.Binary.PropositionalEquality using (subst)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as RationalL2
import DASHI.Physics.Closure.NSTriadKNRationalComplex3LerayPythagoras as Leray
import DASHI.Physics.Closure.NSTriadKNStaticPairingEmitsStructuredTriadicAtomsRound72Exact as Fine
import DASHI.Physics.Closure.NSTriadKNCriticalRemainderTriadicCauchyRound71Exact as R71
import DASHI.Physics.Closure.NSTriadKNFactorizedEffectiveComplexityCauchyRound72Exact as Effective
import DASHI.Physics.Closure.NSTriadKNTwoChannelStructuredCauchyOverlayRound74Exact as Two
import DASHI.Physics.Closure.NSTriadKNStaticRationalTwoChannelOverlayRound75Exact as Static
import DASHI.Physics.Closure.NSTriadKNFixedOutputTwoChannelFrameRound75Exact as Frame

F : C3.RealField _
F = RationalL2.rationalRealField

literalOutputFrameProduct :
  ∀ {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E} →
  Audit.FiniteComplex3GalerkinSystem F E I →
  Z3.FourierMode → ℚ
literalOutputFrameProduct system output =
  Frame.modeEnergy system output * Frame.cutoffEnergy system

literalFixedOutputComplexityBelowOne :
  ∀ {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (O : Leray.RationalInverseNormOrder E I)
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (output : Z3.FourierMode)
    (outputNonzero : Z3.NonZeroMode output)
    (commutatorValue : Z3.FourierMode → ℚ)
    (hh : Fine.HHOwnerSelection) →
  literalOutputFrameProduct system output ≤ 1ℚ →
  Two.twoChannelEffectiveComplexity
    (Static.staticRationalTwoChannelOverlay
      system output commutatorValue hh)
  ≤ 1ℚ
literalFixedOutputComplexityBelowOne
    O system output outputNonzero commutatorValue hh frameProductBelowOne =
  ℚP.≤-trans
    (Frame.staticRationalOverlayEffectiveComplexityFrameBound
      O system output outputNonzero commutatorValue hh)
    frameProductBelowOne

normalizedTwoChannelProductBelowCharge :
  ∀ {atoms}
    (overlay : Two.TriadicTwoChannelOverlay atoms) →
  Two.twoChannelEffectiveComplexity overlay ≤ 1ℚ →
  Two.twoChannelCharge overlay * Two.twoChannelEffectiveComplexity overlay
  ≤ Two.twoChannelCharge overlay
normalizedTwoChannelProductBelowCharge overlay complexityBelowOne =
  let
    chargeNN =
      Effective.concentrationChargeNonnegative (Two.twoChannelFactors overlay)
    complexityNN =
      Effective.effectiveComplexityNonnegative (Two.twoChannelFactors overlay)

    productBelowOne :
      Two.twoChannelCharge overlay * Two.twoChannelEffectiveComplexity overlay
      ≤ Two.twoChannelCharge overlay * 1ℚ
    productBelowOne =
      RationalL2.nonnegativeProductMonotone
        chargeNN complexityNN chargeNN ℚP.0≤1
        ℚP.≤-refl complexityBelowOne
  in
  subst
    (λ upper →
      Two.twoChannelCharge overlay * Two.twoChannelEffectiveComplexity overlay
      ≤ upper)
    (ℚP.*-identityʳ (Two.twoChannelCharge overlay))
    productBelowOne

literalFixedOutputNormalizedSquareCharge :
  ∀ {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (O : Leray.RationalInverseNormOrder E I)
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (output : Z3.FourierMode)
    (outputNonzero : Z3.NonZeroMode output)
    (commutatorValue : Z3.FourierMode → ℚ)
    (hh : Fine.HHOwnerSelection) →
  literalOutputFrameProduct system output ≤ 1ℚ →
  RationalL2.square
    (R71.triadicSignedSum
      (Fine.structuredTriadicAtoms
        (Static.staticRationalPhysicalPairing system output commutatorValue) hh))
  ≤ Two.twoChannelCharge
      (Static.staticRationalTwoChannelOverlay
        system output commutatorValue hh)
literalFixedOutputNormalizedSquareCharge
    O system output outputNonzero commutatorValue hh frameProductBelowOne =
  let
    overlay = Static.staticRationalTwoChannelOverlay
      system output commutatorValue hh
    cauchy = Static.staticRationalTwoChannelCauchy
      system output commutatorValue hh
    normalized = literalFixedOutputComplexityBelowOne
      O system output outputNonzero commutatorValue hh frameProductBelowOne
  in
  ℚP.≤-trans cauchy
    (normalizedTwoChannelProductBelowCharge overlay normalized)

round76LiteralFixedOutputNormalizationHasNoAbstractFrameCertificate : Bool
round76LiteralFixedOutputNormalizationHasNoAbstractFrameCertificate = true

round76LiteralFixedOutputNormalizedSquareChargeConstructed : Bool
round76LiteralFixedOutputNormalizedSquareChargeConstructed = true

round76SelectedTrajectoryCriticalEventNormalizationConstructed : Bool
round76SelectedTrajectoryCriticalEventNormalizationConstructed = false

round76CanonicalQIdentifiedWithPhysicalBudgetCharge : Bool
round76CanonicalQIdentifiedWithPhysicalBudgetCharge = false

round76LiteralFixedOutputNormalizedSquareChargeConstructedIsTrue :
  round76LiteralFixedOutputNormalizedSquareChargeConstructed ≡ true
round76LiteralFixedOutputNormalizedSquareChargeConstructedIsTrue = refl
