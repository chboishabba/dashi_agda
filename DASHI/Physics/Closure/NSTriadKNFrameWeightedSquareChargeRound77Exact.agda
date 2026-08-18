module DASHI.Physics.Closure.NSTriadKNFrameWeightedSquareChargeRound77Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: Augustin-Louis Cauchy; Hermann Amandus Schwarz.
-- Classical finite Cauchy--Schwarz inequality; DOI not applicable.
--
-- Author: Ole Christensen.
-- Title: "An Introduction to Frames and Riesz Bases".
-- DOI: 10.1007/978-3-319-25613-9.
--
-- Author: Jean Leray.
-- Title: "Sur le mouvement d'un liquide visqueux emplissant l'espace".
-- DOI: 10.1007/BF02547354.
--
-- ROUND77 / NON-UNIT FRAME-WEIGHTED SQUARE CHARGE
--
-- Round76 used the sufficient hypothesis B_k <= 1 to conclude mu^2 <= Q_k.
-- The periodic-scaling audit shows that B_k cannot be normalized to one merely
-- by an upward dyadic torus zoom.  The correct division-free replacement is to
-- retain an explicit reciprocal frame weight rho_k:
--
--   B_k rho_k = 1,       rho_k >= 0.
--
-- From the already-constructed literal two-channel estimate
--
--   remainder^2 <= Q_k W_k <= Q_k B_k
--
-- we obtain exactly
--
--   rho_k remainder^2 <= Q_k.
--
-- Thus the physically admissible Carleson floor is the FRAME-WEIGHTED square
-- rho_k mu_k^2.  No square root, ad-hoc amplitude normalization, or assumption
-- B_k <= 1 is required.  This changes the correct D2 propagation threshold from
-- sum r_i^2 > 1 to the weighted condition
--
--   sum rho_i r_i^2 > rho_parent.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _*_; _≤_)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; subst; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSPeriodicConcreteCutoffCubeCarrier as Cube
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
import DASHI.Physics.Closure.NSTriadKNFixedOutputTwoChannelNormalizedChargeRound76Exact as R76

F : C3.RealField _
F = RationalL2.rationalRealField

------------------------------------------------------------------------
-- Generic reciprocal-frame compiler.
------------------------------------------------------------------------

record ReciprocalFrameWeight (frameProduct rho : ℚ) : Set where
  field
    rhoNonnegative : 0ℚ ≤ rho
    reciprocalExact : frameProduct * rho ≡ 1ℚ

open ReciprocalFrameWeight public

reciprocalFrameWeightTurnsProductChargeIntoCharge :
  ∀ {x charge frame rho} →
  0ℚ ≤ x →
  0ℚ ≤ charge →
  x ≤ charge * frame →
  ReciprocalFrameWeight frame rho →
  rho * x ≤ charge
reciprocalFrameWeightTurnsProductChargeIntoCharge
    {x} {charge} {frame} {rho} xNN chargeNN xBelow weighted =
  let
    productNN : 0ℚ ≤ charge * frame
    productNN = ℚP.0≤*0≤ chargeNN

    scaled : rho * x ≤ rho * (charge * frame)
    scaled =
      RationalL2.nonnegativeProductMonotone
        (rhoNonnegative weighted) xNN
        (rhoNonnegative weighted) productNN
        ℚP.≤-refl xBelow

    commuteToReciprocal :
      rho * (charge * frame) ≡ charge * (frame * rho)
    commuteToReciprocal = solve (rho ∷ charge ∷ frame ∷ [])

    collapse : charge * (frame * rho) ≡ charge
    collapse =
      trans
        (cong (charge *_) (reciprocalExact weighted))
        (ℚP.*-identityʳ charge)
  in
  subst (rho * x ≤_)
    (trans commuteToReciprocal collapse)
    scaled

------------------------------------------------------------------------
-- Same literal Round75 two-channel row, now without B<=1.
------------------------------------------------------------------------

literalFixedOutputSquareBelowChargeTimesFrame :
  ∀ {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (O : Leray.RationalInverseNormOrder E I)
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (output : Z3.FourierMode)
    (outputNonzero : Z3.NonZeroMode output)
    (commutatorValue : Z3.FourierMode → ℚ)
    (hh : Fine.HHOwnerSelection) →
  RationalL2.square
    (R71.triadicSignedSum
      (Fine.structuredTriadicAtoms
        (Static.staticRationalPhysicalPairing system output commutatorValue) hh))
  ≤ Two.twoChannelCharge
      (Static.staticRationalTwoChannelOverlay
        system output commutatorValue hh)
      * R76.literalOutputFrameProduct system output
literalFixedOutputSquareBelowChargeTimesFrame
    O system output outputNonzero commutatorValue hh =
  let
    overlay = Static.staticRationalTwoChannelOverlay
      system output commutatorValue hh

    cauchy = Static.staticRationalTwoChannelCauchy
      system output commutatorValue hh

    frameBound =
      Frame.staticRationalOverlayEffectiveComplexityFrameBound
        O system output outputNonzero commutatorValue hh

    chargeNN = Effective.concentrationChargeNonnegative
      (Two.twoChannelFactors overlay)
    complexityNN = Effective.effectiveComplexityNonnegative
      (Two.twoChannelFactors overlay)
    outputNN = Frame.modeEnergyNonnegative system output
    cutoffNN =
      Frame.sumMassNonnegative
        (Frame.modeEnergy system)
        (Frame.modeEnergyNonnegative system)
        (Cube.cutoffModes (Audit.cutoff system))
    frameNN : 0ℚ ≤ R76.literalOutputFrameProduct system output
    frameNN = ℚP.0≤*0≤ outputNN cutoffNN

    productBound :
      Two.twoChannelCharge overlay * Two.twoChannelEffectiveComplexity overlay
      ≤ Two.twoChannelCharge overlay * R76.literalOutputFrameProduct system output
    productBound =
      RationalL2.nonnegativeProductMonotone
        chargeNN complexityNN chargeNN frameNN
        ℚP.≤-refl frameBound
  in
  ℚP.≤-trans cauchy productBound

literalFixedOutputFrameWeightedSquareCharge :
  ∀ {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (O : Leray.RationalInverseNormOrder E I)
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (output : Z3.FourierMode)
    (outputNonzero : Z3.NonZeroMode output)
    (commutatorValue : Z3.FourierMode → ℚ)
    (hh : Fine.HHOwnerSelection)
    (rho : ℚ) →
  ReciprocalFrameWeight (R76.literalOutputFrameProduct system output) rho →
  rho * RationalL2.square
    (R71.triadicSignedSum
      (Fine.structuredTriadicAtoms
        (Static.staticRationalPhysicalPairing system output commutatorValue) hh))
  ≤ Two.twoChannelCharge
      (Static.staticRationalTwoChannelOverlay
        system output commutatorValue hh)
literalFixedOutputFrameWeightedSquareCharge
    O system output outputNonzero commutatorValue hh rho weighted =
  let
    overlay = Static.staticRationalTwoChannelOverlay
      system output commutatorValue hh
    squareNN = RationalL2.squareNonnegative
      (R71.triadicSignedSum
        (Fine.structuredTriadicAtoms
          (Static.staticRationalPhysicalPairing system output commutatorValue) hh))
    chargeNN = Effective.concentrationChargeNonnegative
      (Two.twoChannelFactors overlay)
    squareBelow = literalFixedOutputSquareBelowChargeTimesFrame
      O system output outputNonzero commutatorValue hh
  in
  reciprocalFrameWeightTurnsProductChargeIntoCharge
    squareNN chargeNN squareBelow weighted

round77AbsoluteUnitFrameNormalizationRequired : Bool
round77AbsoluteUnitFrameNormalizationRequired = false

round77LiteralNonUnitFrameWeightedSquareChargeConstructed : Bool
round77LiteralNonUnitFrameWeightedSquareChargeConstructed = true

round77PhysicalReciprocalFrameWeightAtSelectedCriticalEventConstructed : Bool
round77PhysicalReciprocalFrameWeightAtSelectedCriticalEventConstructed = false

round77CanonicalQIdentifiedWithDynamicPhysicalBudgetCharge : Bool
round77CanonicalQIdentifiedWithDynamicPhysicalBudgetCharge = false

round77LiteralNonUnitFrameWeightedSquareChargeConstructedIsTrue :
  round77LiteralNonUnitFrameWeightedSquareChargeConstructed ≡ true
round77LiteralNonUnitFrameWeightedSquareChargeConstructedIsTrue = refl

round77AbsoluteUnitFrameNormalizationRequiredIsFalse :
  round77AbsoluteUnitFrameNormalizationRequired ≡ false
round77AbsoluteUnitFrameNormalizationRequiredIsFalse = refl
