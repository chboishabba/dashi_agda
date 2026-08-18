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
-- Authors: Errett Bishop; Douglas Bridges.
-- Title: "Constructive Analysis".
-- DOI: 10.1007/978-3-642-61667-9.
--
-- ROUND77 / NON-UNIT FRAME-WEIGHTED SQUARE CHARGE
--
-- Round76 used the sufficient hypothesis B_k <= 1 to conclude mu^2 <= Q_k.
-- The periodic-scaling audit shows that B_k cannot be normalized to one merely
-- by an upward dyadic torus zoom.  The correct division-free replacement is to
-- retain the reciprocal frame weight rho_k with
--
--   B_k rho_k = 1,       rho_k >= 0.
--
-- The reciprocal is NOT an arbitrary new premise on the positive branch.  The
-- repository's YM lane already uses the Agda standard library's constructive
-- rational reciprocal (`1/_`, decidable zero, `*-inverseˡ`).  We reproduce that
-- domain-independent arithmetic pattern locally here so NS does not depend on
-- a Yang--Mills namespace.  Positive B therefore canonically constructs rho.
--
-- From the already-constructed literal two-channel estimate
--
--   remainder^2 <= Q_k W_k <= Q_k B_k
--
-- we obtain exactly
--
--   rho_k remainder^2 <= Q_k.
--
-- Thus the physically admissible Carleson floor is rho_k mu_k^2.  No square
-- root, ad-hoc amplitude normalization, or assumption B_k <= 1 is required.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational using
  (ℚ; 0ℚ; 1ℚ; Positive; _*_; _≤_; 1/_; _≟_; ≢-nonZero)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)
open import Relation.Nullary using (yes; no)

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

record ReciprocalFrameWeight (frameProduct rho : ℚ) : Set where
  field
    rhoNonnegative : 0ℚ ≤ rho
    reciprocalExact : frameProduct * rho ≡ 1ℚ

open ReciprocalFrameWeight public

------------------------------------------------------------------------
-- Construct the reciprocal canonically from positivity.  This is the same
-- standard-library arithmetic pattern already used in the YM Gate-4 lane.
------------------------------------------------------------------------

data Empty : Set where

emptyEliminate : ∀ {A : Set} → Empty → A
emptyEliminate ()

positiveZeroImpossible : Positive 0ℚ → Empty
positiveZeroImpossible ()

safeRationalReciprocal : ℚ → ℚ
safeRationalReciprocal value with value ≟ 0ℚ
... | yes _ = 0ℚ
... | no value≢zero = (1/ value) {{≢-nonZero value≢zero}}

safeRationalReciprocalTimesPositive :
  ∀ (value : ℚ) → Positive value →
  safeRationalReciprocal value * value ≡ 1ℚ
safeRationalReciprocalTimesPositive value positive with value ≟ 0ℚ
... | yes value≡zero =
  emptyEliminate
    (positiveZeroImpossible (subst Positive value≡zero positive))
... | no value≢zero =
  ℚP.*-inverseˡ value {{≢-nonZero value≢zero}}

positiveFrameReciprocal :
  ∀ frameProduct → Positive frameProduct →
  ReciprocalFrameWeight frameProduct (safeRationalReciprocal frameProduct)
positiveFrameReciprocal frameProduct positive = record
  { rhoNonnegative =
      ℚP.<⇒≤ (ℚP.reciprocal-positive positive)
  ; reciprocalExact =
      trans
        (ℚP.*-comm frameProduct (safeRationalReciprocal frameProduct))
        (safeRationalReciprocalTimesPositive frameProduct positive)
  }

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

round77PositiveFrameReciprocalConstructed : Bool
round77PositiveFrameReciprocalConstructed = true

round77LiteralNonUnitFrameWeightedSquareChargeConstructed : Bool
round77LiteralNonUnitFrameWeightedSquareChargeConstructed = true

round77PhysicalFrameProductPositiveAtSelectedCriticalEvent : Bool
round77PhysicalFrameProductPositiveAtSelectedCriticalEvent = false

round77CanonicalQIdentifiedWithDynamicPhysicalBudgetCharge : Bool
round77CanonicalQIdentifiedWithDynamicPhysicalBudgetCharge = false

round77PositiveFrameReciprocalConstructedIsTrue :
  round77PositiveFrameReciprocalConstructed ≡ true
round77PositiveFrameReciprocalConstructedIsTrue = refl

round77LiteralNonUnitFrameWeightedSquareChargeConstructedIsTrue :
  round77LiteralNonUnitFrameWeightedSquareChargeConstructed ≡ true
round77LiteralNonUnitFrameWeightedSquareChargeConstructedIsTrue = refl
