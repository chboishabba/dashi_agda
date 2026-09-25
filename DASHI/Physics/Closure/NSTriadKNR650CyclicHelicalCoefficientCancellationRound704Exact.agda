{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNR650CyclicHelicalCoefficientCancellationRound704Exact where

------------------------------------------------------------------------
-- ROUND704 / ORIENTED CYCLIC CANCELLATION OF THE THREE OUTER-LEG COEFFICIENTS
--
-- R703 computes, for helicity signs attached consistently to the physical
-- modes p,q,k,
--
--   c_k = lambda_q - lambda_p,
--   c_p = lambda_q - lambda_k,
--   c_q = lambda_p - lambda_k.
--
-- These do not vanish under the unoriented sum c_k+c_p+c_q.  But the exact
-- cyclic orientation obeys
--
--   c_k - c_p + c_q = 0.
--
-- Therefore the scalar multiplier obstruction is gone IF the corresponding
-- projected-cross / coherent-pairing geometry contributes the orientation
--
--   G_k = G,   G_p = -G,   G_q = G
--
-- at the scalar pairing level.  R704 proves only the coefficient identity and
-- records that the remaining Clay-relevant task is the geometric orientation
-- of the three vector/pairing factors.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplexCommutativeRingExact as Ring
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNR650NestedFourHelicityCoefficientRound702Exact as R702

module OrientedCoefficients
    {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (S : Helical.HelicalModeScalars F)
    (L : Helical.PeriodicHelicalProjectorLaws F E I S)
    (velocityTransverse :
      (mode : Z3.FourierMode) →
      Helical.Transverse E mode (Audit.velocity system mode)) where

  module K =
    R702.CoefficientNormalForm system S L velocityTransverse

  baseCoefficient :
    Physical.PhysicalTriadIncidence →
    Helical.HelicitySign →
    Helical.HelicitySign →
    C3.Complex F
  baseCoefficient beta signP signQ =
    C3.complexSubtract
      (K.C.signedEigenvalue signQ (Physical.q beta))
      (K.C.signedEigenvalue signP (Physical.p beta))

  pLegCoefficient :
    Physical.PhysicalTriadIncidence →
    Helical.HelicitySign →
    Helical.HelicitySign →
    C3.Complex F
  pLegCoefficient beta signK signQ =
    C3.complexSubtract
      (K.C.signedEigenvalue signQ (Physical.q beta))
      (K.C.signedEigenvalue signK (Physical.k beta))

  qLegCoefficient :
    Physical.PhysicalTriadIncidence →
    Helical.HelicitySign →
    Helical.HelicitySign →
    C3.Complex F
  qLegCoefficient beta signK signP =
    C3.complexSubtract
      (K.C.signedEigenvalue signP (Physical.p beta))
      (K.C.signedEigenvalue signK (Physical.k beta))

  orientedCyclicCoefficient :
    Physical.PhysicalTriadIncidence →
    Helical.HelicitySign →
    Helical.HelicitySign →
    Helical.HelicitySign →
    C3.Complex F
  orientedCyclicCoefficient beta signP signQ signK =
    C3.complexAdd
      (C3.complexSubtract
        (baseCoefficient beta signP signQ)
        (pLegCoefficient beta signK signQ))
      (qLegCoefficient beta signK signP)

  orientedCyclicCoefficientZero :
    (beta : Physical.PhysicalTriadIncidence) →
    (signP signQ signK : Helical.HelicitySign) →
    orientedCyclicCoefficient beta signP signQ signK
    ≡ C3.complexZero F
  orientedCyclicCoefficientZero beta signP signQ signK =
    R.solve 3
      (λ lp lq lk →
        (((lq R.⊕ (R.⊝ lp))
          R.⊕ (R.⊝ (lq R.⊕ (R.⊝ lk))))
          R.⊕ (lp R.⊕ (R.⊝ lk)))
        R.⊜ R.ε)
      refl
      (K.C.signedEigenvalue signP (Physical.p beta))
      (K.C.signedEigenvalue signQ (Physical.q beta))
      (K.C.signedEigenvalue signK (Physical.k beta))
    where module R = Ring.Solver F

------------------------------------------------------------------------
-- Status.
------------------------------------------------------------------------

round704OrientedThreeLegScalarCoefficientCancellationClosed : Bool
round704OrientedThreeLegScalarCoefficientCancellationClosed = true

round704UnorientedThreeLegScalarSumClaimedZero : Bool
round704UnorientedThreeLegScalarSumClaimedZero = false

round704RemainingExactCancellationTaskIsVectorPairingOrientation : Bool
round704RemainingExactCancellationTaskIsVectorPairingOrientation = true

round704IntroducesEstimate : Bool
round704IntroducesEstimate = false

round704ThreeOuterLegVectorCancellationClosed : Bool
round704ThreeOuterLegVectorCancellationClosed = false

round704ClayPromotion : Bool
round704ClayPromotion = false

round704OrientedThreeLegScalarCoefficientCancellationClosedIsTrue :
  round704OrientedThreeLegScalarCoefficientCancellationClosed ≡ true
round704OrientedThreeLegScalarCoefficientCancellationClosedIsTrue = refl

round704UnorientedThreeLegScalarSumClaimedZeroIsFalse :
  round704UnorientedThreeLegScalarSumClaimedZero ≡ false
round704UnorientedThreeLegScalarSumClaimedZeroIsFalse = refl

round704RemainingExactCancellationTaskIsVectorPairingOrientationIsTrue :
  round704RemainingExactCancellationTaskIsVectorPairingOrientation ≡ true
round704RemainingExactCancellationTaskIsVectorPairingOrientationIsTrue = refl

round704IntroducesEstimateIsFalse :
  round704IntroducesEstimate ≡ false
round704IntroducesEstimateIsFalse = refl

round704ThreeOuterLegVectorCancellationClosedIsFalse :
  round704ThreeOuterLegVectorCancellationClosed ≡ false
round704ThreeOuterLegVectorCancellationClosedIsFalse = refl

round704ClayPromotionIsFalse :
  round704ClayPromotion ≡ false
round704ClayPromotionIsFalse = refl
