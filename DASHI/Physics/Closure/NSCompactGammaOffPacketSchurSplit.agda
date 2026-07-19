module DASHI.Physics.Closure.NSCompactGammaOffPacketSchurSplit where

open import Agda.Primitive using (Set₁)

open import DASHI.Physics.Closure.NSCompactGammaReplenishmentAbsorption

------------------------------------------------------------------------
-- Abstract composition surface for the differential obstruction isolated by
-- the compact-Gamma audit.
--
-- The analytic target has the form
--
--   |D m_off(u)[h]|
--     <= C_Schur E(u) ||h||_Xtilde + Tail(u,h).
--
-- This module does not construct the concrete weighted norm, the Schur
-- constant, or the tail estimate.  It proves that a near-shell estimate and
-- an explicit far-shell remainder compose into the required off-packet bound,
-- and that this bound can be inserted into a total logarithmic-escape
-- numerator estimate.
------------------------------------------------------------------------

record OffPacketSchurSplitInputs
    (A : AbsorptionArithmetic) : Set₁ where
  field
    offPacketResponse : Scalar A
    nearShellResponse : Scalar A
    farShellTail : Scalar A
    schurWeightedBudget : Scalar A

    offPacketBelowNearPlusTail :
      _≤_ A offPacketResponse
        (_+_ A nearShellResponse farShellTail)

    nearShellBelowSchurBudget :
      _≤_ A nearShellResponse schurWeightedBudget

open OffPacketSchurSplitInputs public

offPacketResponseBelowSchurPlusTail :
  (A : AbsorptionArithmetic) →
  (I : OffPacketSchurSplitInputs A) →
  _≤_ A
    (offPacketResponse I)
    (_+_ A (schurWeightedBudget I) (farShellTail I))
offPacketResponseBelowSchurPlusTail A I =
  ≤-trans A
    (offPacketBelowNearPlusTail I)
    (additionMonotoneRight A (nearShellBelowSchurBudget I))

------------------------------------------------------------------------
-- Optional tail absorption.  This is the exact composition needed once a
-- separate shell-decay estimate controls the measured far-shell term.
------------------------------------------------------------------------

record OffPacketTailAbsorptionInputs
    (A : AbsorptionArithmetic) : Set₁ where
  field
    splitInputs : OffPacketSchurSplitInputs A
    absorbedTailBudget : Scalar A
    fullOffPacketBudget : Scalar A

    farTailBelowAbsorbedBudget :
      _≤_ A
        (farShellTail splitInputs)
        absorbedTailBudget

    schurPlusAbsorbedTailBelowFullBudget :
      _≤_ A
        (_+_ A
          (schurWeightedBudget splitInputs)
          absorbedTailBudget)
        fullOffPacketBudget

open OffPacketTailAbsorptionInputs public

absorbedTailBoundsOffPacketResponse :
  (A : AbsorptionArithmetic) →
  (I : OffPacketTailAbsorptionInputs A) →
  _≤_ A
    (offPacketResponse (splitInputs I))
    (fullOffPacketBudget I)
absorbedTailBoundsOffPacketResponse A I =
  ≤-trans A
    (offPacketResponseBelowSchurPlusTail A (splitInputs I))
    (≤-trans A
      (additionMonotoneLeft A (farTailBelowAbsorbedBudget I))
      (schurPlusAbsorbedTailBelowFullBudget I))

------------------------------------------------------------------------
-- Adapter to a complete logarithmic-escape numerator.  `otherResponse`
-- collects target-packet and viscous differential terms.  Supplying their
-- bound together with the off-packet Schur-tail split yields the total bound
-- required by the division-free logarithmic modulus theorem.
------------------------------------------------------------------------

record OffPacketLogNumeratorInputs
    (A : AbsorptionArithmetic) : Set₁ where
  field
    splitInputs : OffPacketSchurSplitInputs A
    logarithmicNumerator : Scalar A
    otherResponse : Scalar A
    totalNumeratorBudget : Scalar A

    logarithmicNumeratorBelowOtherPlusOffPacket :
      _≤_ A
        logarithmicNumerator
        (_+_ A
          otherResponse
          (offPacketResponse splitInputs))

    otherPlusSchurTailBelowTotalBudget :
      _≤_ A
        (_+_ A
          otherResponse
          (_+_ A
            (schurWeightedBudget splitInputs)
            (farShellTail splitInputs)))
        totalNumeratorBudget

open OffPacketLogNumeratorInputs public

offPacketSchurSplitBoundsLogNumerator :
  (A : AbsorptionArithmetic) →
  (I : OffPacketLogNumeratorInputs A) →
  _≤_ A
    (logarithmicNumerator I)
    (totalNumeratorBudget I)
offPacketSchurSplitBoundsLogNumerator A I =
  ≤-trans A
    (logarithmicNumeratorBelowOtherPlusOffPacket I)
    (≤-trans A
      (additionMonotoneLeft A
        (offPacketResponseBelowSchurPlusTail A (splitInputs I)))
      (otherPlusSchurTailBelowTotalBudget I))
