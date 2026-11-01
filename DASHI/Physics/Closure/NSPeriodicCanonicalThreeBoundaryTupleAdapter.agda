module DASHI.Physics.Closure.NSPeriodicCanonicalThreeBoundaryTupleAdapter where

open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Equality using (_≡_)

open import DASHI.Physics.Closure.NSCompactGammaReplenishmentAbsorption
import DASHI.Physics.Closure.NSPeriodicNormalizedBoundaryCandidateTuple as Candidate
import DASHI.Physics.Closure.NSPeriodicThreeBoundaryPDEMargins as Margins
open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- One real-carrier interpretation of the selected normalized boundary tuple.
--
-- This prevents the three strict signs from being proved with incompatible
-- values of gamma*, rho*, eta* or M².  The actual PDE supplies and losses remain
-- explicit functions of this one interpreted tuple.
------------------------------------------------------------------------

record CanonicalBoundaryTupleInterpretation
    (A : AbsorptionArithmetic) : Set₁ where
  field
    gammaThreshold packetFractionThreshold offPacketThreshold
      sizeSquaredCeiling interpretOne : Scalar A

    RepresentsFraction : Nat → Nat → Scalar A → Set
    RepresentsNatural : Nat → Scalar A → Set

    gammaMeaning :
      RepresentsFraction
        (Candidate.gammaNumerator Candidate.selectedNormalizedBoundaryCandidate)
        (Candidate.gammaDenominator Candidate.selectedNormalizedBoundaryCandidate)
        gammaThreshold

    packetFractionMeaning :
      RepresentsFraction
        (Candidate.packetFractionNumerator
          Candidate.selectedNormalizedBoundaryCandidate)
        (Candidate.fractionDenominator
          Candidate.selectedNormalizedBoundaryCandidate)
        packetFractionThreshold

    offPacketMeaning :
      RepresentsFraction
        (Candidate.offPacketNumerator
          Candidate.selectedNormalizedBoundaryCandidate)
        (Candidate.fractionDenominator
          Candidate.selectedNormalizedBoundaryCandidate)
        offPacketThreshold

    sizeMeaning :
      RepresentsNatural
        (Candidate.sizeSquaredCeiling
          Candidate.selectedNormalizedBoundaryCandidate)
        sizeSquaredCeiling

    complementaryPacketOff :
      _+_ A packetFractionThreshold offPacketThreshold
      ≡ interpretOne

open CanonicalBoundaryTupleInterpretation public

record CanonicalThreeBoundaryPDEOwner
    (A : AbsorptionArithmetic)
    (S : Margins.StrictMarginArithmetic A) : Set₁ where
  field
    tuple : CanonicalBoundaryTupleInterpretation A

    gammaInwardAt gammaLossAt gammaReplenishmentAt gammaMarginAt :
      CanonicalBoundaryTupleInterpretation A → Scalar A

    packetInwardAt packetLossAt packetSupplyAt packetMarginAt :
      CanonicalBoundaryTupleInterpretation A → Scalar A

    sizeInwardAt sizeLossAt sizeDissipationAt sizeMarginAt :
      CanonicalBoundaryTupleInterpretation A → Scalar A

    gammaBalanceAtTuple :
      _+_ A (gammaInwardAt tuple) (gammaLossAt tuple)
      ≡ gammaReplenishmentAt tuple

    gammaLossPlusMarginBelowReplenishmentAtTuple :
      _≤_ A
        (_+_ A (gammaLossAt tuple) (gammaMarginAt tuple))
        (gammaReplenishmentAt tuple)

    gammaMarginPositiveAtTuple :
      Margins.StrictlyPositive S (gammaMarginAt tuple)

    packetBalanceAtTuple :
      _+_ A (packetInwardAt tuple) (packetLossAt tuple)
      ≡ packetSupplyAt tuple

    packetLossPlusMarginBelowSupplyAtTuple :
      _≤_ A
        (_+_ A (packetLossAt tuple) (packetMarginAt tuple))
        (packetSupplyAt tuple)

    packetMarginPositiveAtTuple :
      Margins.StrictlyPositive S (packetMarginAt tuple)

    sizeBalanceAtTuple :
      _+_ A (sizeInwardAt tuple) (sizeLossAt tuple)
      ≡ sizeDissipationAt tuple

    sizeLossPlusMarginBelowDissipationAtTuple :
      _≤_ A
        (_+_ A (sizeLossAt tuple) (sizeMarginAt tuple))
        (sizeDissipationAt tuple)

    sizeMarginPositiveAtTuple :
      Margins.StrictlyPositive S (sizeMarginAt tuple)

open CanonicalThreeBoundaryPDEOwner public

canonicalTupleToThreeBoundaryMarginInputs :
  ∀ {A : AbsorptionArithmetic}
    {S : Margins.StrictMarginArithmetic A} →
  CanonicalThreeBoundaryPDEOwner A S →
  Margins.ThreeBoundaryPDEMarginInputs A S
canonicalTupleToThreeBoundaryMarginInputs P = record
  { gammaInwardDerivative = gammaInwardAt P (tuple P)
  ; gammaLoss = gammaLossAt P (tuple P)
  ; gammaReplenishment = gammaReplenishmentAt P (tuple P)
  ; gammaMargin = gammaMarginAt P (tuple P)
  ; packetInwardDerivative = packetInwardAt P (tuple P)
  ; packetLoss = packetLossAt P (tuple P)
  ; packetSupply = packetSupplyAt P (tuple P)
  ; packetMargin = packetMarginAt P (tuple P)
  ; sizeInwardDerivative = sizeInwardAt P (tuple P)
  ; sizeLoss = sizeLossAt P (tuple P)
  ; sizeDissipation = sizeDissipationAt P (tuple P)
  ; sizeMargin = sizeMarginAt P (tuple P)
  ; gammaBalance = gammaBalanceAtTuple P
  ; gammaLossPlusMarginBelowReplenishment =
      gammaLossPlusMarginBelowReplenishmentAtTuple P
  ; gammaMarginPositive = gammaMarginPositiveAtTuple P
  ; packetBalance = packetBalanceAtTuple P
  ; packetLossPlusMarginBelowSupply =
      packetLossPlusMarginBelowSupplyAtTuple P
  ; packetMarginPositive = packetMarginPositiveAtTuple P
  ; sizeBalance = sizeBalanceAtTuple P
  ; sizeLossPlusMarginBelowDissipation =
      sizeLossPlusMarginBelowDissipationAtTuple P
  ; sizeMarginPositive = sizeMarginPositiveAtTuple P
  }

canonicalTupleGivesThreeStrictBoundarySigns :
  ∀ {A : AbsorptionArithmetic}
    {S : Margins.StrictMarginArithmetic A} →
  (P : CanonicalThreeBoundaryPDEOwner A S) →
  Margins.ThreeUniversalStrictBoundarySigns S
    (canonicalTupleToThreeBoundaryMarginInputs P)
canonicalTupleGivesThreeStrictBoundarySigns P =
  Margins.threeUniversalStrictBoundarySigns
    (canonicalTupleToThreeBoundaryMarginInputs P)

------------------------------------------------------------------------
-- Status: one literal interpretation of (7/100,64/100,36/100,45) now owns all
-- three strict-margin comparisons.  The remaining PDE mathematics is exactly the
-- three supply-vs-loss estimates represented by the `...AtTuple` fields.
------------------------------------------------------------------------

canonicalThreeBoundaryTupleAdapterLevel : ProofLevel
canonicalThreeBoundaryTupleAdapterLevel = machineChecked
