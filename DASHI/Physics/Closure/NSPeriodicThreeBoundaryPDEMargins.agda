module DASHI.Physics.Closure.NSPeriodicThreeBoundaryPDEMargins where

open import Agda.Builtin.Equality using (_≡_)
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import DASHI.Physics.Closure.NSCompactGammaReplenishmentAbsorption
open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Quantitative common ledger for the three independent normalized faces.
--
-- Each inward derivative is presented as
--
--   inwardDerivative + loss = supply,
--   loss + strictMargin <= supply.
--
-- Ordered cancellation then proves strict inwardness.  The packet/off face is
-- represented once; the exact complement-duality modules transport that sign
-- to the off-packet ceiling.
------------------------------------------------------------------------

record StrictMarginArithmetic
    (A : AbsorptionArithmetic) : Set₁ where
  field
    StrictlyPositive : Scalar A → Set

    positiveUpwardClosed : ∀ {margin value} →
      StrictlyPositive margin →
      _≤_ A margin value →
      StrictlyPositive value

open StrictMarginArithmetic public

strictMarginFromBalance :
  ∀ {A : AbsorptionArithmetic} →
  (S : StrictMarginArithmetic A) →
  ∀ {inwardDerivative loss supply margin} →
  _+_ A inwardDerivative loss ≡ supply →
  _≤_ A (_+_ A loss margin) supply →
  StrictlyPositive S margin →
  StrictlyPositive S inwardDerivative
strictMarginFromBalance {A = A} S
  {inwardDerivative} {loss} {supply} {margin}
  balance marginFits marginPositive =
  positiveUpwardClosed S marginPositive marginBelowDerivative
  where
  lossPlusMarginBelowDerivativePlusLoss :
    _≤_ A (_+_ A loss margin) (_+_ A inwardDerivative loss)
  lossPlusMarginBelowDerivativePlusLoss =
    subst
      (λ upper → _≤_ A (_+_ A loss margin) upper)
      (sym balance)
      marginFits

  marginPlusLossBelowDerivativePlusLoss :
    _≤_ A (_+_ A margin loss) (_+_ A inwardDerivative loss)
  marginPlusLossBelowDerivativePlusLoss =
    subst
      (λ lower → _≤_ A lower (_+_ A inwardDerivative loss))
      (addCommutative A loss margin)
      lossPlusMarginBelowDerivativePlusLoss

  marginBelowDerivative : _≤_ A margin inwardDerivative
  marginBelowDerivative =
    additionCancelRight A marginPlusLossBelowDerivativePlusLoss

record ThreeBoundaryPDEMarginInputs
    (A : AbsorptionArithmetic)
    (S : StrictMarginArithmetic A) : Set₁ where
  field
    gammaInwardDerivative gammaLoss gammaReplenishment gammaMargin : Scalar A
    packetInwardDerivative packetLoss packetSupply packetMargin : Scalar A
    sizeInwardDerivative sizeLoss sizeDissipation sizeMargin : Scalar A

    gammaBalance :
      _+_ A gammaInwardDerivative gammaLoss ≡ gammaReplenishment

    gammaLossPlusMarginBelowReplenishment :
      _≤_ A (_+_ A gammaLoss gammaMargin) gammaReplenishment

    gammaMarginPositive : StrictlyPositive S gammaMargin

    packetBalance :
      _+_ A packetInwardDerivative packetLoss ≡ packetSupply

    packetLossPlusMarginBelowSupply :
      _≤_ A (_+_ A packetLoss packetMargin) packetSupply

    packetMarginPositive : StrictlyPositive S packetMargin

    -- The size defining function is M²-X, so a positive inward derivative is
    -- equivalent to the original size derivative being strictly negative.
    sizeBalance :
      _+_ A sizeInwardDerivative sizeLoss ≡ sizeDissipation

    sizeLossPlusMarginBelowDissipation :
      _≤_ A (_+_ A sizeLoss sizeMargin) sizeDissipation

    sizeMarginPositive : StrictlyPositive S sizeMargin

open ThreeBoundaryPDEMarginInputs public

gammaFloorStrictlyInward :
  ∀ {A : AbsorptionArithmetic} {S : StrictMarginArithmetic A} →
  (I : ThreeBoundaryPDEMarginInputs A S) →
  StrictlyPositive S (gammaInwardDerivative I)
gammaFloorStrictlyInward {S = S} I =
  strictMarginFromBalance S
    (gammaBalance I)
    (gammaLossPlusMarginBelowReplenishment I)
    (gammaMarginPositive I)

packetOffFaceStrictlyInward :
  ∀ {A : AbsorptionArithmetic} {S : StrictMarginArithmetic A} →
  (I : ThreeBoundaryPDEMarginInputs A S) →
  StrictlyPositive S (packetInwardDerivative I)
packetOffFaceStrictlyInward {S = S} I =
  strictMarginFromBalance S
    (packetBalance I)
    (packetLossPlusMarginBelowSupply I)
    (packetMarginPositive I)

sizeCeilingStrictlyInward :
  ∀ {A : AbsorptionArithmetic} {S : StrictMarginArithmetic A} →
  (I : ThreeBoundaryPDEMarginInputs A S) →
  StrictlyPositive S (sizeInwardDerivative I)
sizeCeilingStrictlyInward {S = S} I =
  strictMarginFromBalance S
    (sizeBalance I)
    (sizeLossPlusMarginBelowDissipation I)
    (sizeMarginPositive I)

record ThreeUniversalStrictBoundarySigns
    {A : AbsorptionArithmetic}
    (S : StrictMarginArithmetic A)
    (I : ThreeBoundaryPDEMarginInputs A S) : Set where
  field
    gamma-sign : StrictlyPositive S (gammaInwardDerivative I)
    packet-off-sign : StrictlyPositive S (packetInwardDerivative I)
    size-sign : StrictlyPositive S (sizeInwardDerivative I)

open ThreeUniversalStrictBoundarySigns public

threeUniversalStrictBoundarySigns :
  ∀ {A : AbsorptionArithmetic}
    {S : StrictMarginArithmetic A} →
  (I : ThreeBoundaryPDEMarginInputs A S) →
  ThreeUniversalStrictBoundarySigns S I
threeUniversalStrictBoundarySigns I = record
  { gamma-sign = gammaFloorStrictlyInward I
  ; packet-off-sign = packetOffFaceStrictlyInward I
  ; size-sign = sizeCeilingStrictlyInward I
  }

------------------------------------------------------------------------
-- Status: the sign logic and the common strict-margin ledger are closed.  The
-- remaining PDE leaves are precisely the three quantitative supply-vs-loss
-- estimates for one common parameter tuple.
------------------------------------------------------------------------

threeBoundaryPDEMarginLevel : ProofLevel
threeBoundaryPDEMarginLevel = machineChecked
