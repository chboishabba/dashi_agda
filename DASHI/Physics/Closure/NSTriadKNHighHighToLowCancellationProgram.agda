module DASHI.Physics.Closure.NSTriadKNHighHighToLowCancellationProgram where

------------------------------------------------------------------------
-- PROVENANCE
-- Authors: Tosio Kato; Gustavo Ponce.
-- Title: "Commutator estimates and the Euler and Navier-Stokes equations".
-- Venue/year: Communications on Pure and Applied Mathematics 41 (1988),
-- 891--907.
-- DOI: 10.1002/cpa.3160410704.
-- Uses: the general multiplier-commutator mechanism as a fallback route.
-- Relationship: does not itself prove the repository's discrete orbit-shell
-- cancellation or supply a numerical separation threshold.
--
-- Authors: DASHI repository contributors.
-- Title: "Frozen-leg high-high-to-low cancellation audit".
-- Venue/year: DASHI formal development, 2026.
-- DOI: not applicable; the leg-by-leg conclusion is repository-original.
-- Uses: k = p + q, p dot u_p = 0, the literal derivative factor q,
-- and the exact frozen-leg derivative ledger.
-- Relationship: output freezing has the exact identity u_p dot q = u_p dot k;
-- second-adjoint freezing already puts q on the frozen leg; first-adjoint
-- freezing has no comparable primitive low-frequency gain and needs a
-- Sobolev-tail, commutator, or further symbol cancellation argument.
------------------------------------------------------------------------

open import Agda.Primitive using (Level; lsuc)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Closure.NSTriadKNTaoFrozenLegParaproductProgram as Tao

data GainMechanism : Set where
  incompressibilityRelocation
  derivativeAlreadyFrozen
  sobolevTailPayment
  multiplierCommutatorGain
  noPrimitiveLowGain : GainMechanism

gainMechanism : Tao.FrozenLeg → GainMechanism
gainMechanism Tao.freezeOutput = incompressibilityRelocation
gainMechanism Tao.freezeLeft = noPrimitiveLowGain
gainMechanism Tao.freezeRight = derivativeAlreadyFrozen

record FrozenLegGainReceipt : Set where
  constructor receipt
  field
    outputUsesIncompressibility :
      gainMechanism Tao.freezeOutput ≡ incompressibilityRelocation
    firstAdjointHasNoPrimitiveLowGain :
      gainMechanism Tao.freezeLeft ≡ noPrimitiveLowGain
    secondAdjointDerivativeIsFrozen :
      gainMechanism Tao.freezeRight ≡ derivativeAlreadyFrozen

open FrozenLegGainReceipt public

frozenLegGainReceipt : FrozenLegGainReceipt
frozenLegGainReceipt = receipt refl refl refl

record ExactOutputRelocationLaw {m v s : Level} : Set (lsuc (m Level.⊔ v Level.⊔ s)) where
  field
    Mode : Set m
    Vector : Set v
    Scalar : Set s

    addMode : Mode → Mode → Mode
    dot : Vector → Mode → Scalar
    zero : Scalar

    output left right : Mode
    leftVector : Vector

    resonance : addMode left right ≡ output
    leftTransverse : dot leftVector left ≡ zero

    derivativeRelocationIdentity :
      dot leftVector right ≡ dot leftVector output

open ExactOutputRelocationLaw public

record HighHighToLowAnalyticCutset {s : Level} : Set (lsuc s) where
  field
    Scalar : Set s

    outputCancellationRatioBound : Set s
    outputOrderedSwapCancellationRatioBound : Set s
    secondAdjointDirectFrozenDerivativeBound : Set s

    firstAdjointProjectedHighDerivativeBound : Set s
    firstAdjointSobolevTailBound : Set s
    firstAdjointMultiplierCommutatorBound : Set s
    firstAdjointSelectedMechanism : GainMechanism

    nearClassNoSeparatedGainNeeded : Set s
    transitionClassFixedOverlap : Set s
    repositoryFarGapThresholdDerived : Set s

    outputGainUniformInCutoff : Set s
    firstAdjointGainUniformInCutoff : Set s
    secondAdjointGainUniformInCutoff : Set s

open HighHighToLowAnalyticCutset public

outputHighHighToLowStructuralGainIdentified : Bool
outputHighHighToLowStructuralGainIdentified = true

outputHighHighToLowStructuralGainIdentifiedIsTrue :
  outputHighHighToLowStructuralGainIdentified ≡ true
outputHighHighToLowStructuralGainIdentifiedIsTrue = refl

secondAdjointStructuralLowDerivativeIdentified : Bool
secondAdjointStructuralLowDerivativeIdentified = true

secondAdjointStructuralLowDerivativeIdentifiedIsTrue :
  secondAdjointStructuralLowDerivativeIdentified ≡ true
secondAdjointStructuralLowDerivativeIdentifiedIsTrue = refl

firstAdjointPrimitiveLowGainAvailable : Bool
firstAdjointPrimitiveLowGainAvailable = false

firstAdjointPrimitiveLowGainAvailableIsFalse :
  firstAdjointPrimitiveLowGainAvailable ≡ false
firstAdjointPrimitiveLowGainAvailableIsFalse = refl

allThreeCutoffUniformHighHighBoundsClosed : Bool
allThreeCutoffUniformHighHighBoundsClosed = false

allThreeCutoffUniformHighHighBoundsClosedIsFalse :
  allThreeCutoffUniformHighHighBoundsClosed ≡ false
allThreeCutoffUniformHighHighBoundsClosedIsFalse = refl
