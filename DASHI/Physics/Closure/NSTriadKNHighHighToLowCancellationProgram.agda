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
-- Relationship: output freezing has the proved algebraic identity
-- u_p dot q = u_p dot k once resonance, transversality and bilinearity are
-- supplied; second-adjoint freezing already puts q on the frozen leg;
-- first-adjoint freezing has an exact counterexample to any primitive
-- low-frequency derivative gain and needs a Sobolev-tail, commutator, or
-- further symbol cancellation argument.
------------------------------------------------------------------------

open import Agda.Primitive using (Level; lsuc; _⊔_)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (sym; cong)

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

------------------------------------------------------------------------
-- Generic exact theorem behind u_p dot q = u_p dot k.
------------------------------------------------------------------------

record ResonantTransverseRelocationLaws
    {m v s : Level} : Set (lsuc (m ⊔ v ⊔ s)) where
  field
    Mode : Set m
    Vector : Set v
    Scalar : Set s

    addMode : Mode → Mode → Mode
    modeVector : Mode → Vector
    vectorAdd : Vector → Vector → Vector
    dot : Vector → Vector → Scalar
    scalarAdd : Scalar → Scalar → Scalar
    zero : Scalar

    modeVectorAdd : ∀ p q →
      modeVector (addMode p q)
      ≡ vectorAdd (modeVector p) (modeVector q)

    dotRightAdd : ∀ u p q →
      dot u (vectorAdd p q)
      ≡ scalarAdd (dot u p) (dot u q)

    scalarZeroLeft : ∀ x → scalarAdd zero x ≡ x

open ResonantTransverseRelocationLaws public

outputDerivativeRelocation :
  ∀ {m v s}
    (L : ResonantTransverseRelocationLaws {m} {v} {s})
    (output left right : Mode L)
    (leftVector : Vector L) →
  addMode L left right ≡ output →
  dot L leftVector (modeVector L left) ≡ zero L →
  dot L leftVector (modeVector L right)
  ≡ dot L leftVector (modeVector L output)
outputDerivativeRelocation L output left right leftVector resonance transverse
  rewrite sym (cong (modeVector L) resonance)
        | modeVectorAdd L left right
        | dotRightAdd L leftVector (modeVector L left) (modeVector L right)
        | transverse
        | scalarZeroLeft L (dot L leftVector (modeVector L right))
  = refl

record ConcreteComplexCarrierRelocationCutset {s : Level} : Set (lsuc s) where
  field
    Scalar : Set s
    repositoryModeVectorAddInstantiated : Set s
    repositoryBilinearDotRightAddInstantiated : Set s
    repositoryScalarZeroLeftInstantiated : Set s
    repositoryTransverseVelocityConsumed : Set s
    repositoryOutputRelocationObtained : Set s

open ConcreteComplexCarrierRelocationCutset public

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

outputRelocationAlgebraTheoremClosed : Bool
outputRelocationAlgebraTheoremClosed = true

outputRelocationAlgebraTheoremClosedIsTrue :
  outputRelocationAlgebraTheoremClosed ≡ true
outputRelocationAlgebraTheoremClosedIsTrue = refl

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

concreteComplexCarrierOutputRelocationClosed : Bool
concreteComplexCarrierOutputRelocationClosed = false

concreteComplexCarrierOutputRelocationClosedIsFalse :
  concreteComplexCarrierOutputRelocationClosed ≡ false
concreteComplexCarrierOutputRelocationClosedIsFalse = refl

allThreeCutoffUniformHighHighBoundsClosed : Bool
allThreeCutoffUniformHighHighBoundsClosed = false

allThreeCutoffUniformHighHighBoundsClosedIsFalse :
  allThreeCutoffUniformHighHighBoundsClosed ≡ false
allThreeCutoffUniformHighHighBoundsClosedIsFalse = refl
