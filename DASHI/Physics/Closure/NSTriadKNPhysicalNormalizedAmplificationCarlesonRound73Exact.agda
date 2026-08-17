module DASHI.Physics.Closure.NSTriadKNPhysicalNormalizedAmplificationCarlesonRound73Exact where

------------------------------------------------------------------------
-- ROUND73 / PHYSICAL NORMALIZED AMPLIFICATION -> CARLESON NODE
--
-- This is the direct same-object composition of the Round73 concentration and
-- funding lanes.  A PhysicalNormalizedAmplificationWitness already contains:
--
--   * the SAME critical-ratio step and excess mu;
--   * the SAME Round62 structured atom list;
--   * the SAME exact triadic remainder identity;
--   * a normalized source factorization W <= 1;
--   * an explicit physical charge Q equal to overlayCharge.
--
-- The normalized concentration theorem gives mu^2 <= Q.  The square-funding
-- compiler turns that into a SquareChargedAmplificationEvent, and the Carleson
-- bridge turns exactly that event into one FundedNode.
--
-- Therefore the propagation layer cannot independently choose another floor or
-- charge: its node is definitionally
--
--      floor  = mu^2,
--      charge = physicalCharge.
--
-- The remaining PDE theorem is solely to produce a duplicate-free/additive
-- physical family of these nodes whose cumulative square floors outrun the one
-- finite energy budget.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; 0ℚ; _≤_; _<_)
import Data.Rational.Properties as ℚP
open import Relation.Binary.PropositionalEquality using (cong; subst; sym)
open import Relation.Nullary.Negation.Core using (¬_)

import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as L2
import DASHI.Physics.Closure.NSTriadKNCriticalAmplificationForcesRemainderRound69Exact as Amplification
import DASHI.Physics.Closure.NSTriadKNCriticalRatioNormalizationRound63Exact as C1
import DASHI.Physics.Closure.NSTriadKNLocalizedPDEStructuredAtomsRound62Exact as Structured
import DASHI.Physics.Closure.NSTriadKNStructuredTriadicFactorizationOverlayRound72Exact as Overlay
import DASHI.Physics.Closure.NSTriadKNPhysicalNormalizedOverlayFundingBridgeRound73Exact as Physical
import DASHI.Physics.Closure.NSTriadKNSquareChargeFundingCompilerRound73Exact as Square
import DASHI.Physics.Closure.NSTriadKNPhysicalCarlesonFundingRound73Exact as Carleson
import DASHI.Physics.Closure.NSTriadKNSquareChargeCarlesonBridgeRound73Exact as Bridge

physicalNormalizedWitnessAsCarlesonNode :
  ∀ {balances block}
    {positiveBlock : C1.PositiveCriticalBlockScale balances block}
    {step : Amplification.CriticalRatioStepDecomposition positiveBlock}
    {n mu atoms overlay} →
  Physical.PhysicalNormalizedAmplificationWitness step n mu atoms overlay →
  Carleson.FundedNode
physicalNormalizedWitnessAsCarlesonNode witness =
  Bridge.squareEventAsFundedNode
    (Physical.normalizedWitnessAsSquareChargedEvent witness)

physicalNormalizedNodeFloorExact :
  ∀ {balances block}
    {positiveBlock : C1.PositiveCriticalBlockScale balances block}
    {step : Amplification.CriticalRatioStepDecomposition positiveBlock}
    {n mu atoms overlay}
    (witness : Physical.PhysicalNormalizedAmplificationWitness
      step n mu atoms overlay) →
  Carleson.floor (physicalNormalizedWitnessAsCarlesonNode witness)
  ≡ L2.square mu
physicalNormalizedNodeFloorExact witness = refl

physicalNormalizedNodeChargeExact :
  ∀ {balances block}
    {positiveBlock : C1.PositiveCriticalBlockScale balances block}
    {step : Amplification.CriticalRatioStepDecomposition positiveBlock}
    {n mu atoms overlay}
    (witness : Physical.PhysicalNormalizedAmplificationWitness
      step n mu atoms overlay) →
  Carleson.charge (physicalNormalizedWitnessAsCarlesonNode witness)
  ≡ Physical.physicalCharge witness
physicalNormalizedNodeChargeExact witness = refl

physicalNormalizedNodeFloorBelowCharge :
  ∀ {balances block}
    {positiveBlock : C1.PositiveCriticalBlockScale balances block}
    {step : Amplification.CriticalRatioStepDecomposition positiveBlock}
    {n mu atoms overlay}
    (witness : Physical.PhysicalNormalizedAmplificationWitness
      step n mu atoms overlay) →
  L2.square mu ≤ Physical.physicalCharge witness
physicalNormalizedNodeFloorBelowCharge witness =
  Physical.normalizedWitnessSquareBelowPhysicalCharge witness

record ErasedPhysicalNormalizedNode : Set where
  constructor erased-physical-normalized-node
  field
    amplitude : ℚ
    physicalCharge : ℚ
    physicalChargeNonnegative : 0ℚ ≤ physicalCharge
    squareBelowPhysicalCharge : L2.square amplitude ≤ physicalCharge

open ErasedPhysicalNormalizedNode public

erasePhysicalNormalizedWitness :
  ∀ {balances block}
    {positiveBlock : C1.PositiveCriticalBlockScale balances block}
    {step : Amplification.CriticalRatioStepDecomposition positiveBlock}
    {n mu atoms overlay} →
  Physical.PhysicalNormalizedAmplificationWitness step n mu atoms overlay →
  ErasedPhysicalNormalizedNode
erasePhysicalNormalizedWitness {mu = mu} witness =
  erased-physical-normalized-node
    mu
    (Physical.physicalCharge witness)
    (Physical.physicalChargeNonnegative witness)
    (Physical.normalizedWitnessSquareBelowPhysicalCharge witness)

erasedAsCarlesonNode : ErasedPhysicalNormalizedNode → Carleson.FundedNode
erasedAsCarlesonNode node =
  Carleson.funded-node
    (L2.square (amplitude node))
    (physicalCharge node)
    (L2.squareNonnegative (amplitude node))
    (squareBelowPhysicalCharge node)

erasedNodesAsCarlesonNodes :
  List ErasedPhysicalNormalizedNode → List Carleson.FundedNode
erasedNodesAsCarlesonNodes [] = []
erasedNodesAsCarlesonNodes (node ∷ rest) =
  erasedAsCarlesonNode node ∷ erasedNodesAsCarlesonNodes rest

record AdditivePhysicalNormalizedFamily
    (nodes : List ErasedPhysicalNormalizedNode)
    (energy : ℚ) : Set where
  field
    energyNonnegative : 0ℚ ≤ energy
    totalPhysicalChargeBelowEnergy :
      Carleson.sumCharges (erasedNodesAsCarlesonNodes nodes) ≤ energy

open AdditivePhysicalNormalizedFamily public

additivePhysicalNormalizedFamilyAsCarlesonBudget :
  ∀ {nodes energy} →
  AdditivePhysicalNormalizedFamily nodes energy →
  Carleson.PhysicalCarlesonBudget
    (erasedNodesAsCarlesonNodes nodes) energy
additivePhysicalNormalizedFamilyAsCarlesonBudget family = record
  { budgetNonnegative = energyNonnegative family
  ; subtreeChargeWithinBudget = totalPhysicalChargeBelowEnergy family
  }

physicalNormalizedFloorPrefixAboveEnergyImpossible :
  ∀ {nodes energy} →
  energy < Carleson.sumFloors (erasedNodesAsCarlesonNodes nodes) →
  ¬ AdditivePhysicalNormalizedFamily nodes energy
physicalNormalizedFloorPrefixAboveEnergyImpossible excess family =
  Carleson.floorPrefixAboveBudgetRefutesCarlesonFunding
    excess
    (additivePhysicalNormalizedFamilyAsCarlesonBudget family)

round73PhysicalNormalizedWitnessCompilesToCarlesonNode : Bool
round73PhysicalNormalizedWitnessCompilesToCarlesonNode = true

round73CarlesonNodeFloorIsExactlyAmplificationSquare : Bool
round73CarlesonNodeFloorIsExactlyAmplificationSquare = true

round73PhysicalAdditiveNormalizedDescendantFamilyConstructed : Bool
round73PhysicalAdditiveNormalizedDescendantFamilyConstructed = false

round73PhysicalNormalizedWitnessCompilesToCarlesonNodeIsTrue :
  round73PhysicalNormalizedWitnessCompilesToCarlesonNode ≡ true
round73PhysicalNormalizedWitnessCompilesToCarlesonNodeIsTrue = refl

round73PhysicalAdditiveNormalizedDescendantFamilyConstructedIsFalse :
  round73PhysicalAdditiveNormalizedDescendantFamilyConstructed ≡ false
round73PhysicalAdditiveNormalizedDescendantFamilyConstructedIsFalse = refl
