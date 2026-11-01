module DASHI.Physics.YangMills.BalabanPath4SU2WilsonGaugeOpenFoldExact where

open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational using (0ℚ; _+_)
open import Relation.Binary.PropositionalEquality using (trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanPath4SU2PhysicalTangentExact
open import DASHI.Physics.YangMills.BalabanPath4SU2LiteralPlaquetteLiftExact using
  (literalWilsonHessianPositivePlaneFold)
open import DASHI.Physics.YangMills.BalabanPath4SU2PeriodicHodgeProducerExact using
  (literalGaugeFixingEnergy; physicalPeriodicReferenceDifferenceEnergy)
open import DASHI.Physics.YangMills.BalabanConfiguredSide4PeriodicOpenEnergySeamExact
open import DASHI.Physics.YangMills.BalabanPath4SU2PeriodicReferenceHodgeExact using
  (literalWilsonGaugeEqualsPeriodicDifferenceEnergy)

hodgeRightHandSideMatchesPhysicalReferenceDifferenceEnergyWithBoundary :
  ∀ tangent →
  physicalPeriodicReferenceDifferenceEnergy tangent
  ≡ physicalReferenceDifferenceEnergy tangent
    + physicalPeriodicWrapEnergy tangent
hodgeRightHandSideMatchesPhysicalReferenceDifferenceEnergyWithBoundary =
  physicalPeriodicDifferenceOpenPlusWrap

literalWilsonGaugeEqualsPhysicalDifferencePlusBoundary : ∀ tangent →
  literalWilsonHessianPositivePlaneFold tangent
  + literalGaugeFixingEnergy tangent
  ≡ physicalReferenceDifferenceEnergy tangent
    + physicalPeriodicWrapEnergy tangent
literalWilsonGaugeEqualsPhysicalDifferencePlusBoundary tangent =
  trans
    (literalWilsonGaugeEqualsPeriodicDifferenceEnergy tangent)
    (physicalPeriodicDifferenceOpenPlusWrap tangent)

hodgeRightHandSideMatchesPhysicalReferenceDifferenceEnergyOnWrapFreeFields :
  ∀ tangent →
  physicalPeriodicWrapEnergy tangent ≡ 0ℚ →
  physicalPeriodicReferenceDifferenceEnergy tangent
  ≡ physicalReferenceDifferenceEnergy tangent
hodgeRightHandSideMatchesPhysicalReferenceDifferenceEnergyOnWrapFreeFields =
  hodgeRightHandSideMatchesPhysicalReferenceDifferenceEnergy

literalWilsonGaugeOpenFoldWithBoundaryLevel : ProofLevel
literalWilsonGaugeOpenFoldWithBoundaryLevel = machineChecked

unconditionalBoundaryFreeOpenFoldLevel : ProofLevel
unconditionalBoundaryFreeOpenFoldLevel = conditional
