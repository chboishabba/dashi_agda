{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.YMExactOSPullbackM4GateAdapterExact where

------------------------------------------------------------------------
-- YM MASS-GAP GATE M4 / EXACT OS PULLBACK ROUTE
--
-- The historical Round15-era machinery already proves that an exact physical
-- pullback of the blocked OS quadratic form preserves reflection positivity,
-- and the blocking bridge identifies that pullback with the repository's
-- reflection-positive blocking interface once both use the same fine OS form.
--
-- The physical `ExactOSPullbackData` itself remains an input.  This module only
-- transports an actual pullback package into the abstract M4-left gate after an
-- explicit same-proposition weld.  The alternative M4 transfer-intertwining
-- route remains available independently in the gate package.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayExactOSPullbackRecombinationExact as Pullback
import DASHI.Physics.YangMills.BalabanClayMassGapGatePackageExact as Gates

record ExactOSPullbackM4GateWeld
    {Original Blocked Scalar : Set}
    (pullbackData : Pullback.ExactOSPullbackData Original Blocked Scalar)
    (gates : Gates.ClayMassGapGatePropositions) : Set₁ where
  field
    m4IsExactPhysicalOSPullback :
      Gates.M4ExactOSPullback gates
      ≡ Pullback.ExactOSPullbackData Original Blocked Scalar

open ExactOSPullbackM4GateWeld public

exactOSPullbackPaysM4Left :
  ∀ {Original Blocked Scalar gates}
    {pullbackData : Pullback.ExactOSPullbackData Original Blocked Scalar} →
  ExactOSPullbackM4GateWeld pullbackData gates →
  Gates.M4ExactOSPullback gates
exactOSPullbackPaysM4Left {pullbackData = pullbackData} weld =
  subst
    (λ P → P)
    (sym (m4IsExactPhysicalOSPullback weld))
    pullbackData

exactOSPullbackPaysM4 :
  ∀ {Original Blocked Scalar gates}
    {pullbackData : Pullback.ExactOSPullbackData Original Blocked Scalar} →
  ExactOSPullbackM4GateWeld pullbackData gates →
  Gates._or_
    (Gates.M4ExactOSPullback gates)
    (Gates.M4TransferIntertwining gates)
exactOSPullbackPaysM4 weld = Gates.leftRoute (exactOSPullbackPaysM4Left weld)

exactOSPullbackM4TransportCompilerLevel : ProofLevel
exactOSPullbackM4TransportCompilerLevel = machineChecked

physicalExactOSPullbackConstructionLevel : ProofLevel
physicalExactOSPullbackConstructionLevel =
  Pullback.physicalPullbackConstructionInputsLevel

exactOSPullbackM4SamePropositionWeldLevel : ProofLevel
exactOSPullbackM4SamePropositionWeldLevel = conditional
