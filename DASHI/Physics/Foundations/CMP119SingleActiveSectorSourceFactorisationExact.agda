{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119SingleActiveSectorSourceFactorisationExact where

open import DASHI.Core.Prelude
open import DASHI.Physics.YangMills.CompactLieProofLevel
open import Relation.Binary.PropositionalEquality using (trans)

import DASHI.Physics.Foundations.SameCandidateQFTGRRecoveryExact as Weld
import DASHI.Physics.Foundations.SharedEffectiveSourceRecoveryExact as Shared
import DASHI.Physics.Foundations.GRQFTActiveGaugeSectorTotalizationExact as Active
import DASHI.Physics.Foundations.CMP119PinnedYMGRQFTSectorStressBridgeExact as CMPBridge
import DASHI.Physics.YangMills.YangMillsClayLiteralTopDownConstructionExact as Top
import DASHI.Physics.YangMills.YangMillsClayPinnedPhysicalConstructionExact as Pinned
import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119ConcreteLocalCExact as C

------------------------------------------------------------------------
-- SINGLE ACTIVE PINNED YM SECTOR -> QFT SOURCE FACTORISATION
--
-- For one physically selected compact-simple YM sector, the active-sector
-- predicate can be the identity fibre of that group.  This is intentionally
-- different from Clay's universal theorem parameter over all compact-simple G.
--
-- Once the application proves that its declared qftTotalStressShared is this
-- selected sector and supplies legacy aggregation compatibility, the existing
-- CMP119 same-object bridge makes the QFT source factorisation automatic.
------------------------------------------------------------------------

singlePinnedGaugeSectorSelection :
  ∀ {U : Weld.UnifiedCandidate} →
  Top.CompactSimpleGroup (Weld.qftCarriers U) →
  Active.PhysicalGaugeSectorSelection U
singlePinnedGaugeSectorSelection group = record
  { Active.PhysicalGaugeSectorSelection.ActiveSector =
      λ _ candidateGroup → candidateGroup ≡ group
  ; Active.PhysicalGaugeSectorSelection.selectedGroup =
      λ _ → group
  ; Active.PhysicalGaugeSectorSelection.selectedGroupIsActive =
      λ _ → refl
  }

record CMP119SingleActiveSectorSourceInputs
    (U : Weld.UnifiedCandidate)
    (source : Shared.SharedEffectiveSourceTheory U)
    (pinned :
      Pinned.PinnedYangMillsConstruction
        {C = Weld.qftCarriers U}
        (Weld.qftSemantics U))
    (group : Top.CompactSimpleGroup (Weld.qftCarriers U))
    {X Configuration Position CurvaturePolynomial LocalOperator OPECoefficient
     Hilbert Vector Algebra Scale Volume Root ContinuumFamily Core
     sequenceLimit limitLaws quotient division S osInputs reconstruction}
    (inputs :
      C.PinnedCMP119ConcreteLocalCInputs
        (Top.CompactSimpleGroup (Weld.qftCarriers U))
        X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient (Top.StressTensor (Weld.qftCarriers U))
        Hilbert Vector (Top.Hamiltonian (Weld.qftCarriers U)) Algebra
        Scale Volume Root ContinuumFamily Core
        {sequenceLimit = sequenceLimit}
        {limitLaws = limitLaws} {quotient = quotient} {division = division}
        {S = S} osInputs reconstruction group) : Set₁ where
  field
    stressBridge :
      CMPBridge.CMP119PinnedYMGRQFTSectorStressBridge
        U pinned group inputs

    totalization :
      Active.SingleActiveGaugeSectorTotalization
        (singlePinnedGaugeSectorSelection group)

    effectiveSourceIsCMP119SharedStress :
      ∀ candidate regime →
      Weld.qftRegime U regime →
      Shared.effectiveSource source
        (Weld.coarseGrain U candidate regime) regime
      ≡
      Weld.qftSectorStressToShared U group
        (C.stressTensor inputs)

open CMP119SingleActiveSectorSourceInputs public

cmp119SingleActiveSectorBuildsQFTSourceFactorisation :
  ∀ {U : Weld.UnifiedCandidate}
    {source : Shared.SharedEffectiveSourceTheory U}
    {pinned :
      Pinned.PinnedYangMillsConstruction
        {C = Weld.qftCarriers U}
        (Weld.qftSemantics U)}
    {group : Top.CompactSimpleGroup (Weld.qftCarriers U)}
    {X Configuration Position CurvaturePolynomial LocalOperator OPECoefficient
     Hilbert Vector Algebra Scale Volume Root ContinuumFamily Core
     sequenceLimit limitLaws quotient division S osInputs reconstruction}
    {inputs :
      C.PinnedCMP119ConcreteLocalCInputs
        (Top.CompactSimpleGroup (Weld.qftCarriers U))
        X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient (Top.StressTensor (Weld.qftCarriers U))
        Hilbert Vector (Top.Hamiltonian (Weld.qftCarriers U)) Algebra
        Scale Volume Root ContinuumFamily Core
        {sequenceLimit = sequenceLimit}
        {limitLaws = limitLaws} {quotient = quotient} {division = division}
        {S = S} osInputs reconstruction group} →
  CMP119SingleActiveSectorSourceInputs
    U source pinned group inputs →
  Shared.QFTSourceFactorisation source
cmp119SingleActiveSectorBuildsQFTSourceFactorisation
    {U = U} {source = source} {group = group}
    sourceInputs =
  Active.singleActiveSectorQFTSourceFactorisation
    source
    (singlePinnedGaugeSectorSelection group)
    (totalization sourceInputs)
    (λ candidate regime qftAtRegime →
      trans
        (effectiveSourceIsCMP119SharedStress
          sourceInputs candidate regime qftAtRegime)
        (CMPBridge.cmp119StressSharedIsActualSelectedQFTSectorStress
          (stressBridge sourceInputs)
          candidate regime qftAtRegime))

singleSectorCompilerDoesNotManufactureDeclaredTotal : Bool
singleSectorCompilerDoesNotManufactureDeclaredTotal = false

singleSectorCompilerDoesNotManufactureDeclaredTotalIsFalse :
  singleSectorCompilerDoesNotManufactureDeclaredTotal ≡ false
singleSectorCompilerDoesNotManufactureDeclaredTotalIsFalse = refl

singleSectorCompilerLevel : ProofLevel
singleSectorCompilerLevel = machineChecked
