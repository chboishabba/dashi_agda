{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119PinnedYMGRQFTSectorStressBridgeExact where

open import DASHI.Core.Prelude
open import Relation.Binary.PropositionalEquality using (cong; trans)

import DASHI.Physics.Foundations.SameCandidateQFTGRRecoveryExact as Weld
import DASHI.Physics.Foundations.PinnedYangMillsRecoveredQFTAttachmentExact as Recover
import DASHI.Physics.YangMills.YangMillsClayLiteralTopDownConstructionExact as Top
import DASHI.Physics.YangMills.YangMillsClayPinnedPhysicalConstructionExact as Pinned
import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119OSReconstructionExact as OSR
import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119StressCommonCoreExact as Common
import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119ConcreteLocalCExact as C
import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119LiteralStressAttachmentExact as CMP

------------------------------------------------------------------------
-- POST-MERGE SAME-OBJECT COMPILER
--
-- The YM CMP119 stress lane and the GRQFT recovery lane now share ancestry.
-- Combine, rather than duplicate, their two explicit same-object payments:
--
--   CMP119 stress = literal pinned YM stress
--   literal pinned YM construction = recovered/selected QFT construction
--
-- This yields the actual SharedStressEnergy sector object consumed by U_T.
------------------------------------------------------------------------

record CMP119PinnedYMGRQFTSectorStressBridge
    (U : Weld.UnifiedCandidate)
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
    cmp119LiteralAttachment :
      CMP.PinnedCMP119LiteralStressAttachment
        (Pinned.asLiteralYangMillsConstruction pinned)
        group inputs

    pinnedRecoveredAttachment :
      Recover.PinnedYangMillsRecoveredQFTAttachment U pinned

    qftRecovery :
      Weld.QFTRecoveryReceipt U

open CMP119PinnedYMGRQFTSectorStressBridge public

cmp119StressIsActualSelectedQFTStress :
  ∀ {U pinned group X Configuration Position CurvaturePolynomial
      LocalOperator OPECoefficient Hilbert Vector Algebra Scale Volume Root
      ContinuumFamily Core sequenceLimit limitLaws quotient division S
      osInputs reconstruction inputs}
    (bridge :
      CMP119PinnedYMGRQFTSectorStressBridge
        U pinned group
        {X = X} {Configuration = Configuration} {Position = Position}
        {CurvaturePolynomial = CurvaturePolynomial}
        {LocalOperator = LocalOperator} {OPECoefficient = OPECoefficient}
        {Hilbert = Hilbert} {Vector = Vector} {Algebra = Algebra}
        {Scale = Scale} {Volume = Volume} {Root = Root}
        {ContinuumFamily = ContinuumFamily} {Core = Core}
        {sequenceLimit = sequenceLimit} {limitLaws = limitLaws}
        {quotient = quotient} {division = division} {S = S}
        {osInputs = osInputs} {reconstruction = reconstruction}
        inputs)
    candidate regime →
  Weld.qftRegime U regime →
  C.stressTensor inputs
  ≡ Weld.actualQFTStressTensor U
      (Weld.coarseGrain U candidate regime) group
cmp119StressIsActualSelectedQFTStress
    bridge candidate regime qftAtRegime =
  trans
    (CMP.cmp119StressIsLiteralStress
      (cmp119LiteralAttachment bridge))
    (Recover.pinnedStressIsActualSelectedQFTStress
      (pinnedRecoveredAttachment bridge)
      (qftRecovery bridge)
      candidate regime qftAtRegime group)

cmp119StressSharedIsActualSelectedQFTSectorStress :
  ∀ {U pinned group X Configuration Position CurvaturePolynomial
      LocalOperator OPECoefficient Hilbert Vector Algebra Scale Volume Root
      ContinuumFamily Core sequenceLimit limitLaws quotient division S
      osInputs reconstruction inputs}
    (bridge :
      CMP119PinnedYMGRQFTSectorStressBridge
        U pinned group
        {X = X} {Configuration = Configuration} {Position = Position}
        {CurvaturePolynomial = CurvaturePolynomial}
        {LocalOperator = LocalOperator} {OPECoefficient = OPECoefficient}
        {Hilbert = Hilbert} {Vector = Vector} {Algebra = Algebra}
        {Scale = Scale} {Volume = Volume} {Root = Root}
        {ContinuumFamily = ContinuumFamily} {Core = Core}
        {sequenceLimit = sequenceLimit} {limitLaws = limitLaws}
        {quotient = quotient} {division = division} {S = S}
        {osInputs = osInputs} {reconstruction = reconstruction}
        inputs)
    candidate regime →
  Weld.qftRegime U regime →
  Weld.qftSectorStressToShared U group (C.stressTensor inputs)
  ≡ Weld.actualQFTSectorStressShared U
      (Weld.coarseGrain U candidate regime) group
cmp119StressSharedIsActualSelectedQFTSectorStress
    {U = U} {group = group}
    bridge candidate regime qftAtRegime =
  cong
    (Weld.qftSectorStressToShared U group)
    (cmp119StressIsActualSelectedQFTStress
      bridge candidate regime qftAtRegime)

cmp119StressChargeGeneratesSelectedQFTHamiltonian :
  ∀ {U pinned group X Configuration Position CurvaturePolynomial
      LocalOperator OPECoefficient Hilbert Vector Algebra Scale Volume Root
      ContinuumFamily Core sequenceLimit limitLaws quotient division S
      osInputs reconstruction inputs}
    (bridge :
      CMP119PinnedYMGRQFTSectorStressBridge
        U pinned group
        {X = X} {Configuration = Configuration} {Position = Position}
        {CurvaturePolynomial = CurvaturePolynomial}
        {LocalOperator = LocalOperator} {OPECoefficient = OPECoefficient}
        {Hilbert = Hilbert} {Vector = Vector} {Algebra = Algebra}
        {Scale = Scale} {Volume = Volume} {Root = Root}
        {ContinuumFamily = ContinuumFamily} {Core = Core}
        {sequenceLimit = sequenceLimit} {limitLaws = limitLaws}
        {quotient = quotient} {division = division} {S = S}
        {osInputs = osInputs} {reconstruction = reconstruction}
        inputs)
    candidate regime →
  Weld.qftRegime U regime →
  Common.stressCharge (C.stressCommonCore inputs)
    (Top.stressTensor (Pinned.asLiteralYangMillsConstruction pinned) group)
  ≡
  Top.hamiltonian
    (Weld.qftTarget U (Weld.coarseGrain U candidate regime))
    group
cmp119StressChargeGeneratesSelectedQFTHamiltonian
    bridge candidate regime qftAtRegime =
  trans
    (CMP.cmp119StressChargeGeneratesLiteralHamiltonian
      (cmp119LiteralAttachment bridge))
    (cong
      (λ construction → Top.hamiltonian construction group)
      (Recover.pinnedConstructionIsSelectedQFTTarget
        (pinnedRecoveredAttachment bridge)
        (qftRecovery bridge)
        candidate regime qftAtRegime))

secondCMP119ToSharedStressTheoremRequired : Bool
secondCMP119ToSharedStressTheoremRequired = false

secondCMP119ToSharedStressTheoremRequiredIsFalse :
  secondCMP119ToSharedStressTheoremRequired ≡ false
secondCMP119ToSharedStressTheoremRequiredIsFalse = refl
