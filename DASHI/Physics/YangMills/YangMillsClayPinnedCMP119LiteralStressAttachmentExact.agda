{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsClayPinnedCMP119LiteralStressAttachmentExact where

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)
open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.YangMillsClayLiteralTopDownConstructionExact as Top
import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119OSReconstructionExact as OSR
import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119StressCommonCoreExact as Common
import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119ConcreteLocalCExact as C

------------------------------------------------------------------------
-- CMP119 C STRESS -> LITERAL CLAY STRESS: EXPLICIT SAME-OBJECT ADAPTER
--
-- The newer CMP119 A/B/C lane and PinnedYangMillsConstruction both use
-- "pinned", but names do not identify carriers. A consumer supplies exactly
-- the stress and Hamiltonian same-object equalities it actually needs.
------------------------------------------------------------------------

record PinnedCMP119LiteralStressAttachment
    {Carriers : Top.LiteralYangMillsCarriers}
    {Semantics : Top.LiteralYangMillsSemantics Carriers}
    (Y : Top.LiteralYangMillsConstruction Carriers Semantics)
    (group : Top.CompactSimpleGroup Carriers)
    {X Configuration Position CurvaturePolynomial LocalOperator OPECoefficient
     Hilbert Vector Algebra Scale Volume Root ContinuumFamily Core
     sequenceLimit limitLaws quotient division S osInputs reconstruction}
    (inputs :
      C.PinnedCMP119ConcreteLocalCInputs
        (Top.CompactSimpleGroup Carriers)
        X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient (Top.StressTensor Carriers)
        Hilbert Vector (Top.Hamiltonian Carriers) Algebra
        Scale Volume Root ContinuumFamily Core
        {sequenceLimit = sequenceLimit}
        {limitLaws = limitLaws} {quotient = quotient} {division = division}
        {S = S} osInputs reconstruction group) : Set₁ where
  field
    cmp119StressIsLiteralStress :
      C.stressTensor inputs ≡ Top.stressTensor Y group

    cmp119HamiltonianIsLiteralHamiltonian :
      OSR.reconstructedHamiltonian reconstruction group
      ≡ Top.hamiltonian Y group

open PinnedCMP119LiteralStressAttachment public

cmp119StressChargeGeneratesLiteralHamiltonian :
  ∀ {Carriers Semantics Y group X Configuration Position CurvaturePolynomial
      LocalOperator OPECoefficient Hilbert Vector Algebra Scale Volume Root
      ContinuumFamily Core sequenceLimit limitLaws quotient division S
      osInputs reconstruction}
    {inputs :
      C.PinnedCMP119ConcreteLocalCInputs
        (Top.CompactSimpleGroup Carriers)
        X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient (Top.StressTensor Carriers)
        Hilbert Vector (Top.Hamiltonian Carriers) Algebra
        Scale Volume Root ContinuumFamily Core
        {sequenceLimit = sequenceLimit}
        {limitLaws = limitLaws} {quotient = quotient} {division = division}
        {S = S} osInputs reconstruction group}
    (attachment :
      PinnedCMP119LiteralStressAttachment
        {Carriers = Carriers} {Semantics = Semantics}
        Y group inputs) →
  Common.stressCharge (C.stressCommonCore inputs) (Top.stressTensor Y group)
  ≡ Top.hamiltonian Y group
cmp119StressChargeGeneratesLiteralHamiltonian
    {inputs = inputs}
    attachment =
  trans
    (cong
      (Common.stressCharge (C.stressCommonCore inputs))
      (sym (cmp119StressIsLiteralStress attachment)))
    (trans
      (C.stressChargeGeneratesPinnedHamiltonian inputs)
      (cmp119HamiltonianIsLiteralHamiltonian attachment))

pinnedCMP119LiteralStressAttachmentCompilerLevel : ProofLevel
pinnedCMP119LiteralStressAttachmentCompilerLevel = machineChecked

sameObjectAttachmentManufacturedFromPinnedName : Bool
sameObjectAttachmentManufacturedFromPinnedName = false

sameObjectAttachmentManufacturedFromPinnedNameIsFalse :
  sameObjectAttachmentManufacturedFromPinnedName ≡ false
sameObjectAttachmentManufacturedFromPinnedNameIsFalse = refl
