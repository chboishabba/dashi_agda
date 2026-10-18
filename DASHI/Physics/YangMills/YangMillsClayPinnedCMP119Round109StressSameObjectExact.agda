{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsClayPinnedCMP119Round109StressSameObjectExact where

------------------------------------------------------------------------
-- LITERAL C / ROUND109 COMPLETED MARKED STRESS SAME-OBJECT WELD
--
-- Round109 constructs the continuum stress projection from the SAME completed
-- marked RG state and identifies it with the literal Clay stress tensor.
-- This owner exposes the exact equality transport needed by the pinned
-- common-core route without assuming that the two carrier presentations have
-- already been identified.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Relation.Binary.PropositionalEquality using (trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanSameFamilyStressCauchySchwingerRound109Exact as R109
import DASHI.Physics.YangMills.BalabanMarkedSourceNuclearCompositeFieldExact as Marked
import DASHI.Physics.YangMills.BalabanMarkedSourceCompositeStressFieldExact as StressMarked
import DASHI.Physics.YangMills.YangMillsClayLiteralTopDownConstructionExact as Top

completedMarkedStressEqualsSelectedLiteralStress :
  ∀ {C S}
    {Y : Top.LiteralYangMillsConstruction C S}
    {group : Top.CompactSimpleGroup C}
    (completion : R109.LiteralSchwingerStressMarkedCompletion Y group)
    (selectedStress : Top.StressTensor C) →
  Top.stressTensor Y group ≡ selectedStress →
  Marked.continuumComposite
    (StressMarked.stressField
      (StressMarked.sameCompletedMarkedSourcesGiveCompositeAndStressFields
        (R109.completedSources completion)))
  ≡ selectedStress
completedMarkedStressEqualsSelectedLiteralStress
    completion selectedStress literalStressIsSelected =
  trans
    (R109.literalStressIsCompletedMarkedStress completion)
    literalStressIsSelected

round109StressCompletionSameObjectTransportLevel : ProofLevel
round109StressCompletionSameObjectTransportLevel = machineChecked

-- Physical C residue: instantiate Round109 on the selected CMP119 family and
-- identify its literal stress projection with the stress tensor used by the
-- pinned Ward/common-core construction.
literalCompletedStressPinnedCommonCoreIdentificationLevel : ProofLevel
literalCompletedStressPinnedCommonCoreIdentificationLevel = conditional
