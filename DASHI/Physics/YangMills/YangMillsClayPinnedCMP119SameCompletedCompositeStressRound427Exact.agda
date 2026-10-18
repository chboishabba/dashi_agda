{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsClayPinnedCMP119SameCompletedCompositeStressRound427Exact where

------------------------------------------------------------------------
-- C / ROUND427: ROUND109 SAME COMPLETED STATE -> COMPOSITE + STRESS FIELDS
--
-- The Round109 completion already contains BOTH marked coordinates on one
-- completed RG state.  Compile both nuclear fields together and retain the
-- completed-state identity explicitly.  No parallel continuum stress object.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanSameFamilyStressCauchySchwingerRound109Exact as R109
import DASHI.Physics.YangMills.BalabanMarkedSourceNuclearCompositeFieldExact as Marked
import DASHI.Physics.YangMills.BalabanMarkedSourceCompositeStressFieldExact as Both
import DASHI.Physics.YangMills.YangMillsClayLiteralTopDownConstructionExact as Top

record SameCompletedCompositeStressFields
    {C : Top.LiteralYangMillsCarriers}
    {S : Top.LiteralYangMillsSemantics C}
    {Y : Top.LiteralYangMillsConstruction C S}
    {group : Top.CompactSimpleGroup C}
    (completion : R109.LiteralSchwingerStressMarkedCompletion Y group)
    : Set₁ where
  field
    fields :
      Both.SameFamilyCompositeStressNuclearFields
        (R109.completedSources completion)

open SameCompletedCompositeStressFields public

compileSameCompletedCompositeStress :
  ∀ {C S Y group}
    (completion :
      R109.LiteralSchwingerStressMarkedCompletion
        {C = C} {S = S} Y group) →
  SameCompletedCompositeStressFields completion
compileSameCompletedCompositeStress completion = record
  { fields =
      Both.sameCompletedMarkedSourcesGiveCompositeAndStressFields
        (R109.completedSources completion)
  }

compositeField :
  ∀ {C S Y group}
    (completion :
      R109.LiteralSchwingerStressMarkedCompletion
        {C = C} {S = S} Y group) →
  Marked.SameFamilyNuclearCompositeField
    (Both.compositeData (R109.completedSources completion))
compositeField completion =
  Both.compositeField (fields (compileSameCompletedCompositeStress completion))

stressField :
  ∀ {C S Y group}
    (completion :
      R109.LiteralSchwingerStressMarkedCompletion
        {C = C} {S = S} Y group) →
  Marked.SameFamilyNuclearCompositeField
    (Both.stressData (R109.completedSources completion))
stressField completion =
  Both.stressField (fields (compileSameCompletedCompositeStress completion))

sameCompletedState :
  ∀ {C S Y group}
    (completion :
      R109.LiteralSchwingerStressMarkedCompletion
        {C = C} {S = S} Y group) →
  Marked.completedState
    (Both.compositeData (R109.completedSources completion))
  ≡
  Marked.completedState
    (Both.stressData (R109.completedSources completion))
sameCompletedState completion =
  Both.completedStateAgreement
    (fields (compileSameCompletedCompositeStress completion))

stressFieldIsLiteralClayStress :
  ∀ {C S Y group}
    (completion :
      R109.LiteralSchwingerStressMarkedCompletion
        {C = C} {S = S} Y group) →
  Marked.continuumComposite (stressField completion)
  ≡ Top.stressTensor Y group
stressFieldIsLiteralClayStress completion =
  R109.literalStressIsCompletedMarkedStress completion

round427SameCompletedCompositeStressCompilerLevel : ProofLevel
round427SameCompletedCompositeStressCompilerLevel = machineChecked

-- Remaining C source work is not completion/topology: it is literal production
-- of the Round109 marked completion plus curvature-polynomial semantics for the
-- composite coordinate.
literalRound427SameCompletedSourceLevel : ProofLevel
literalRound427SameCompletedSourceLevel = conditional
