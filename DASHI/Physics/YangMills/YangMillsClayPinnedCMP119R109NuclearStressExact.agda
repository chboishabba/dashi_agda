{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsClayPinnedCMP119R109NuclearStressExact where

------------------------------------------------------------------------
-- C / ROUND109 COMPLETION -> NUCLEAR-CONTINUOUS LITERAL CLAY STRESS
--
-- Round109 already carries both completed marked source coordinates and proves
-- that the completed marked stress composite is the literal Clay stress tensor.
-- The generic Round87 compiler therefore supplies the stress nuclear field
-- without another continuum-stress construction.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (trans)
open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanSameFamilyStressCauchySchwingerRound109Exact as R109
import DASHI.Physics.YangMills.BalabanMarkedSourceNuclearCompositeFieldExact as Marked
import DASHI.Physics.YangMills.BalabanMarkedSourceCompositeStressFieldExact as StressMarked
import DASHI.Physics.YangMills.YangMillsClayLiteralTopDownConstructionExact as Top

r109StressNuclearField :
  ∀ {C S}
    {Y : Top.LiteralYangMillsConstruction C S}
    {group : Top.CompactSimpleGroup C}
    (completion : R109.LiteralSchwingerStressMarkedCompletion Y group) →
  Marked.SameFamilyNuclearCompositeField
    (StressMarked.stressData (R109.completedSources completion))
r109StressNuclearField completion =
  StressMarked.stressField
    (StressMarked.sameCompletedMarkedSourcesGiveCompositeAndStressFields
      (R109.completedSources completion))

r109StressFieldIsLiteralClayStress :
  ∀ {C S}
    {Y : Top.LiteralYangMillsConstruction C S}
    {group : Top.CompactSimpleGroup C}
    (completion : R109.LiteralSchwingerStressMarkedCompletion Y group) →
  Marked.continuumComposite (r109StressNuclearField completion)
  ≡ Top.stressTensor Y group
r109StressFieldIsLiteralClayStress =
  R109.literalStressIsCompletedMarkedStress

r109StressFunctionalIsLiteralSourceDerivative :
  ∀ {C S}
    {Y : Top.LiteralYangMillsConstruction C S}
    {group : Top.CompactSimpleGroup C}
    (completion : R109.LiteralSchwingerStressMarkedCompletion Y group) →
  Marked.fieldFunctional (r109StressNuclearField completion)
  ≡
  Marked.sourceDerivative
    (StressMarked.stressData (R109.completedSources completion))
    (Top.stressTensor Y group)
r109StressFunctionalIsLiteralSourceDerivative completion =
  trans
    (Marked.fieldFunctionalIsLiteralSourceDerivative
      (r109StressNuclearField completion))
    (congDerivative
      (r109StressFieldIsLiteralClayStress completion))
  where
  congDerivative :
    ∀ {left right} →
    left ≡ right →
    Marked.sourceDerivative
      (StressMarked.stressData (R109.completedSources completion)) left
    ≡
    Marked.sourceDerivative
      (StressMarked.stressData (R109.completedSources completion)) right
  congDerivative refl =
    refl

r109StressNuclearCompilerLevel : ProofLevel
r109StressNuclearCompilerLevel =
  StressMarked.sameCompletedCompositeStressFieldCompilerLevel

-- Stress distribution existence/continuity is no longer a separate C leaf once
-- Round109 completion is inhabited.  Remaining stress work is finite insertion
-- same-object identification plus Ward/local-core/closure analysis.
literalR109StressCompletionLevel : ProofLevel
literalR109StressCompletionLevel = conditional
