{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanLiteralStressCoordinateRound114Exact where

------------------------------------------------------------------------
-- ROUND114: ONE PHYSICAL STRESS COORDINATE FEEDS TELESCOPE AND COMPLETION
------------------------------------------------------------------------

open import Relation.Binary.PropositionalEquality using (_≡_)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanSameFamilyStressCauchySchwingerRound109Exact as R109
import DASHI.Physics.YangMills.BalabanStressSameObjectProvenanceRound110Exact as R110
import DASHI.Physics.YangMills.BalabanCharacteristicNuclearContinuityTransportExact as Nuclear
import DASHI.Physics.YangMills.BalabanMarkedSourceNuclearCompositeFieldExact as Marked
import DASHI.Physics.YangMills.BalabanMarkedSourceCompositeStressFieldExact as StressMarked
import DASHI.Physics.YangMills.BalabanStressShellEnergyToHilbertRound112Exact as R112
import DASHI.Physics.YangMills.BalabanStressShellPartitionEnergyRound113Exact as R113
import DASHI.Physics.YangMills.YangMillsClayLiteralTopDownConstructionExact as Top

record LiteralStressCoordinate
    {C : Top.LiteralYangMillsCarriers}
    {S : Top.LiteralYangMillsSemantics C}
    (Y : Top.LiteralYangMillsConstruction C S)
    (group : Top.CompactSimpleGroup C) : Set₁ where
  field
    StressCoordinate : Set
    coordinate : StressCoordinate

    -- Three source-native views of ONE selected coordinate.
    asCMP119Cauchy : StressCoordinate → R109.SourceNativeStressScaleCauchy
    asShellPartition : StressCoordinate → R113.LiteralStressShellPartition
    asMarkedCompletion :
      StressCoordinate → R109.LiteralSchwingerStressMarkedCompletion Y group

    -- The completion of the selected CMP119 insertion must literally be the
    -- field functional of the marked completion selected by the same coordinate.
    cmp119CompletedResponse :
      let completion = asMarkedCompletion coordinate
      in
      Nuclear.Test (R109.continuityScale completion) →
      Nuclear.Value (R109.continuityScale completion)

    cauchyCompletionIsActualMarkedStressFunctional :
      let completion = asMarkedCompletion coordinate
          sources = R109.completedSources completion
          fields = StressMarked.sameCompletedMarkedSourcesGiveCompositeAndStressFields sources
      in
      cmp119CompletedResponse
      ≡ Marked.fieldFunctional (StressMarked.stressField fields)
open LiteralStressCoordinate public

asSameObjectProvenance :
  ∀ {C S}
    {Y : Top.LiteralYangMillsConstruction C S}
    {group : Top.CompactSimpleGroup C} →
  LiteralStressCoordinate Y group →
  R110.LiteralStressSameObjectProvenance Y group
asSameObjectProvenance dataSet = record
  { R110.LiteralStressSameObjectProvenance.sourceCauchy =
      asCMP119Cauchy dataSet (coordinate dataSet)
  ; R110.LiteralStressSameObjectProvenance.markedCompletion =
      asMarkedCompletion dataSet (coordinate dataSet)
  ; R110.LiteralStressSameObjectProvenance.cmp119CompletedResponse =
      cmp119CompletedResponse dataSet
  ; R110.LiteralStressSameObjectProvenance.cauchyCompletionIsActualMarkedStressFunctional =
      cauchyCompletionIsActualMarkedStressFunctional dataSet
  }

asStressCoefficientShellIdentification :
  ∀ {C S}
    {Y : Top.LiteralYangMillsConstruction C S}
    {group : Top.CompactSimpleGroup C} →
  LiteralStressCoordinate Y group →
  R112.LiteralStressCoefficientShellIdentification
asStressCoefficientShellIdentification dataSet =
  R113.asRound112StressCoefficientShellIdentification
    (asShellPartition dataSet (coordinate dataSet))

sameCoordinateCompletedResponseIsLiteralStressDerivative :
  ∀ {C S}
    {Y : Top.LiteralYangMillsConstruction C S}
    {group : Top.CompactSimpleGroup C}
    (dataSet : LiteralStressCoordinate Y group) →
  let completion = asMarkedCompletion dataSet (coordinate dataSet)
      sources = R109.completedSources completion
      stressData = StressMarked.stressData sources
  in
  cmp119CompletedResponse dataSet
  ≡ Marked.sourceDerivative stressData (Top.stressTensor Y group)
sameCoordinateCompletedResponseIsLiteralStressDerivative dataSet =
  R110.completedCMP119StressIsLiteralClayStressDerivative
    (asSameObjectProvenance dataSet)

literalStressCoordinateCompilerLevel : ProofLevel
literalStressCoordinateCompilerLevel = machineChecked

-- Central physical BIDI leaf: instantiate ONE literal differentiated CMP116
-- stress coordinate whose CMP119, shell/coefficient, and marked-completion views
-- are exactly the three views above.
literalCMP116StressCoordinateInstantiationLevel : ProofLevel
literalCMP116StressCoordinateInstantiationLevel = conditional
