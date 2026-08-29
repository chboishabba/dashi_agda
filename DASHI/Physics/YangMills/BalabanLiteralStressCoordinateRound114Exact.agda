{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanLiteralStressCoordinateRound114Exact where

------------------------------------------------------------------------
-- ROUND114: ONE PHYSICAL STRESS COORDINATE FEEDS TELESCOPE AND COMPLETION
--
-- A BIDI guard against a subtle false closure: the CMP119 Cauchy insertion and
-- the Row-B / marked-source completion must be views of the SAME differentiated
-- physical stress coordinate.  It is not enough to have one insertion that
-- telescopes and another stress-like field that completes.
------------------------------------------------------------------------

open import Relation.Binary.PropositionalEquality using (_≡_)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanSameFamilyStressCauchySchwingerRound109Exact as R109
import DASHI.Physics.YangMills.BalabanStressSameObjectProvenanceRound110Exact as R110
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

    MetricPerturbation Response : Set
    cmp119CompletedResponse : MetricPerturbation → Response
    completedMarkedStressResponse : MetricPerturbation → Response
    literalStressPairing :
      Top.StressTensor C → MetricPerturbation → Response

    cauchyCompletionIsCompletedMarkedStress : ∀ perturbation →
      cmp119CompletedResponse perturbation
      ≡ completedMarkedStressResponse perturbation

    completedMarkedStressIsLiteralStressPairing : ∀ perturbation →
      completedMarkedStressResponse perturbation
      ≡ literalStressPairing (Top.stressTensor Y group) perturbation
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
  ; R110.LiteralStressSameObjectProvenance.MetricPerturbation =
      MetricPerturbation dataSet
  ; R110.LiteralStressSameObjectProvenance.Response = Response dataSet
  ; R110.LiteralStressSameObjectProvenance.cmp119CompletedResponse =
      cmp119CompletedResponse dataSet
  ; R110.LiteralStressSameObjectProvenance.completedMarkedStressResponse =
      completedMarkedStressResponse dataSet
  ; R110.LiteralStressSameObjectProvenance.literalStressPairing =
      literalStressPairing dataSet
  ; R110.LiteralStressSameObjectProvenance.cauchyCompletionIsCompletedMarkedStress =
      cauchyCompletionIsCompletedMarkedStress dataSet
  ; R110.LiteralStressSameObjectProvenance.completedMarkedStressIsLiteralStressPairing =
      completedMarkedStressIsLiteralStressPairing dataSet
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

sameCoordinateCompletedResponseIsLiteralStressPairing :
  ∀ {C S}
    {Y : Top.LiteralYangMillsConstruction C S}
    {group : Top.CompactSimpleGroup C}
    (dataSet : LiteralStressCoordinate Y group)
    perturbation →
  cmp119CompletedResponse dataSet perturbation
  ≡ literalStressPairing dataSet (Top.stressTensor Y group) perturbation
sameCoordinateCompletedResponseIsLiteralStressPairing dataSet =
  R110.completedCMP119StressIsLiteralClayStressPairing
    (asSameObjectProvenance dataSet)

literalStressCoordinateCompilerLevel : ProofLevel
literalStressCoordinateCompilerLevel = machineChecked

-- This is now the central physical BIDI leaf for the stress-continuum lane:
-- instantiate ONE literal differentiated CMP116 stress coordinate whose CMP119,
-- shell/coefficient, and marked-completion views are the three views above.
literalCMP116StressCoordinateInstantiationLevel : ProofLevel
literalCMP116StressCoordinateInstantiationLevel = conditional
