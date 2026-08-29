{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanStressSameObjectProvenanceRound110Exact where

------------------------------------------------------------------------
-- ROUND110: ONE STRESS OBJECT THROUGH TELESCOPE, COMPLETION, AND CLAY ENDPOINT
--
-- Tightened after Round111: the endpoint response is not an arbitrary function.
-- It is the literal `fieldFunctional` of the actual marked stress field produced
-- by the same `completedSources` carried by Round109.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational.Base as ℚ using (_≤_; _*_)
open import Relation.Binary.PropositionalEquality using (trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanSameFamilyStressCauchySchwingerRound109Exact as R109
import DASHI.Physics.YangMills.BalabanMarkedStressLiteralDerivativeRound111Exact as R111
import DASHI.Physics.YangMills.BalabanCharacteristicNuclearContinuityTransportExact as Nuclear
import DASHI.Physics.YangMills.BalabanMarkedSourceNuclearCompositeFieldExact as Marked
import DASHI.Physics.YangMills.BalabanMarkedSourceCompositeStressFieldExact as StressMarked
import DASHI.Physics.YangMills.BalabanContinuumScaleLocalObservableCauchyExact as Scale
import DASHI.Physics.YangMills.BalabanTopDownSummableRGIncrementExact as Sum
import DASHI.Physics.YangMills.BalabanCMP119CompatibleLocalExpectationFlowExact as Source
import DASHI.Physics.YangMills.BalabanTraceKoteckyPreissGeometricExact as Geo
import DASHI.Physics.YangMills.YangMillsClayLiteralTopDownConstructionExact as Top

record LiteralStressSameObjectProvenance
    {C : Top.LiteralYangMillsCarriers}
    {S : Top.LiteralYangMillsSemantics C}
    (Y : Top.LiteralYangMillsConstruction C S)
    (group : Top.CompactSimpleGroup C) : Set₁ where
  field
    sourceCauchy : R109.SourceNativeStressScaleCauchy
    markedCompletion : R109.LiteralSchwingerStressMarkedCompletion Y group

    -- The completion of the SAME CMP119 stress insertion.  Its codomain is
    -- forced to be the actual Round85 continuity-scale value carrier.
    cmp119CompletedResponse :
      Nuclear.Test (R109.continuityScale markedCompletion) →
      Nuclear.Value (R109.continuityScale markedCompletion)

    -- No parallel `completedMarkedStressResponse` is permitted: the target is
    -- literally the field functional constructed from `completedSources`.
    cauchyCompletionIsActualMarkedStressFunctional :
      let sources = R109.completedSources markedCompletion
          fields = StressMarked.sameCompletedMarkedSourcesGiveCompositeAndStressFields sources
      in
      cmp119CompletedResponse
      ≡ Marked.fieldFunctional (StressMarked.stressField fields)
open LiteralStressSameObjectProvenance public

stressDifferenceCauchyModulus :
  ∀ {C S}
    {Y : Top.LiteralYangMillsConstruction C S}
    {group : Top.CompactSimpleGroup C}
    (dataSet : LiteralStressSameObjectProvenance Y group) →
  ∀ start count →
  R109.stressDifference (sourceCauchy dataSet) start count
  ≤ Scale.coefficient
      (Sum.commonMajorant
        (Source.sourceCompatibleSameFamilyIncrement
          (R109.source (sourceCauchy dataSet))
          (R109.smallHistory (sourceCauchy dataSet))
          (R109.stressInsertion (sourceCauchy dataSet))))
      * (Geo.half * Geo.halfPower start)
stressDifferenceCauchyModulus dataSet =
  R109.stressResponseCauchyModulus (sourceCauchy dataSet)

completedCMP119StressIsLiteralClayStressDerivative :
  ∀ {C S}
    {Y : Top.LiteralYangMillsConstruction C S}
    {group : Top.CompactSimpleGroup C}
    (dataSet : LiteralStressSameObjectProvenance Y group) →
  let completion = markedCompletion dataSet
      sources = R109.completedSources completion
      stressData = StressMarked.stressData sources
  in
  cmp119CompletedResponse dataSet
  ≡ Marked.sourceDerivative stressData (Top.stressTensor Y group)
completedCMP119StressIsLiteralClayStressDerivative dataSet =
  let
    completion = markedCompletion dataSet
    sources = R109.completedSources completion
    fields = StressMarked.sameCompletedMarkedSourcesGiveCompositeAndStressFields sources
    markedFunctional = Marked.fieldFunctional (StressMarked.stressField fields)
  in
  trans
    (cauchyCompletionIsActualMarkedStressFunctional dataSet)
    (R111.completedMarkedStressFunctionalIsLiteralClayStressDerivative completion)

sameObjectStressProvenanceCompilerLevel : ProofLevel
sameObjectStressProvenanceCompilerLevel = machineChecked

literalCMP119StressCompletionProvenanceLevel : ProofLevel
literalCMP119StressCompletionProvenanceLevel = conditional
