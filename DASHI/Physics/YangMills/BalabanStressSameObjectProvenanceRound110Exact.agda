{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanStressSameObjectProvenanceRound110Exact where

------------------------------------------------------------------------
-- ROUND110: ONE STRESS OBJECT THROUGH TELESCOPE, COMPLETION, AND CLAY ENDPOINT
--
-- Round109 separated three remaining same-object seams:
--
--   finite stress response = CMP119 local-insertion response;
--   Cauchy completion       = completed marked stress field;
--   completed marked stress = literal Clay stressTensor Y G.
--
-- This file packages those seams into one provenance carrier and proves the
-- downstream endpoint equality by transitivity.  It deliberately does not
-- identify the rational Cauchy-difference carrier with the value type of the
-- stress functional: the telescope controls differences, while the completion
-- lives in its own response carrier.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base as ℚ using (ℚ; _≤_; _*_)
open import Relation.Binary.PropositionalEquality using (trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanSameFamilyStressCauchySchwingerRound109Exact as R109
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

    MetricPerturbation Response : Set

    cmp119CompletedResponse : MetricPerturbation → Response
    completedMarkedStressResponse : MetricPerturbation → Response
    literalStressPairing :
      Top.StressTensor C → MetricPerturbation → Response

    -- The completion is explicitly the completion of the SAME insertion whose
    -- finite differences are controlled by `sourceCauchy`.
    cauchyCompletionIsCompletedMarkedStress : ∀ perturbation →
      cmp119CompletedResponse perturbation
      ≡ completedMarkedStressResponse perturbation

    -- The completed marked stress response is represented by the literal
    -- group-indexed Clay stress tensor.
    completedMarkedStressIsLiteralStressPairing : ∀ perturbation →
      completedMarkedStressResponse perturbation
      ≡ literalStressPairing (Top.stressTensor Y group) perturbation
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

completedCMP119StressIsLiteralClayStressPairing :
  ∀ {C S}
    {Y : Top.LiteralYangMillsConstruction C S}
    {group : Top.CompactSimpleGroup C}
    (dataSet : LiteralStressSameObjectProvenance Y group)
    perturbation →
  cmp119CompletedResponse dataSet perturbation
  ≡ literalStressPairing dataSet (Top.stressTensor Y group) perturbation
completedCMP119StressIsLiteralClayStressPairing dataSet perturbation =
  trans
    (cauchyCompletionIsCompletedMarkedStress dataSet perturbation)
    (completedMarkedStressIsLiteralStressPairing dataSet perturbation)

sameObjectStressProvenanceCompilerLevel : ProofLevel
sameObjectStressProvenanceCompilerLevel = machineChecked

-- Genuine physical bindings still required: instantiate this record from the
-- literal differentiated CMP116/CMP119 stress insertion and its completed
-- marked-source endpoint.  No new telescope or completion theorem is required.
literalCMP119StressCompletionProvenanceLevel : ProofLevel
literalCMP119StressCompletionProvenanceLevel = conditional
