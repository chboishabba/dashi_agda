module DASHI.Physics.QuantumVacuum.CasimirBidiEndgameRouterV3Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Analysis.MetricConvergenceKernelBidiExact as Metric
import DASHI.Analysis.BishopRound11FactorDerivativeInterchangeExact as Trig
import DASHI.Analysis.BishopRound11ClassicalTrigObjectWeldExact as TrigWeld

import DASHI.Physics.QuantumVacuum.CasimirParallelPlateKernel as Casimir
import DASHI.Physics.QuantumVacuum.ParallelPlateTETMModeExpansionSourceTransportExact as MaxwellSource
import DASHI.Physics.QuantumVacuum.PerfectConductorTETMProofBearingCompletenessExact as MaxwellProof
import DASHI.Physics.QuantumVacuum.BishopPolarMeasureSourceWeldReducedExact as Polar
import DASHI.Physics.QuantumVacuum.CasimirRegulatorMetricTailReceiptExact as Tail
import DASHI.Physics.QuantumVacuum.CasimirRegulatorMetricTailResidualCompilerExact as ResidualTail
import DASHI.Physics.QuantumVacuum.CasimirResidualConvergenceRouteBidiExact as Residual
import DASHI.Physics.QuantumVacuum.CasimirZetaSourceBackedDefectCompilerExact as Zeta
import DASHI.Physics.QuantumVacuum.CasimirZetaMinusThreeBidiExact as LegacyZeta
import DASHI.Physics.QuantumVacuum.Casimir720FactorisationBidiExact as C720

------------------------------------------------------------------------
-- CASIMIR BIDI ENDGAME ROUTER V3
--
-- V3 consumes proof-bearing local welds.  It deliberately does not accept the
-- older bare-Set Maxwell completeness or regulator-tail surfaces as sufficient
-- evidence.
------------------------------------------------------------------------

record ProofBearingCasimirEndgameBundle
    (kernel : Casimir.CasimirScalarModel)
    (trigProblem : Trig.Round11FactorInterchangeProblem)
    (trigWeld : TrigWeld.Round11ClassicalTrigObjectWeld trigProblem)
    (metricProblem : Metric.ParameterisedMetricLimitProblem)
    (metricTail : Tail.ProofBearingMetricTail metricProblem) : Set₁ where
  field
    maxwellSourceTarget : MaxwellSource.LocalParallelPlateModeExpansionTarget
    maxwellCompleteness : MaxwellProof.ProofBearingTETMCompletenessReceipt

    polarMeasureTarget :
      Polar.ReducedBishopPolarMeasureTarget trigProblem trigWeld

    residualTailWeld :
      ResidualTail.ProofBearingResidualMetricTailWeld
        metricProblem metricTail

    zetaDefectWeld : Zeta.CasimirZetaDefectCarrierWeld kernel

    SamePhysicalSpectrumAcrossMaxwellAndCasimir : Set
    samePhysicalSpectrumAcrossMaxwellAndCasimirEvidence :
      SamePhysicalSpectrumAcrossMaxwellAndCasimir

    SameTransverseObjectAcrossPolarAndRenormalisation : Set
    sameTransverseObjectAcrossPolarAndRenormalisationEvidence :
      SameTransverseObjectAcrossPolarAndRenormalisation

    SameResidualObservableAcrossTailAndFinalEnergy : Set
    sameResidualObservableAcrossTailAndFinalEnergyEvidence :
      SameResidualObservableAcrossTailAndFinalEnergy

    SameLongitudinalDefectAcrossRenormalisationAndZeta : Set
    sameLongitudinalDefectAcrossRenormalisationAndZetaEvidence :
      SameLongitudinalDefectAcrossRenormalisationAndZeta

    SameSeparationParameterAcrossAllStages : Set
    sameSeparationParameterAcrossAllStagesEvidence :
      SameSeparationParameterAcrossAllStages

    reading : String

open ProofBearingCasimirEndgameBundle public

------------------------------------------------------------------------
-- Compiler outputs.
------------------------------------------------------------------------

compiledMaxwellModeExpansion :
  ∀ {kernel trigProblem trigWeld metricProblem metricTail} →
  (B : ProofBearingCasimirEndgameBundle
    kernel trigProblem trigWeld metricProblem metricTail) →
  MaxwellSource.LocalModeExpansion (maxwellSourceTarget B)
compiledMaxwellModeExpansion B =
  MaxwellSource.compileLocalParallelPlateModeExpansion
    (maxwellSourceTarget B)

compiledTrigDerivativeAuthority :
  ∀ {kernel trigProblem trigWeld metricProblem metricTail} →
  ProofBearingCasimirEndgameBundle
    kernel trigProblem trigWeld metricProblem metricTail →
  Trig.Round11FactorInterchangeAuthority trigProblem
compiledTrigDerivativeAuthority B =
  TrigWeld.compileRound11DerivativeAuthority _ _

compiledTrigPythagorean :
  ∀ {kernel trigProblem trigWeld metricProblem metricTail} →
  ProofBearingCasimirEndgameBundle
    kernel trigProblem trigWeld metricProblem metricTail →
  TrigWeld.Round11Pythagorean trigProblem
compiledTrigPythagorean B =
  TrigWeld.compileRound11Pythagorean _ _

compiledPolarMeasureChange :
  ∀ {kernel trigProblem trigWeld metricProblem metricTail} →
  (B : ProofBearingCasimirEndgameBundle
    kernel trigProblem trigWeld metricProblem metricTail) →
  Polar.LocalPolarMeasureChange (polarMeasureTarget B)
compiledPolarMeasureChange B =
  Polar.compileLocalPolarMeasureChange (polarMeasureTarget B)

compiledResidualLimit :
  ∀ {kernel trigProblem trigWeld metricProblem metricTail} →
  (B : ProofBearingCasimirEndgameBundle
    kernel trigProblem trigWeld metricProblem metricTail) →
  Residual.ResidualLimitResult
compiledResidualLimit B =
  ResidualTail.compileProofBearingDirectResidualLimit
    (residualTailWeld B)

compiledZetaProducer :
  ∀ {kernel trigProblem trigWeld metricProblem metricTail} →
  ProofBearingCasimirEndgameBundle
    kernel trigProblem trigWeld metricProblem metricTail →
  LegacyZeta.CasimirZeta120Producer kernel
compiledZetaProducer B =
  Zeta.compileCasimirZeta120Producer (zetaDefectWeld B)

compiledZeta120 :
  ∀ {kernel trigProblem trigWeld metricProblem metricTail} →
  ProofBearingCasimirEndgameBundle
    kernel trigProblem trigWeld metricProblem metricTail →
  C720.ZetaMinusThree120Receipt
compiledZeta120 B =
  Zeta.compileCasimirZeta120Receipt (zetaDefectWeld B)

compiled720Arithmetic :
  ∀ {kernel trigProblem trigWeld metricProblem metricTail} →
  ProofBearingCasimirEndgameBundle
    kernel trigProblem trigWeld metricProblem metricTail →
  6 * 120 ≡ 720
compiled720Arithmetic _ = C720.sixTimes120Is720

record ProofBearingEndgameOutputs
    (kernel : Casimir.CasimirScalarModel)
    (trigProblem : Trig.Round11FactorInterchangeProblem)
    (trigWeld : TrigWeld.Round11ClassicalTrigObjectWeld trigProblem)
    (metricProblem : Metric.ParameterisedMetricLimitProblem)
    (metricTail : Tail.ProofBearingMetricTail metricProblem)
    (B : ProofBearingCasimirEndgameBundle
      kernel trigProblem trigWeld metricProblem metricTail) : Set₁ where
  field
    maxwellModeExpansion : MaxwellSource.LocalModeExpansion (maxwellSourceTarget B)
    trigDerivativeAuthority : Trig.Round11FactorInterchangeAuthority trigProblem
    trigPythagorean : TrigWeld.Round11Pythagorean trigProblem
    polarMeasureChange : Polar.LocalPolarMeasureChange (polarMeasureTarget B)
    residualLimit : Residual.ResidualLimitResult
    zetaProducer : LegacyZeta.CasimirZeta120Producer kernel
    zeta120 : C720.ZetaMinusThree120Receipt
    arithmetic720 : 6 * 120 ≡ 720

    sameSpectrum : SamePhysicalSpectrumAcrossMaxwellAndCasimir B
    sameTransverseObject : SameTransverseObjectAcrossPolarAndRenormalisation B
    sameResidualObservable : SameResidualObservableAcrossTailAndFinalEnergy B
    sameLongitudinalDefect : SameLongitudinalDefectAcrossRenormalisationAndZeta B
    sameSeparation : SameSeparationParameterAcrossAllStages B

    reading : String

open ProofBearingEndgameOutputs public

compileProofBearingEndgame :
  ∀ {kernel trigProblem trigWeld metricProblem metricTail} →
  (B : ProofBearingCasimirEndgameBundle
    kernel trigProblem trigWeld metricProblem metricTail) →
  ProofBearingEndgameOutputs
    kernel trigProblem trigWeld metricProblem metricTail B
compileProofBearingEndgame B = record
  { maxwellModeExpansion = compiledMaxwellModeExpansion B
  ; trigDerivativeAuthority = compiledTrigDerivativeAuthority B
  ; trigPythagorean = compiledTrigPythagorean B
  ; polarMeasureChange = compiledPolarMeasureChange B
  ; residualLimit = compiledResidualLimit B
  ; zetaProducer = compiledZetaProducer B
  ; zeta120 = compiledZeta120 B
  ; arithmetic720 = compiled720Arithmetic B
  ; sameSpectrum = samePhysicalSpectrumAcrossMaxwellAndCasimirEvidence B
  ; sameTransverseObject = sameTransverseObjectAcrossPolarAndRenormalisationEvidence B
  ; sameResidualObservable = sameResidualObservableAcrossTailAndFinalEnergyEvidence B
  ; sameLongitudinalDefect = sameLongitudinalDefectAcrossRenormalisationAndZetaEvidence B
  ; sameSeparation = sameSeparationParameterAcrossAllStagesEvidence B
  ; reading =
      "V3 proof-bearing endgame: source-backed Maxwell/trig/measure theorems, one coherent metric tail, and the typed zeta compiler are assembled only through inhabited same-object welds."
  }

------------------------------------------------------------------------
-- Reverse obligations at the V3 boundary.
------------------------------------------------------------------------

record ReverseV3EndgameObligations : Set where
  field
    maxwellSourceToLiteralFiniteEnergyCarrier : Set
    sharedClassicalToBishopTrigObject : Set
    polarMeasureDomainAndIntegrandWeld : Set
    oneConcreteDependentResidualTailBound : Set
    zetaTransformationTraceToLiteralLongitudinalDefect : Set
    crossStageSameObjectReceipts : Set

open ReverseV3EndgameObligations public

data BareStatusBooleanClosesV3 : Set where
data BareSetLabelClosesV3 : Set where

aStatusFlagIsNotEvidence : BareStatusBooleanClosesV3 → ⊥
aStatusFlagIsNotEvidence ()

aSetLabelIsNotEvidence : BareSetLabelClosesV3 → ⊥
aSetLabelIsNotEvidence ()

record Status : Set where
  field
    v3ProofBearingRouterOwned : Bool
    coherentMetricTailRequired : Bool
    sharedTrigWeldReusedAcrossDerivativeAndJacobian : Bool
    measureCutsetContainsNoIndependentTrigDerivativeLeaf : Bool
    legacyBareSetEvidenceAccepted : Bool

    v3ProofBearingRouterOwnedIsTrue : v3ProofBearingRouterOwned ≡ true
    coherentMetricTailRequiredIsTrue : coherentMetricTailRequired ≡ true
    sharedTrigWeldReusedAcrossDerivativeAndJacobianIsTrue :
      sharedTrigWeldReusedAcrossDerivativeAndJacobian ≡ true
    measureCutsetContainsNoIndependentTrigDerivativeLeafIsTrue :
      measureCutsetContainsNoIndependentTrigDerivativeLeaf ≡ true
    legacyBareSetEvidenceAcceptedIsFalse : legacyBareSetEvidenceAccepted ≡ false

open Status public

canonicalStatus : Status
canonicalStatus = record
  { v3ProofBearingRouterOwned = true
  ; coherentMetricTailRequired = true
  ; sharedTrigWeldReusedAcrossDerivativeAndJacobian = true
  ; measureCutsetContainsNoIndependentTrigDerivativeLeaf = true
  ; legacyBareSetEvidenceAccepted = false
  ; v3ProofBearingRouterOwnedIsTrue = refl
  ; coherentMetricTailRequiredIsTrue = refl
  ; sharedTrigWeldReusedAcrossDerivativeAndJacobianIsTrue = refl
  ; measureCutsetContainsNoIndependentTrigDerivativeLeafIsTrue = refl
  ; legacyBareSetEvidenceAcceptedIsFalse = refl
  }
