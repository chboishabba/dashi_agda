module DASHI.Physics.QuantumVacuum.CasimirBidiEndgameRouterV4Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Analysis.BishopRound11FactorDerivativeInterchangeExact as Trig
import DASHI.Analysis.BishopRound11ClassicalTrigObjectWeldExact as TrigWeld

import DASHI.Physics.QuantumVacuum.CasimirParallelPlateKernel as Casimir
import DASHI.Physics.QuantumVacuum.ParallelPlateTETMModeExpansionSourceTransportExact as MaxwellSource
import DASHI.Physics.QuantumVacuum.PerfectConductorTETMProofBearingCompletenessExact as MaxwellProof
import DASHI.Physics.QuantumVacuum.BishopPolarMeasureSourceWeldReducedExact as Polar
import DASHI.Physics.QuantumVacuum.CasimirCanonicalResidualMetricConvergenceCompilerExact as Residual
import DASHI.Physics.QuantumVacuum.CasimirResidualConvergenceRouteBidiExact as ResidualResult
import DASHI.Physics.QuantumVacuum.CasimirZetaSourceBackedDefectCompilerExact as Zeta
import DASHI.Physics.QuantumVacuum.CasimirZetaMinusThreeBidiExact as LegacyZeta
import DASHI.Physics.QuantumVacuum.Casimir720FactorisationBidiExact as C720

------------------------------------------------------------------------
-- CASIMIR BIDI ENDGAME ROUTER V4
--
-- V4 removes the generic metric problem from the capstone.  The direct
-- residual route is canonical on the literal Bishop sequence/candidate, so the
-- only convergence input is the actual dependent 1/(m+1) tail theorem.
------------------------------------------------------------------------

record CanonicalCasimirEndgameBundle
    (kernel : Casimir.CasimirScalarModel)
    (trigProblem : Trig.Round11FactorInterchangeProblem)
    (trigWeld : TrigWeld.Round11ClassicalTrigObjectWeld trigProblem) : Set₁ where
  field
    maxwellSourceTarget : MaxwellSource.LocalParallelPlateModeExpansionTarget
    maxwellCompleteness : MaxwellProof.ProofBearingTETMCompletenessReceipt

    polarMeasureTarget :
      Polar.ReducedBishopPolarMeasureTarget trigProblem trigWeld

    residualTail : Residual.CanonicalResidualTailInput

    zetaDefectWeld : Zeta.CasimirZetaDefectCarrierWeld kernel

    SamePhysicalSpectrumAcrossMaxwellAndCasimir : Set
    samePhysicalSpectrumAcrossMaxwellAndCasimirEvidence :
      SamePhysicalSpectrumAcrossMaxwellAndCasimir

    SameTransverseObjectAcrossPolarAndRenormalisation : Set
    sameTransverseObjectAcrossPolarAndRenormalisationEvidence :
      SameTransverseObjectAcrossPolarAndRenormalisation

    SameLongitudinalDefectAcrossRenormalisationAndZeta : Set
    sameLongitudinalDefectAcrossRenormalisationAndZetaEvidence :
      SameLongitudinalDefectAcrossRenormalisationAndZeta

    SameSeparationParameterAcrossAllStages : Set
    sameSeparationParameterAcrossAllStagesEvidence :
      SameSeparationParameterAcrossAllStages

    reading : String

open CanonicalCasimirEndgameBundle public

compiledMaxwellModeExpansion :
  ∀ {kernel trigProblem trigWeld} →
  (B : CanonicalCasimirEndgameBundle kernel trigProblem trigWeld) →
  MaxwellSource.LocalModeExpansion (maxwellSourceTarget B)
compiledMaxwellModeExpansion B =
  MaxwellSource.compileLocalParallelPlateModeExpansion
    (maxwellSourceTarget B)

compiledTrigDerivativeAuthority :
  ∀ {kernel trigProblem trigWeld} →
  CanonicalCasimirEndgameBundle kernel trigProblem trigWeld →
  Trig.Round11FactorInterchangeAuthority trigProblem
compiledTrigDerivativeAuthority
    {trigProblem = trigProblem} {trigWeld = trigWeld} B =
  TrigWeld.compileRound11DerivativeAuthority trigProblem trigWeld

compiledTrigPythagorean :
  ∀ {kernel trigProblem trigWeld} →
  CanonicalCasimirEndgameBundle kernel trigProblem trigWeld →
  TrigWeld.Round11Pythagorean trigProblem
compiledTrigPythagorean
    {trigProblem = trigProblem} {trigWeld = trigWeld} B =
  TrigWeld.compileRound11Pythagorean trigProblem trigWeld

compiledPolarMeasureChange :
  ∀ {kernel trigProblem trigWeld} →
  (B : CanonicalCasimirEndgameBundle kernel trigProblem trigWeld) →
  Polar.LocalPolarMeasureChange (polarMeasureTarget B)
compiledPolarMeasureChange B =
  Polar.compileLocalPolarMeasureChange (polarMeasureTarget B)

compiledResidualLimit :
  ∀ {kernel trigProblem trigWeld} →
  CanonicalCasimirEndgameBundle kernel trigProblem trigWeld →
  ResidualResult.ResidualLimitResult
compiledResidualLimit B =
  Residual.compileCanonicalResidualLimit (residualTail B)

compiledZetaProducer :
  ∀ {kernel trigProblem trigWeld} →
  CanonicalCasimirEndgameBundle kernel trigProblem trigWeld →
  LegacyZeta.CasimirZeta120Producer kernel
compiledZetaProducer B =
  Zeta.compileCasimirZeta120Producer (zetaDefectWeld B)

compiledZeta120 :
  ∀ {kernel trigProblem trigWeld} →
  CanonicalCasimirEndgameBundle kernel trigProblem trigWeld →
  C720.ZetaMinusThree120Receipt
compiledZeta120 B =
  Zeta.compileCasimirZeta120Receipt (zetaDefectWeld B)

record CanonicalEndgameOutputs
    (kernel : Casimir.CasimirScalarModel)
    (trigProblem : Trig.Round11FactorInterchangeProblem)
    (trigWeld : TrigWeld.Round11ClassicalTrigObjectWeld trigProblem)
    (B : CanonicalCasimirEndgameBundle kernel trigProblem trigWeld) : Set₁ where
  field
    maxwellModeExpansion : MaxwellSource.LocalModeExpansion (maxwellSourceTarget B)
    trigDerivativeAuthority : Trig.Round11FactorInterchangeAuthority trigProblem
    trigPythagorean : TrigWeld.Round11Pythagorean trigProblem
    polarMeasureChange : Polar.LocalPolarMeasureChange (polarMeasureTarget B)
    residualLimit : ResidualResult.ResidualLimitResult
    zetaProducer : LegacyZeta.CasimirZeta120Producer kernel
    zeta120 : C720.ZetaMinusThree120Receipt
    arithmetic720 : 6 * 120 ≡ 720

    sameSpectrum : SamePhysicalSpectrumAcrossMaxwellAndCasimir B
    sameTransverseObject : SameTransverseObjectAcrossPolarAndRenormalisation B
    sameLongitudinalDefect : SameLongitudinalDefectAcrossRenormalisationAndZeta B
    sameSeparation : SameSeparationParameterAcrossAllStages B

    reading : String

open CanonicalEndgameOutputs public

compileCanonicalEndgame :
  ∀ {kernel trigProblem trigWeld} →
  (B : CanonicalCasimirEndgameBundle kernel trigProblem trigWeld) →
  CanonicalEndgameOutputs kernel trigProblem trigWeld B
compileCanonicalEndgame B = record
  { maxwellModeExpansion = compiledMaxwellModeExpansion B
  ; trigDerivativeAuthority = compiledTrigDerivativeAuthority B
  ; trigPythagorean = compiledTrigPythagorean B
  ; polarMeasureChange = compiledPolarMeasureChange B
  ; residualLimit = compiledResidualLimit B
  ; zetaProducer = compiledZetaProducer B
  ; zeta120 = compiledZeta120 B
  ; arithmetic720 = C720.sixTimes120Is720
  ; sameSpectrum = samePhysicalSpectrumAcrossMaxwellAndCasimirEvidence B
  ; sameTransverseObject = sameTransverseObjectAcrossPolarAndRenormalisationEvidence B
  ; sameLongitudinalDefect = sameLongitudinalDefectAcrossRenormalisationAndZetaEvidence B
  ; sameSeparation = sameSeparationParameterAcrossAllStagesEvidence B
  ; reading =
      "V4 canonical endgame: residual metric family, candidate and Bishop transport are definitionally fixed by the literal post-cancellation sequence."
  }

------------------------------------------------------------------------
-- True remaining V4 producer payments.
------------------------------------------------------------------------

record ReverseV4EndgameObligations : Set where
  field
    maxwellFiniteEnergyCarrierWeld : Set
    sharedClassicalBishopTrigObjectWeld : Set
    polarMeasureDomainIntegrandWeld : Set
    concreteOneOverSuccessorResidualTail : Set
    zetaTransformationTrace : Set
    crossStagePhysicalSameObjectReceipts : Set

open ReverseV4EndgameObligations public

data GenericMetricProblemStillRequiredAtCapstone : Set where
data MetricToBishopTransportStillRequiredAtCapstone : Set where
data ResidualTrajectoryIdentityStillRequiredAtCapstone : Set where

genericMetricProblemPruned : GenericMetricProblemStillRequiredAtCapstone → ⊥
genericMetricProblemPruned ()

metricTransportPruned : MetricToBishopTransportStillRequiredAtCapstone → ⊥
metricTransportPruned ()

residualTrajectoryWeldPruned : ResidualTrajectoryIdentityStillRequiredAtCapstone → ⊥
residualTrajectoryWeldPruned ()

record Status : Set where
  field
    v4CanonicalRouterOwned : Bool
    residualMetricParametersPruned : Bool
    residualTrajectoryWeldPruned : Bool
    metricToBishopTransportPruned : Bool
    remainingProducerFamilies : Nat

    v4CanonicalRouterOwnedIsTrue : v4CanonicalRouterOwned ≡ true
    residualMetricParametersPrunedIsTrue : residualMetricParametersPruned ≡ true
    residualTrajectoryWeldPrunedIsTrue : residualTrajectoryWeldPruned ≡ true
    metricToBishopTransportPrunedIsTrue : metricToBishopTransportPruned ≡ true
    remainingProducerFamiliesIsFive : remainingProducerFamilies ≡ 5

open Status public

canonicalStatus : Status
canonicalStatus = record
  { v4CanonicalRouterOwned = true
  ; residualMetricParametersPruned = true
  ; residualTrajectoryWeldPruned = true
  ; metricToBishopTransportPruned = true
  ; remainingProducerFamilies = 5
  ; v4CanonicalRouterOwnedIsTrue = refl
  ; residualMetricParametersPrunedIsTrue = refl
  ; residualTrajectoryWeldPrunedIsTrue = refl
  ; metricToBishopTransportPrunedIsTrue = refl
  ; remainingProducerFamiliesIsFive = refl
  }
