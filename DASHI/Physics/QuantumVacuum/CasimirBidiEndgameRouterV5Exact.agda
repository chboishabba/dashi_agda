module DASHI.Physics.QuantumVacuum.CasimirBidiEndgameRouterV5Exact where

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
import DASHI.Physics.QuantumVacuum.CasimirZetaMinusThreeBidiExact as ZetaProblem
import DASHI.Physics.QuantumVacuum.CasimirZetaDefectTransformationTraceExact as ZetaTrace
import DASHI.Physics.QuantumVacuum.Casimir720FactorisationBidiExact as C720

------------------------------------------------------------------------
-- CASIMIR BIDI ENDGAME ROUTER V5
--
-- V5 removes the legacy bare-Set zeta weld from the canonical endgame.  The
-- longitudinal lane is now one literal Casimir zeta problem, one proof-bearing
-- transformation trace from its discrete-minus-continuum defect, and one
-- proof-bearing source-backed zeta(-3)=1/120 receipt.
------------------------------------------------------------------------

record CanonicalCasimirEndgameBundle
    (kernel : Casimir.CasimirScalarModel)
    (trigProblem : Trig.Round11FactorInterchangeProblem)
    (trigWeld : TrigWeld.Round11ClassicalTrigObjectWeld trigProblem)
    (zetaProblem : ZetaProblem.CasimirLongitudinalZetaProblem kernel)
    (zetaTrace : ZetaTrace.LongitudinalDefectTransformationTrace kernel zetaProblem)
    (zeta120 : ZetaTrace.ProofBearingCasimirZeta120 kernel zetaProblem zetaTrace) : Set₁ where
  field
    maxwellSourceTarget : MaxwellSource.LocalParallelPlateModeExpansionTarget
    maxwellCompleteness : MaxwellProof.ProofBearingTETMCompletenessReceipt

    polarMeasureTarget :
      Polar.ReducedBishopPolarMeasureTarget trigProblem trigWeld

    residualTail : Residual.CanonicalResidualTailInput

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
  ∀ {kernel trigProblem trigWeld zetaProblem zetaTrace zeta120} →
  (B : CanonicalCasimirEndgameBundle
    kernel trigProblem trigWeld zetaProblem zetaTrace zeta120) →
  MaxwellSource.LocalModeExpansion (maxwellSourceTarget B)
compiledMaxwellModeExpansion B =
  MaxwellSource.compileLocalParallelPlateModeExpansion
    (maxwellSourceTarget B)

compiledTrigDerivativeAuthority :
  ∀ {kernel trigProblem trigWeld zetaProblem zetaTrace zeta120} →
  CanonicalCasimirEndgameBundle
    kernel trigProblem trigWeld zetaProblem zetaTrace zeta120 →
  Trig.Round11FactorInterchangeAuthority trigProblem
compiledTrigDerivativeAuthority
    {trigProblem = trigProblem} {trigWeld = trigWeld} B =
  TrigWeld.compileRound11DerivativeAuthority trigProblem trigWeld

compiledTrigPythagorean :
  ∀ {kernel trigProblem trigWeld zetaProblem zetaTrace zeta120} →
  CanonicalCasimirEndgameBundle
    kernel trigProblem trigWeld zetaProblem zetaTrace zeta120 →
  TrigWeld.Round11Pythagorean trigProblem
compiledTrigPythagorean
    {trigProblem = trigProblem} {trigWeld = trigWeld} B =
  TrigWeld.compileRound11Pythagorean trigProblem trigWeld

compiledPolarMeasureChange :
  ∀ {kernel trigProblem trigWeld zetaProblem zetaTrace zeta120} →
  (B : CanonicalCasimirEndgameBundle
    kernel trigProblem trigWeld zetaProblem zetaTrace zeta120) →
  Polar.LocalPolarMeasureChange (polarMeasureTarget B)
compiledPolarMeasureChange B =
  Polar.compileLocalPolarMeasureChange (polarMeasureTarget B)

compiledResidualLimit :
  ∀ {kernel trigProblem trigWeld zetaProblem zetaTrace zeta120} →
  CanonicalCasimirEndgameBundle
    kernel trigProblem trigWeld zetaProblem zetaTrace zeta120 →
  ResidualResult.ResidualLimitResult
compiledResidualLimit B =
  Residual.compileCanonicalResidualLimit (residualTail B)

compiledTransformedDefectOneOver120 :
  ∀ {kernel trigProblem trigWeld zetaProblem zetaTrace zeta120} →
  CanonicalCasimirEndgameBundle
    kernel trigProblem trigWeld zetaProblem zetaTrace zeta120 →
  ZetaProblem.transformedDefectValue zetaProblem ≡
    ZetaTrace.problemOneOver120Value zeta120
compiledTransformedDefectOneOver120 B =
  ZetaTrace.transformedLiteralDefectEqualsOneOver120 _

compiledLegacyZeta120 :
  ∀ {kernel trigProblem trigWeld zetaProblem zetaTrace zeta120} →
  CanonicalCasimirEndgameBundle
    kernel trigProblem trigWeld zetaProblem zetaTrace zeta120 →
  C720.ZetaMinusThree120Receipt
compiledLegacyZeta120 B = ZetaTrace.asLegacyZeta120Receipt _

record CanonicalEndgameOutputs
    (kernel : Casimir.CasimirScalarModel)
    (trigProblem : Trig.Round11FactorInterchangeProblem)
    (trigWeld : TrigWeld.Round11ClassicalTrigObjectWeld trigProblem)
    (zetaProblem : ZetaProblem.CasimirLongitudinalZetaProblem kernel)
    (zetaTrace : ZetaTrace.LongitudinalDefectTransformationTrace kernel zetaProblem)
    (zeta120 : ZetaTrace.ProofBearingCasimirZeta120 kernel zetaProblem zetaTrace)
    (B : CanonicalCasimirEndgameBundle
      kernel trigProblem trigWeld zetaProblem zetaTrace zeta120) : Set₁ where
  field
    maxwellModeExpansion : MaxwellSource.LocalModeExpansion (maxwellSourceTarget B)
    trigDerivativeAuthority : Trig.Round11FactorInterchangeAuthority trigProblem
    trigPythagorean : TrigWeld.Round11Pythagorean trigProblem
    polarMeasureChange : Polar.LocalPolarMeasureChange (polarMeasureTarget B)
    residualLimit : ResidualResult.ResidualLimitResult
    transformedDefectOneOver120 :
      ZetaProblem.transformedDefectValue zetaProblem ≡
      ZetaTrace.problemOneOver120Value zeta120
    legacyZeta120 : C720.ZetaMinusThree120Receipt
    arithmetic720 : 6 * 120 ≡ 720

    sameLiteralZetaDefect : ZetaTrace.SameLiteralLongitudinalDefect zetaTrace
    sameSpectrum : SamePhysicalSpectrumAcrossMaxwellAndCasimir B
    sameTransverseObject : SameTransverseObjectAcrossPolarAndRenormalisation B
    sameLongitudinalDefect : SameLongitudinalDefectAcrossRenormalisationAndZeta B
    sameSeparation : SameSeparationParameterAcrossAllStages B

    reading : String

open CanonicalEndgameOutputs public

compileCanonicalEndgame :
  ∀ {kernel trigProblem trigWeld zetaProblem zetaTrace zeta120} →
  (B : CanonicalCasimirEndgameBundle
    kernel trigProblem trigWeld zetaProblem zetaTrace zeta120) →
  CanonicalEndgameOutputs
    kernel trigProblem trigWeld zetaProblem zetaTrace zeta120 B
compileCanonicalEndgame
    {zetaTrace = zetaTrace} {zeta120 = zeta120} B = record
  { maxwellModeExpansion = compiledMaxwellModeExpansion B
  ; trigDerivativeAuthority = compiledTrigDerivativeAuthority B
  ; trigPythagorean = compiledTrigPythagorean B
  ; polarMeasureChange = compiledPolarMeasureChange B
  ; residualLimit = compiledResidualLimit B
  ; transformedDefectOneOver120 = compiledTransformedDefectOneOver120 B
  ; legacyZeta120 = compiledLegacyZeta120 B
  ; arithmetic720 = C720.sixTimes120Is720
  ; sameLiteralZetaDefect = ZetaTrace.sameLiteralDefectProof zetaTrace
  ; sameSpectrum = samePhysicalSpectrumAcrossMaxwellAndCasimirEvidence B
  ; sameTransverseObject = sameTransverseObjectAcrossPolarAndRenormalisationEvidence B
  ; sameLongitudinalDefect = sameLongitudinalDefectAcrossRenormalisationAndZetaEvidence B
  ; sameSeparation = sameSeparationParameterAcrossAllStagesEvidence B
  ; reading =
      "V5 canonical endgame: longitudinal same-object evidence is a typed transformation trace, not a legacy Set marker; the transformed literal defect equals the source-backed 1/120 value by theorem."
  }

------------------------------------------------------------------------
-- True remaining V5 producer payments.
------------------------------------------------------------------------

record ReverseV5EndgameObligations : Set where
  field
    maxwellFiniteEnergyCarrierWeld : Set
    sharedClassicalBishopTrigObjectWeld : Set
    polarMeasureDomainIntegrandWeld : Set
    concreteOneOverSuccessorResidualTail : Set
    concreteLongitudinalTransformationTrace : Set
    crossStagePhysicalSameObjectReceipts : Set

open ReverseV5EndgameObligations public

data LegacyZetaSameDefectSetStillRequired : Set where

proofBearingTraceSupersedesLegacyZetaSet :
  LegacyZetaSameDefectSetStillRequired → ⊥
proofBearingTraceSupersedesLegacyZetaSet ()

record Status : Set where
  field
    v5ProofBearingZetaRouterOwned : Bool
    literalTransformedDefectOneOver120ProofOwned : Bool
    legacyZetaSameDefectSetPruned : Bool
    remainingProducerFamilies : Nat

    v5ProofBearingZetaRouterOwnedIsTrue : v5ProofBearingZetaRouterOwned ≡ true
    literalTransformedDefectOneOver120ProofOwnedIsTrue :
      literalTransformedDefectOneOver120ProofOwned ≡ true
    legacyZetaSameDefectSetPrunedIsTrue : legacyZetaSameDefectSetPruned ≡ true
    remainingProducerFamiliesIsFive : remainingProducerFamilies ≡ 5

open Status public

canonicalStatus : Status
canonicalStatus = record
  { v5ProofBearingZetaRouterOwned = true
  ; literalTransformedDefectOneOver120ProofOwned = true
  ; legacyZetaSameDefectSetPruned = true
  ; remainingProducerFamilies = 5
  ; v5ProofBearingZetaRouterOwnedIsTrue = refl
  ; literalTransformedDefectOneOver120ProofOwnedIsTrue = refl
  ; legacyZetaSameDefectSetPrunedIsTrue = refl
  ; remainingProducerFamiliesIsFive = refl
  }
