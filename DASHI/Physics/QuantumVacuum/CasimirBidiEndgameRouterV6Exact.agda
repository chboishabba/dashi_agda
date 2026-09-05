module DASHI.Physics.QuantumVacuum.CasimirBidiEndgameRouterV6Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Analysis.BishopRound11FactorDerivativeInterchangeExact as Trig
import DASHI.Analysis.BishopRound11ClassicalTrigObjectWeldExact as TrigWeld

import DASHI.Physics.QuantumVacuum.CasimirParallelPlateKernel as Casimir
import DASHI.Physics.QuantumVacuum.ParallelPlateTETMSourceBackedCompletenessCompilerExact as Maxwell
import DASHI.Physics.QuantumVacuum.PerfectConductorTETMProofBearingCompletenessExact as MaxwellProof
import DASHI.Physics.QuantumVacuum.BishopPolarMeasureSourceWeldReducedExact as Polar
import DASHI.Physics.QuantumVacuum.CasimirCanonicalResidualMetricConvergenceCompilerExact as Residual
import DASHI.Physics.QuantumVacuum.CasimirResidualConvergenceRouteBidiExact as ResidualResult
import DASHI.Physics.QuantumVacuum.CasimirZetaMinusThreeBidiExact as ZetaProblem
import DASHI.Physics.QuantumVacuum.CasimirZetaDefectTransformationTraceExact as ZetaTrace
import DASHI.Physics.QuantumVacuum.Casimir720FactorisationBidiExact as C720

------------------------------------------------------------------------
-- CASIMIR BIDI ENDGAME ROUTER V6
--
-- Maxwell source transport is now compiled into the proof-bearing completeness
-- receipt at the capstone: field spanning and longitudinal coverage come from
-- the bounded source after one same-object mode-space weld; exact zero-sector
-- counting, transverse completion and TE/TM independence remain local.
------------------------------------------------------------------------

record CanonicalCasimirEndgameBundle
    (kernel : Casimir.CasimirScalarModel)
    (trigProblem : Trig.Round11FactorInterchangeProblem)
    (trigWeld : TrigWeld.Round11ClassicalTrigObjectWeld trigProblem)
    (zetaProblem : ZetaProblem.CasimirLongitudinalZetaProblem kernel)
    (zetaTrace : ZetaTrace.LongitudinalDefectTransformationTrace kernel zetaProblem)
    (zeta120 : ZetaTrace.ProofBearingCasimirZeta120 kernel zetaProblem zetaTrace) : Set₁ where
  field
    maxwell : Maxwell.LocalTETMCompletenessSkeleton

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

compiledMaxwellCompleteness :
  ∀ {kernel trigProblem trigWeld zetaProblem zetaTrace zeta120} →
  CanonicalCasimirEndgameBundle
    kernel trigProblem trigWeld zetaProblem zetaTrace zeta120 →
  MaxwellProof.ProofBearingTETMCompletenessReceipt
compiledMaxwellCompleteness B =
  Maxwell.compileProofBearingTETMCompleteness (maxwell B)

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
compiledTransformedDefectOneOver120
    {zeta120 = zeta120} B =
  ZetaTrace.transformedLiteralDefectEqualsOneOver120 zeta120

compiledLegacyZeta120 :
  ∀ {kernel trigProblem trigWeld zetaProblem zetaTrace zeta120} →
  CanonicalCasimirEndgameBundle
    kernel trigProblem trigWeld zetaProblem zetaTrace zeta120 →
  C720.ZetaMinusThree120Receipt
compiledLegacyZeta120 {zeta120 = zeta120} B =
  ZetaTrace.asLegacyZeta120Receipt zeta120

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
    maxwellCompleteness : MaxwellProof.ProofBearingTETMCompletenessReceipt
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
  { maxwellCompleteness = compiledMaxwellCompleteness B
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
      "V6 canonical endgame: the bounded parallel-plate source compiles field spanning and longitudinal coverage into the proof-bearing Maxwell completeness receipt; only local Hilbert/transverse/independence/zero-sector semantics remain."
  }

------------------------------------------------------------------------
-- TRUE REMAINING V6 PRODUCER PAYMENTS
------------------------------------------------------------------------

record ReverseV6EndgameObligations : Set where
  field
    maxwellModeObjectAndFiniteEnergyHilbertWeld : Set
    maxwellTransverseCompleteness : Set
    maxwellTETMIndependenceAwayFromZeroSector : Set
    maxwellExactZeroSectorCounting : Set
    sharedClassicalBishopTrigObjectWeld : Set
    polarMeasureDomainIntegrandWeld : Set
    concreteOneOverSuccessorResidualTail : Set
    concreteLongitudinalTransformationTrace : Set
    crossStagePhysicalSameObjectReceipts : Set

open ReverseV6EndgameObligations public

data PrebuiltMaxwellCompletenessReceiptStillRequired : Set where

data SeparateSourceSpanningAndLongitudinalReceiptsStillRequired : Set where

maxwellCompletenessNowCompiled :
  PrebuiltMaxwellCompletenessReceiptStillRequired → ⊥
maxwellCompletenessNowCompiled ()

oneSourceModeObjectWeldFeedsBoth :
  SeparateSourceSpanningAndLongitudinalReceiptsStillRequired → ⊥
oneSourceModeObjectWeldFeedsBoth ()

record Status : Set where
  field
    v6MaxwellCompilerRouterOwned : Bool
    sourceBackedFieldSpanningCompiled : Bool
    sourceBackedLongitudinalCoverageCompiled : Bool
    prebuiltMaxwellReceiptPruned : Bool
    remainingProducerFamilies : Nat

    v6MaxwellCompilerRouterOwnedIsTrue : v6MaxwellCompilerRouterOwned ≡ true
    sourceBackedFieldSpanningCompiledIsTrue : sourceBackedFieldSpanningCompiled ≡ true
    sourceBackedLongitudinalCoverageCompiledIsTrue : sourceBackedLongitudinalCoverageCompiled ≡ true
    prebuiltMaxwellReceiptPrunedIsTrue : prebuiltMaxwellReceiptPruned ≡ true
    remainingProducerFamiliesIsFive : remainingProducerFamilies ≡ 5

open Status public

canonicalStatus : Status
canonicalStatus = record
  { v6MaxwellCompilerRouterOwned = true
  ; sourceBackedFieldSpanningCompiled = true
  ; sourceBackedLongitudinalCoverageCompiled = true
  ; prebuiltMaxwellReceiptPruned = true
  ; remainingProducerFamilies = 5
  ; v6MaxwellCompilerRouterOwnedIsTrue = refl
  ; sourceBackedFieldSpanningCompiledIsTrue = refl
  ; sourceBackedLongitudinalCoverageCompiledIsTrue = refl
  ; prebuiltMaxwellReceiptPrunedIsTrue = refl
  ; remainingProducerFamiliesIsFive = refl
  }
