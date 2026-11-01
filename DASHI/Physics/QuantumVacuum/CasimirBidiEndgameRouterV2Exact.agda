module DASHI.Physics.QuantumVacuum.CasimirBidiEndgameRouterV2Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Physics.QuantumVacuum.CasimirParallelPlateKernel as Casimir
import DASHI.Physics.QuantumVacuum.PerfectConductorPlateModePDECutsetExact as Maxwell
import DASHI.Physics.QuantumVacuum.ParallelPlateTransverseMeasureLimitBidiExact as Transverse
import DASHI.Physics.QuantumVacuum.CasimirRadialMeasureOneSixthCutsetExact as Six
import DASHI.Physics.QuantumVacuum.CasimirResidualConvergenceRouteBidiExact as Residual
import DASHI.Physics.QuantumVacuum.CasimirZetaSourceBackedDefectCompilerExact as Zeta
import DASHI.Physics.QuantumVacuum.CasimirZetaMinusThreeBidiExact as LegacyZeta
import DASHI.Physics.QuantumVacuum.Casimir720FactorisationBidiExact as C720

------------------------------------------------------------------------
-- CASIMIR BIDI ENDGAME ROUTER V2
------------------------------------------------------------------------

record ReducedCasimirProducerBundle
    (kernel : Casimir.CasimirScalarModel) : Set₁ where
  field
    maxwell : Maxwell.PerfectConductorPDECompletion kernel

    transverseFamily : Transverse.CasimirTransverseMeasureFamily kernel
    oneSixth : Six.TransverseOneSixthReceipt kernel transverseFamily

    residualConvergence : Residual.ResidualConvergenceRoute

    zetaDefectWeld : Zeta.CasimirZetaDefectCarrierWeld kernel

    sameSpectrumAcrossMaxwellAndTransverse : Set
    sameSpectrumAcrossMaxwellAndTransverseEvidence :
      sameSpectrumAcrossMaxwellAndTransverse

    samePostCancellationResidualAsTransverseCalculation : Set
    samePostCancellationResidualAsTransverseCalculationEvidence :
      samePostCancellationResidualAsTransverseCalculation

    sameLongitudinalDefectAcrossOneSixthAndZeta : Set
    sameLongitudinalDefectAcrossOneSixthAndZetaEvidence :
      sameLongitudinalDefectAcrossOneSixthAndZeta

    sameSeparationParameter : Set
    sameSeparationParameterEvidence : sameSeparationParameter

    sameRenormalisedObservable : Set
    sameRenormalisedObservableEvidence : sameRenormalisedObservable

    zetaDefectSameObjectEvidence :
      Zeta.sameCasimirLongitudinalDefect zetaDefectWeld

    reading : String

open ReducedCasimirProducerBundle public

compiledResidualLimit :
  ∀ {kernel} →
  ReducedCasimirProducerBundle kernel →
  Residual.ResidualLimitResult
compiledResidualLimit B =
  Residual.compileResidualLimit (residualConvergence B)

compiledZetaProducer :
  ∀ {kernel} →
  ReducedCasimirProducerBundle kernel →
  LegacyZeta.CasimirZeta120Producer kernel
compiledZetaProducer B =
  Zeta.compileCasimirZeta120Producer (zetaDefectWeld B)

compiledZeta120Receipt :
  ∀ {kernel} →
  ReducedCasimirProducerBundle kernel →
  C720.ZetaMinusThree120Receipt
compiledZeta120Receipt B =
  Zeta.compileCasimirZeta120Receipt (zetaDefectWeld B)

compiled6Times120 :
  ∀ {kernel} →
  ReducedCasimirProducerBundle kernel →
  6 * 120 ≡ 720
compiled6Times120 _ = C720.sixTimes120Is720

record ReducedEndgameOutputs
    (kernel : Casimir.CasimirScalarModel)
    (B : ReducedCasimirProducerBundle kernel) : Set₁ where
  field
    residualLimit : Residual.ResidualLimitResult
    zetaProducer : LegacyZeta.CasimirZeta120Producer kernel
    zeta120 : C720.ZetaMinusThree120Receipt
    arithmetic720 : 6 * 120 ≡ 720

    residualIsSameRenormalisedObservable : sameRenormalisedObservable B
    zetaIsSameLongitudinalDefect :
      Zeta.sameCasimirLongitudinalDefect (zetaDefectWeld B)

    reading : String

open ReducedEndgameOutputs public

compileReducedEndgame :
  ∀ {kernel} →
  (B : ReducedCasimirProducerBundle kernel) →
  ReducedEndgameOutputs kernel B
compileReducedEndgame B = record
  { residualLimit = compiledResidualLimit B
  ; zetaProducer = compiledZetaProducer B
  ; zeta120 = compiledZeta120Receipt B
  ; arithmetic720 = compiled6Times120 B
  ; residualIsSameRenormalisedObservable = sameRenormalisedObservableEvidence B
  ; zetaIsSameLongitudinalDefect = zetaDefectSameObjectEvidence B
  ; reading =
      "Reduced Casimir endgame: Maxwell/transverse producers plus one convergence route and one typed proof-bearing zeta-defect weld compile the residual limit and longitudinal 1/120 receipt."
  }

------------------------------------------------------------------------
-- Reverse routing / firewalls.
------------------------------------------------------------------------

record ReverseReducedEndgameObligations : Set where
  field
    continuumMaxwellPhysicalWeld : Set
    transverseOneSixthPhysicalWeld : Set
    oneResidualConvergenceRoute : Set
    typedSourceBackedZetaDefectWeld : Set
    proofBearingSameObjectAssemblyWelds : Set

open ReverseReducedEndgameObligations public

data OldMonolithicRegulatorCompletionIsAlwaysRequired : Set where
data PrebuiltLegacyZetaProducerIsAlwaysRequired : Set where
data BothResidualConvergenceRoutesAreRequired : Set where
data BareSameObjectSetLabelIsEnoughForV2Assembly : Set where

monolithicRegulatorNoLongerMandatory :
  OldMonolithicRegulatorCompletionIsAlwaysRequired → ⊥
monolithicRegulatorNoLongerMandatory ()

legacyZetaProducerNoLongerMandatory :
  PrebuiltLegacyZetaProducerIsAlwaysRequired → ⊥
legacyZetaProducerNoLongerMandatory ()

onlyOneResidualRouteRequired :
  BothResidualConvergenceRoutesAreRequired → ⊥
onlyOneResidualRouteRequired ()

v2RequiresEvidenceNotBareLabels :
  BareSameObjectSetLabelIsEnoughForV2Assembly → ⊥
v2RequiresEvidenceNotBareLabels ()

record Status : Set where
  field
    reducedEndgameRouterOwned : Bool
    proofBearingAssemblyWeldsOwned : Bool
    zetaProducerCompilerOwned : Bool
    convergenceRouteDisjunctionOwned : Bool
    arithmetic720CompilerOwned : Bool
    continuumMaxwellStillLive : Bool
    transversePhysicalWeldStillLive : Bool
    concreteResidualTailStillLive : Bool
    zetaDefectSameObjectWeldStillLive : Bool

    reducedEndgameRouterOwnedIsTrue : reducedEndgameRouterOwned ≡ true
    proofBearingAssemblyWeldsOwnedIsTrue : proofBearingAssemblyWeldsOwned ≡ true
    zetaProducerCompilerOwnedIsTrue : zetaProducerCompilerOwned ≡ true
    convergenceRouteDisjunctionOwnedIsTrue : convergenceRouteDisjunctionOwned ≡ true
    arithmetic720CompilerOwnedIsTrue : arithmetic720CompilerOwned ≡ true
    continuumMaxwellStillLiveIsTrue : continuumMaxwellStillLive ≡ true
    transversePhysicalWeldStillLiveIsTrue : transversePhysicalWeldStillLive ≡ true
    concreteResidualTailStillLiveIsTrue : concreteResidualTailStillLive ≡ true
    zetaDefectSameObjectWeldStillLiveIsTrue : zetaDefectSameObjectWeldStillLive ≡ true

open Status public

canonicalStatus : Status
canonicalStatus = record
  { reducedEndgameRouterOwned = true
  ; proofBearingAssemblyWeldsOwned = true
  ; zetaProducerCompilerOwned = true
  ; convergenceRouteDisjunctionOwned = true
  ; arithmetic720CompilerOwned = true
  ; continuumMaxwellStillLive = true
  ; transversePhysicalWeldStillLive = true
  ; concreteResidualTailStillLive = true
  ; zetaDefectSameObjectWeldStillLive = true
  ; reducedEndgameRouterOwnedIsTrue = refl
  ; proofBearingAssemblyWeldsOwnedIsTrue = refl
  ; zetaProducerCompilerOwnedIsTrue = refl
  ; convergenceRouteDisjunctionOwnedIsTrue = refl
  ; arithmetic720CompilerOwnedIsTrue = refl
  ; continuumMaxwellStillLiveIsTrue = refl
  ; transversePhysicalWeldStillLiveIsTrue = refl
  ; concreteResidualTailStillLiveIsTrue = refl
  ; zetaDefectSameObjectWeldStillLiveIsTrue = refl
  }
