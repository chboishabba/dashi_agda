module DASHI.Biology.MoonshineGradedStageBridgeExact where

open import DASHI.Core.Prelude

import DASHI.Biology.ReducedFiftyThreeFibreExact as Reduced
import DASHI.Biology.TernaryHypercubeHyperfabricExact as Hyper

------------------------------------------------------------------------
-- Additive stage progression after the completed nonary sheet.  This is kept
-- separate from the analytic modular coordinate q = exp(2 pi i tau).

data PostNonaryStage : Set where
  stage9 : PostNonaryStage
  stage10 : PostNonaryStage
  stage11 : PostNonaryStage
  stage12 : PostNonaryStage

stageNumber : PostNonaryStage → Nat
stageNumber stage9 = 9
stageNumber stage10 = 10
stageNumber stage11 = 11
stageNumber stage12 = 12

nextStage : PostNonaryStage → PostNonaryStage
nextStage stage9 = stage10
nextStage stage10 = stage11
nextStage stage11 = stage12
nextStage stage12 = stage12

stageNineAdvancesToTen : nextStage stage9 ≡ stage10
stageNineAdvancesToTen = refl

stageTenAdvancesToEleven : nextStage stage10 ≡ stage11
stageTenAdvancesToEleven = refl

stageElevenAdvancesToTwelve : nextStage stage11 ≡ stage12
stageElevenAdvancesToTwelve = refl

------------------------------------------------------------------------
-- Modular/moonshine pipeline is typed rather than collapsed into one map.

data ModularPipelineStage : Set where
  upperHalfPlanePhase : ModularPipelineStage
  exponentialQCoordinate : ModularPipelineStage
  modularInvariantValue : ModularPipelineStage
  gradedRepresentationCoefficient : ModularPipelineStage

nextModularStage : ModularPipelineStage → ModularPipelineStage
nextModularStage upperHalfPlanePhase = exponentialQCoordinate
nextModularStage exponentialQCoordinate = modularInvariantValue
nextModularStage modularInvariantValue = gradedRepresentationCoefficient
nextModularStage gradedRepresentationCoefficient = gradedRepresentationCoefficient

record ModularCoordinatePipeline : Set₁ where
  constructor modularCoordinatePipeline
  field
    PhaseCoordinate : Set
    QCoordinate : Set
    ModularInvariant : Set
    GradedCoefficient : Set
    phaseToQ : PhaseCoordinate → QCoordinate
    qToInvariant : QCoordinate → ModularInvariant
    coefficientAt : ModularInvariant → Nat → GradedCoefficient

------------------------------------------------------------------------
-- Exact arithmetic visible in the first positive J coefficient.

ternaryExpansionOf196884 :
  Hyper.powNat 3 11
  + Hyper.powNat 3 9
  + 2 * Hyper.powNat 3 3
  ≡ 196884
ternaryExpansionOf196884 = refl

ternaryCoefficientDigits : List Nat
ternaryCoefficientDigits =
  1 ∷ 0 ∷ 1 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 2 ∷ 0 ∷ 0 ∷ 0 ∷ []

listCount : ∀ {A : Set} → List A → Nat
listCount [] = 0
listCount (_ ∷ xs) = suc (listCount xs)

evaluateBaseThreeDigits : List Nat → Nat
evaluateBaseThreeDigits [] = 0
evaluateBaseThreeDigits (digit ∷ digits) =
  digit * Hyper.powNat 3 (listCount digits)
  + evaluateBaseThreeDigits digits

ternaryDigitsEvaluateTo196884 :
  evaluateBaseThreeDigits ternaryCoefficientDigits ≡ 196884
ternaryDigitsEvaluateTo196884 = refl

ternaryFirstCoefficientCandidate : Nat
ternaryFirstCoefficientCandidate =
  10 * Hyper.ternaryLatticeCount 9
  + Reduced.fullSixByNineDimension

ternaryNontrivialCoefficientCandidate : Nat
ternaryNontrivialCoefficientCandidate =
  10 * Hyper.ternaryLatticeCount 9
  + Reduced.reducedDimension

firstCoefficientCandidateIs196884 :
  ternaryFirstCoefficientCandidate ≡ 196884
firstCoefficientCandidateIs196884 = refl

nontrivialCoefficientCandidateIs196883 :
  ternaryNontrivialCoefficientCandidate ≡ 196883
nontrivialCoefficientCandidateIs196883 = refl

record FirstGradedPieceCandidate : Set where
  constructor firstGradedPieceCandidate
  field
    ternaryNineFibres : Nat
    ternaryNineFibreDimension : Nat
    sixByNineFibreDimension : Nat
    totalCoefficient : Nat
    coefficientCertificate :
      ternaryNineFibres * ternaryNineFibreDimension
      + sixByNineFibreDimension
      ≡ totalCoefficient

open FirstGradedPieceCandidate public

canonicalFirstGradedPieceCandidate : FirstGradedPieceCandidate
canonicalFirstGradedPieceCandidate =
  firstGradedPieceCandidate 10 19683 54 196884 refl

record DualMoonshineObservation : Set where
  constructor dualMoonshineObservation
  field
    multiplicativeSSPValue : Nat
    additiveFabricValue : Nat
    multiplicativeCertificate : multiplicativeSSPValue ≡ 196883
    additiveCertificate : additiveFabricValue ≡ 196883

open DualMoonshineObservation public

canonicalDualMoonshineObservation : DualMoonshineObservation
canonicalDualMoonshineObservation =
  dualMoonshineObservation
    (47 * 59 * 71)
    ternaryNontrivialCoefficientCandidate
    refl
    nontrivialCoefficientCandidateIs196883

record MoonshineStageBoundary : Set where
  constructor moonshineStageBoundary
  field
    jInvariantIsIdentifiedWithOrdinaryExponentiation : Bool
    jInvariantIsIdentifiedWithOrdinaryExponentiationIsFalse :
      jInvariantIsIdentifiedWithOrdinaryExponentiation ≡ false

    stageNineToTwelveIsAProvedModularUniformization : Bool
    stageNineToTwelveIsAProvedModularUniformizationIsFalse :
      stageNineToTwelveIsAProvedModularUniformization ≡ false

    coefficientIdentityConstructsMonsterEquivariance : Bool
    coefficientIdentityConstructsMonsterEquivarianceIsFalse :
      coefficientIdentityConstructsMonsterEquivariance ≡ false

    exponentialCoordinateAndGradedCoefficientAreDistinctTypes : Bool
    exponentialCoordinateAndGradedCoefficientAreDistinctTypesIsTrue :
      exponentialCoordinateAndGradedCoefficientAreDistinctTypes ≡ true

open MoonshineStageBoundary public

canonicalMoonshineStageBoundary : MoonshineStageBoundary
canonicalMoonshineStageBoundary =
  moonshineStageBoundary false refl false refl false refl true refl
