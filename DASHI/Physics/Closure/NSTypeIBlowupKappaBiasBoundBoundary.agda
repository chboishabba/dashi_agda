module DASHI.Physics.Closure.NSTypeIBlowupKappaBiasBoundBoundary where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)

import DASHI.Physics.Closure.NSBiotSavartStrainMeanSquareExactFormulaBoundary
  as MeanSquare
import DASHI.Physics.Closure.NSAbelTriadicDefectMeasureConstructionBoundary
  as AbelMeasure
import DASHI.Physics.Closure.NSCascadeKappaArcsineLawBoundary
  as Arcsine
import DASHI.Physics.Closure.NSCoherentStretchingExactFormulaBoundary
  as Stretching
import DASHI.Physics.Closure.NSLeiRenTianGreatCircleCriterionBoundary
  as LRT
import DASHI.Physics.Closure.NSTransferOperatorBiasNeutralityBoundary
  as TransferNeutrality
import DASHI.Physics.Closure.NSTriadicCompensatedLeakageIdentityBoundary
  as Leakage

------------------------------------------------------------------------
-- NS Type-I blowup kappa-bias bound boundary.
--
-- The finite S2 cascade package supplies the neutral kappa coordinates:
--
--   kappa has arcsine second moment E[kappa^2] = 1 / 2,
--   Omega_c dot S(c) Omega_c = lambda(c)(2 kappa^2 - 1),
--   hence the finite/background coordinates identify the zero-bias channel.
--
-- The live PDE gate is no longer "coherent triad domination" and is not a
-- separate finite-cascade theorem.  It is the conditional Type-I/
-- self-similar Abel-triadic bias estimate
--
--   Bias_kappa(mu)
--     = int lambda(c) (kappa^2 - 1 / 2) d mu
--     <= 0
--
-- conditional on:
--
--   AbelTriadicDefectMeasureConstruction,
--   approximate transfer-operator stationarity,
--   NSTransferOperatorBiasNeutrality.
--
-- This module records that collapsed dependency target only.  It proves no
-- PDE measure construction, no stationarity theorem, no transfer-operator
-- bias-neutrality theorem, no residual depletion, no Navier-Stokes Clay
-- theorem, and no terminal promotion.

data List (A : Set) : Set where
  [] :
    List A
  _∷_ :
    A →
    List A →
    List A

infixr 5 _∷_

listLength : {A : Set} → List A → Nat
listLength [] =
  zero
listLength (_ ∷ xs) =
  suc (listLength xs)

data ⊥ : Set where

data TypeIBlowupKappaBiasObject : Set where
  typeISelfSimilarVelocityProfile :
    TypeIBlowupKappaBiasObject
  gaussianWeightedSelfSimilarVorticityProfile :
    TypeIBlowupKappaBiasObject
  abelTriadicMeasureOnPropagatedLerayCascade :
    TypeIBlowupKappaBiasObject
  outputDirectionProjectionSupport :
    TypeIBlowupKappaBiasObject
  kappaCoordinateFromPropagatedPolarization :
    TypeIBlowupKappaBiasObject
  biotSavartStrainEigenvalueLambda :
    TypeIBlowupKappaBiasObject

canonicalTypeIBlowupKappaBiasObjects :
  List TypeIBlowupKappaBiasObject
canonicalTypeIBlowupKappaBiasObjects =
  typeISelfSimilarVelocityProfile
  ∷ gaussianWeightedSelfSimilarVorticityProfile
  ∷ abelTriadicMeasureOnPropagatedLerayCascade
  ∷ outputDirectionProjectionSupport
  ∷ kappaCoordinateFromPropagatedPolarization
  ∷ biotSavartStrainEigenvalueLambda
  ∷ []

typeIBlowupKappaBiasObjectCount : Nat
typeIBlowupKappaBiasObjectCount =
  listLength canonicalTypeIBlowupKappaBiasObjects

typeIBlowupKappaBiasObjectCountIs6 :
  typeIBlowupKappaBiasObjectCount ≡ 6
typeIBlowupKappaBiasObjectCountIs6 =
  refl

data KappaBiasFunctionalClause : Set where
  biasFunctionalIsIntegralAgainstAbelTriadicMeasure :
    KappaBiasFunctionalClause
  integrandIsLambdaTimesKappaSquaredMinusOneHalf :
    KappaBiasFunctionalClause
  arcsineNeutralBaselineHasZeroBias :
    KappaBiasFunctionalClause
  transferOperatorStationaryNeutralityHasZeroBias :
    KappaBiasFunctionalClause
  positiveBiasWouldBeBlowupDrivingStretchingSelection :
    KappaBiasFunctionalClause
  elevenSixtiethMeanSquareSetsNaturalLambdaScale :
    KappaBiasFunctionalClause

canonicalKappaBiasFunctionalClauses :
  List KappaBiasFunctionalClause
canonicalKappaBiasFunctionalClauses =
  biasFunctionalIsIntegralAgainstAbelTriadicMeasure
  ∷ integrandIsLambdaTimesKappaSquaredMinusOneHalf
  ∷ arcsineNeutralBaselineHasZeroBias
  ∷ transferOperatorStationaryNeutralityHasZeroBias
  ∷ positiveBiasWouldBeBlowupDrivingStretchingSelection
  ∷ elevenSixtiethMeanSquareSetsNaturalLambdaScale
  ∷ []

kappaBiasFunctionalClauseCount : Nat
kappaBiasFunctionalClauseCount =
  listLength canonicalKappaBiasFunctionalClauses

kappaBiasFunctionalClauseCountIs6 :
  kappaBiasFunctionalClauseCount ≡ 6
kappaBiasFunctionalClauseCountIs6 =
  refl

data TypeIBlowupKappaBiasInput : Set where
  arcsineKappaLawSupport :
    TypeIBlowupKappaBiasInput
  exactStretchingFormulaSupport :
    TypeIBlowupKappaBiasInput
  approximateTransferOperatorStationaritySupport :
    TypeIBlowupKappaBiasInput
  nsTransferOperatorBiasNeutralitySupport :
    TypeIBlowupKappaBiasInput
  meanSquareStrainElevenSixtiethSupport :
    TypeIBlowupKappaBiasInput
  leiRenTianGreatCircleOutputSupportInput :
    TypeIBlowupKappaBiasInput
  typeISelfSimilarGaussianMeasureInput :
    TypeIBlowupKappaBiasInput
  abelTriadicMeasureConstructionInput :
    TypeIBlowupKappaBiasInput

canonicalTypeIBlowupKappaBiasInputs :
  List TypeIBlowupKappaBiasInput
canonicalTypeIBlowupKappaBiasInputs =
  arcsineKappaLawSupport
  ∷ exactStretchingFormulaSupport
  ∷ approximateTransferOperatorStationaritySupport
  ∷ nsTransferOperatorBiasNeutralitySupport
  ∷ meanSquareStrainElevenSixtiethSupport
  ∷ leiRenTianGreatCircleOutputSupportInput
  ∷ typeISelfSimilarGaussianMeasureInput
  ∷ abelTriadicMeasureConstructionInput
  ∷ []

typeIBlowupKappaBiasInputCount : Nat
typeIBlowupKappaBiasInputCount =
  listLength canonicalTypeIBlowupKappaBiasInputs

typeIBlowupKappaBiasInputCountIs8 :
  typeIBlowupKappaBiasInputCount ≡ 8
typeIBlowupKappaBiasInputCountIs8 =
  refl

data TypeIBlowupKappaBiasCollapsedDependency : Set where
  abelTriadicDefectMeasureConstructionDependency :
    TypeIBlowupKappaBiasCollapsedDependency
  approximateTransferOperatorStationarityDependency :
    TypeIBlowupKappaBiasCollapsedDependency
  nsTransferOperatorBiasNeutralityDependency :
    TypeIBlowupKappaBiasCollapsedDependency

canonicalTypeIBlowupKappaBiasCollapsedDependencies :
  List TypeIBlowupKappaBiasCollapsedDependency
canonicalTypeIBlowupKappaBiasCollapsedDependencies =
  abelTriadicDefectMeasureConstructionDependency
  ∷ approximateTransferOperatorStationarityDependency
  ∷ nsTransferOperatorBiasNeutralityDependency
  ∷ []

typeIBlowupKappaBiasCollapsedDependencyCount : Nat
typeIBlowupKappaBiasCollapsedDependencyCount =
  listLength canonicalTypeIBlowupKappaBiasCollapsedDependencies

typeIBlowupKappaBiasCollapsedDependencyCountIs3 :
  typeIBlowupKappaBiasCollapsedDependencyCount ≡ 3
typeIBlowupKappaBiasCollapsedDependencyCountIs3 =
  refl

data GaussianSelfSimilarObligation : Set where
  backwardSelfSimilarVelocityEquation :
    GaussianSelfSimilarObligation
  vorticityEquationWithStretchingAndLaplacian :
    GaussianSelfSimilarObligation
  gaussianOrnsteinUhlenbeckIntegrationByParts :
    GaussianSelfSimilarObligation
  driftAndViscosityDissipativeSign :
    GaussianSelfSimilarObligation
  pressureAndTransportTermsDoNotCreatePositiveKappaBias :
    GaussianSelfSimilarObligation
  passageFromProfileIdentityToAbelTriadicMeasure :
    GaussianSelfSimilarObligation

canonicalGaussianSelfSimilarObligations :
  List GaussianSelfSimilarObligation
canonicalGaussianSelfSimilarObligations =
  backwardSelfSimilarVelocityEquation
  ∷ vorticityEquationWithStretchingAndLaplacian
  ∷ gaussianOrnsteinUhlenbeckIntegrationByParts
  ∷ driftAndViscosityDissipativeSign
  ∷ pressureAndTransportTermsDoNotCreatePositiveKappaBias
  ∷ passageFromProfileIdentityToAbelTriadicMeasure
  ∷ []

gaussianSelfSimilarObligationCount : Nat
gaussianSelfSimilarObligationCount =
  listLength canonicalGaussianSelfSimilarObligations

gaussianSelfSimilarObligationCountIs6 :
  gaussianSelfSimilarObligationCount ≡ 6
gaussianSelfSimilarObligationCountIs6 =
  refl

data TypeIBlowupKappaBiasBlocker : Set where
  missingTypeISelfSimilarAbelTriadicMeasureConstruction :
    TypeIBlowupKappaBiasBlocker
  missingApproximateTransferOperatorStationarity :
    TypeIBlowupKappaBiasBlocker
  missingNSTransferOperatorBiasNeutrality :
    TypeIBlowupKappaBiasBlocker
  missingLeiRenTianOutputSupportTransferToMeasure :
    TypeIBlowupKappaBiasBlocker
  missingGaussianSelfSimilarDriftViscosityIdentity :
    TypeIBlowupKappaBiasBlocker
  missingKappaBiasNonPositiveVariationalProof :
    TypeIBlowupKappaBiasBlocker
  missingTriadicCompensatedLeakageIdentity :
    TypeIBlowupKappaBiasBlocker
  missingCriticalResidualAndCKNBKMClosure :
    TypeIBlowupKappaBiasBlocker

canonicalTypeIBlowupKappaBiasBlockers :
  List TypeIBlowupKappaBiasBlocker
canonicalTypeIBlowupKappaBiasBlockers =
  missingTypeISelfSimilarAbelTriadicMeasureConstruction
  ∷ missingApproximateTransferOperatorStationarity
  ∷ missingNSTransferOperatorBiasNeutrality
  ∷ missingLeiRenTianOutputSupportTransferToMeasure
  ∷ missingGaussianSelfSimilarDriftViscosityIdentity
  ∷ missingKappaBiasNonPositiveVariationalProof
  ∷ missingTriadicCompensatedLeakageIdentity
  ∷ missingCriticalResidualAndCKNBKMClosure
  ∷ []

typeIBlowupKappaBiasBlockerCount : Nat
typeIBlowupKappaBiasBlockerCount =
  listLength canonicalTypeIBlowupKappaBiasBlockers

typeIBlowupKappaBiasBlockerCountIs8 :
  typeIBlowupKappaBiasBlockerCount ≡ 8
typeIBlowupKappaBiasBlockerCountIs8 =
  refl

data NSTypeIBlowupKappaBiasPromotion : Set where

nsTypeIBlowupKappaBiasPromotionImpossibleHere :
  NSTypeIBlowupKappaBiasPromotion →
  ⊥
nsTypeIBlowupKappaBiasPromotionImpossibleHere ()

typeIBlowupKappaBiasBoundProved : Bool
typeIBlowupKappaBiasBoundProved =
  false

gaussianSelfSimilarDriftViscosityObligationDischarged : Bool
gaussianSelfSimilarDriftViscosityObligationDischarged =
  false

lrtConstrainedSupportTransferProved : Bool
lrtConstrainedSupportTransferProved =
  false

abelTriadicMeasureConstructionProved : Bool
abelTriadicMeasureConstructionProved =
  false

approximateTransferOperatorStationarityProved : Bool
approximateTransferOperatorStationarityProved =
  false

nsTransferOperatorBiasNeutralityProved : Bool
nsTransferOperatorBiasNeutralityProved =
  false

triadicCompensatedLeakageIdentityProved : Bool
triadicCompensatedLeakageIdentityProved =
  false

nsCriticalResidualNonPositiveProved : Bool
nsCriticalResidualNonPositiveProved =
  false

clayNavierStokesPromoted : Bool
clayNavierStokesPromoted =
  false

terminalPromotion : Bool
terminalPromotion =
  false

data NSTypeIBlowupKappaBiasBoundStatus : Set where
  typeIBlowupKappaBiasBoundRecorded_openPDEGate_noPromotion :
    NSTypeIBlowupKappaBiasBoundStatus

nsTypeIBlowupKappaBiasBoundSummary : String
nsTypeIBlowupKappaBiasBoundSummary =
  "Records the collapsed live NS PDE gate: the Type-I kappa-bias bound is conditional on AbelTriadicDefectMeasureConstruction, approximate transfer-operator stationarity, and NSTransferOperatorBiasNeutrality.  The finite arcsine/stretching coordinates supply the neutral channel only; there is no separate finite-cascade theorem and no promotion."

record ImportedKappaCoordinateSupport : Set where
  field
    arcsineBoundary :
      Arcsine.NSCascadeKappaArcsineLawBoundary
    arcsineBoundaryIsCanonical :
      arcsineBoundary ≡ Arcsine.canonicalNSCascadeKappaArcsineLawBoundary
    stretchingBoundary :
      Stretching.NSCoherentStretchingExactFormulaBoundary
    stretchingBoundaryIsCanonical :
      stretchingBoundary
        ≡ Stretching.canonicalNSCoherentStretchingExactFormulaBoundary
    meanSquareBoundary :
      MeanSquare.NSBiotSavartStrainMeanSquareExactFormulaBoundary
    meanSquareBoundaryIsCanonical :
      meanSquareBoundary
        ≡ MeanSquare.canonicalNSBiotSavartStrainMeanSquareExactFormulaBoundary

canonicalImportedKappaCoordinateSupport :
  ImportedKappaCoordinateSupport
canonicalImportedKappaCoordinateSupport =
  record
    { arcsineBoundary =
        Arcsine.canonicalNSCascadeKappaArcsineLawBoundary
    ; arcsineBoundaryIsCanonical =
        refl
    ; stretchingBoundary =
        Stretching.canonicalNSCoherentStretchingExactFormulaBoundary
    ; stretchingBoundaryIsCanonical =
        refl
    ; meanSquareBoundary =
        MeanSquare.canonicalNSBiotSavartStrainMeanSquareExactFormulaBoundary
    ; meanSquareBoundaryIsCanonical =
        refl
    }

record ImportedCollapsedKappaBiasDependencies : Set where
  field
    abelMeasureBoundary :
      AbelMeasure.NSAbelTriadicDefectMeasureConstructionBoundary
    abelMeasureBoundaryIsCanonical :
      abelMeasureBoundary
        ≡ AbelMeasure.canonicalNSAbelTriadicDefectMeasureConstructionBoundary
    approximateTransferOperatorStationarityRecorded :
      Bool
    approximateTransferOperatorStationarityRecordedIsFalse :
      approximateTransferOperatorStationarityRecorded ≡ false
    nsTransferOperatorBiasNeutralityBoundary :
      TransferNeutrality.NSTransferOperatorBiasNeutralityBoundary
    nsTransferOperatorBiasNeutralityBoundaryIsCanonical :
      nsTransferOperatorBiasNeutralityBoundary
        ≡ TransferNeutrality.canonicalNSTransferOperatorBiasNeutralityBoundary
    nsTransferOperatorBiasNeutralityStillConditional :
      TransferNeutrality.finiteStatisticalClaimConditional ≡ true
    nsTransferOperatorBiasNeutralityDoesNotPromoteTypeIBias :
      TransferNeutrality.typeIBiasBoundPromoted ≡ false

canonicalImportedCollapsedKappaBiasDependencies :
  ImportedCollapsedKappaBiasDependencies
canonicalImportedCollapsedKappaBiasDependencies =
  record
    { abelMeasureBoundary =
        AbelMeasure.canonicalNSAbelTriadicDefectMeasureConstructionBoundary
    ; abelMeasureBoundaryIsCanonical =
        refl
    ; approximateTransferOperatorStationarityRecorded =
        false
    ; approximateTransferOperatorStationarityRecordedIsFalse =
        refl
    ; nsTransferOperatorBiasNeutralityBoundary =
        TransferNeutrality.canonicalNSTransferOperatorBiasNeutralityBoundary
    ; nsTransferOperatorBiasNeutralityBoundaryIsCanonical =
        refl
    ; nsTransferOperatorBiasNeutralityStillConditional =
        refl
    ; nsTransferOperatorBiasNeutralityDoesNotPromoteTypeIBias =
        refl
    }

record ImportedAnalyticSupportBoundaries : Set where
  field
    leiRenTianGreatCircleCriterionInputRecorded :
      Bool
    leiRenTianGreatCircleCriterionInputRecordedIsTrue :
      leiRenTianGreatCircleCriterionInputRecorded ≡ true
    leakageBoundary :
      Leakage.NSTriadicCompensatedLeakageIdentityBoundary
    leakageBoundaryIsCanonical :
      leakageBoundary
        ≡ Leakage.canonicalNSTriadicCompensatedLeakageIdentityBoundary

canonicalImportedAnalyticSupportBoundaries :
  ImportedAnalyticSupportBoundaries
canonicalImportedAnalyticSupportBoundaries =
  record
    { leiRenTianGreatCircleCriterionInputRecorded =
        true
    ; leiRenTianGreatCircleCriterionInputRecordedIsTrue =
        refl
    ; leakageBoundary =
        Leakage.canonicalNSTriadicCompensatedLeakageIdentityBoundary
    ; leakageBoundaryIsCanonical =
        refl
    }

record NSTypeIBlowupKappaBiasBoundBoundary : Set where
  field
    status :
      NSTypeIBlowupKappaBiasBoundStatus
    statusIsCanonical :
      status
        ≡ typeIBlowupKappaBiasBoundRecorded_openPDEGate_noPromotion
    kappaCoordinateSupport :
      ImportedKappaCoordinateSupport
    kappaCoordinateSupportIsCanonical :
      kappaCoordinateSupport ≡ canonicalImportedKappaCoordinateSupport
    collapsedDependencies :
      ImportedCollapsedKappaBiasDependencies
    collapsedDependenciesAreCanonical :
      collapsedDependencies
        ≡ canonicalImportedCollapsedKappaBiasDependencies
    analyticSupportBoundaries :
      ImportedAnalyticSupportBoundaries
    analyticSupportBoundariesAreCanonical :
      analyticSupportBoundaries
        ≡ canonicalImportedAnalyticSupportBoundaries
    objects :
      List TypeIBlowupKappaBiasObject
    objectsAreCanonical :
      objects ≡ canonicalTypeIBlowupKappaBiasObjects
    objectCountIsSix :
      typeIBlowupKappaBiasObjectCount ≡ 6
    functionalClauses :
      List KappaBiasFunctionalClause
    functionalClausesAreCanonical :
      functionalClauses ≡ canonicalKappaBiasFunctionalClauses
    functionalClauseCountIsSix :
      kappaBiasFunctionalClauseCount ≡ 6
    inputs :
      List TypeIBlowupKappaBiasInput
    inputsAreCanonical :
      inputs ≡ canonicalTypeIBlowupKappaBiasInputs
    inputCountIsEight :
      typeIBlowupKappaBiasInputCount ≡ 8
    collapsedDependencyRows :
      List TypeIBlowupKappaBiasCollapsedDependency
    collapsedDependencyRowsAreCanonical :
      collapsedDependencyRows
        ≡ canonicalTypeIBlowupKappaBiasCollapsedDependencies
    collapsedDependencyCountIsThree :
      typeIBlowupKappaBiasCollapsedDependencyCount ≡ 3
    gaussianObligations :
      List GaussianSelfSimilarObligation
    gaussianObligationsAreCanonical :
      gaussianObligations ≡ canonicalGaussianSelfSimilarObligations
    gaussianObligationCountIsSix :
      gaussianSelfSimilarObligationCount ≡ 6
    blockers :
      List TypeIBlowupKappaBiasBlocker
    blockersAreCanonical :
      blockers ≡ canonicalTypeIBlowupKappaBiasBlockers
    blockerCountIsEight :
      typeIBlowupKappaBiasBlockerCount ≡ 8
    typeIBlowupKappaBiasBoundProvedIsFalse :
      typeIBlowupKappaBiasBoundProved ≡ false
    gaussianSelfSimilarDriftViscosityObligationDischargedIsFalse :
      gaussianSelfSimilarDriftViscosityObligationDischarged ≡ false
    lrtConstrainedSupportTransferProvedIsFalse :
      lrtConstrainedSupportTransferProved ≡ false
    abelTriadicMeasureConstructionProvedIsFalse :
      abelTriadicMeasureConstructionProved ≡ false
    approximateTransferOperatorStationarityProvedIsFalse :
      approximateTransferOperatorStationarityProved ≡ false
    nsTransferOperatorBiasNeutralityProvedIsFalse :
      nsTransferOperatorBiasNeutralityProved ≡ false
    triadicCompensatedLeakageIdentityProvedIsFalse :
      triadicCompensatedLeakageIdentityProved ≡ false
    nsCriticalResidualNonPositiveProvedIsFalse :
      nsCriticalResidualNonPositiveProved ≡ false
    clayNavierStokesPromotedIsFalse :
      clayNavierStokesPromoted ≡ false
    terminalPromotionIsFalse :
      terminalPromotion ≡ false
    summary :
      String
    summaryIsCanonical :
      summary ≡ nsTypeIBlowupKappaBiasBoundSummary

canonicalNSTypeIBlowupKappaBiasBoundBoundary :
  NSTypeIBlowupKappaBiasBoundBoundary
canonicalNSTypeIBlowupKappaBiasBoundBoundary =
  record
    { status =
        typeIBlowupKappaBiasBoundRecorded_openPDEGate_noPromotion
    ; statusIsCanonical =
        refl
    ; kappaCoordinateSupport =
        canonicalImportedKappaCoordinateSupport
    ; kappaCoordinateSupportIsCanonical =
        refl
    ; collapsedDependencies =
        canonicalImportedCollapsedKappaBiasDependencies
    ; collapsedDependenciesAreCanonical =
        refl
    ; analyticSupportBoundaries =
        canonicalImportedAnalyticSupportBoundaries
    ; analyticSupportBoundariesAreCanonical =
        refl
    ; objects =
        canonicalTypeIBlowupKappaBiasObjects
    ; objectsAreCanonical =
        refl
    ; objectCountIsSix =
        refl
    ; functionalClauses =
        canonicalKappaBiasFunctionalClauses
    ; functionalClausesAreCanonical =
        refl
    ; functionalClauseCountIsSix =
        refl
    ; inputs =
        canonicalTypeIBlowupKappaBiasInputs
    ; inputsAreCanonical =
        refl
    ; inputCountIsEight =
        refl
    ; collapsedDependencyRows =
        canonicalTypeIBlowupKappaBiasCollapsedDependencies
    ; collapsedDependencyRowsAreCanonical =
        refl
    ; collapsedDependencyCountIsThree =
        refl
    ; gaussianObligations =
        canonicalGaussianSelfSimilarObligations
    ; gaussianObligationsAreCanonical =
        refl
    ; gaussianObligationCountIsSix =
        refl
    ; blockers =
        canonicalTypeIBlowupKappaBiasBlockers
    ; blockersAreCanonical =
        refl
    ; blockerCountIsEight =
        refl
    ; typeIBlowupKappaBiasBoundProvedIsFalse =
        refl
    ; gaussianSelfSimilarDriftViscosityObligationDischargedIsFalse =
        refl
    ; lrtConstrainedSupportTransferProvedIsFalse =
        refl
    ; abelTriadicMeasureConstructionProvedIsFalse =
        refl
    ; approximateTransferOperatorStationarityProvedIsFalse =
        refl
    ; nsTransferOperatorBiasNeutralityProvedIsFalse =
        refl
    ; triadicCompensatedLeakageIdentityProvedIsFalse =
        refl
    ; nsCriticalResidualNonPositiveProvedIsFalse =
        refl
    ; clayNavierStokesPromotedIsFalse =
        refl
    ; terminalPromotionIsFalse =
        refl
    ; summary =
        nsTypeIBlowupKappaBiasBoundSummary
    ; summaryIsCanonical =
        refl
    }

nsTypeIBlowupKappaBiasBoundKeepsTheoremFalse :
  typeIBlowupKappaBiasBoundProved ≡ false
nsTypeIBlowupKappaBiasBoundKeepsTheoremFalse =
  refl

nsTypeIBlowupKappaBiasBoundKeepsClayFalse :
  clayNavierStokesPromoted ≡ false
nsTypeIBlowupKappaBiasBoundKeepsClayFalse =
  refl

nsTypeIBlowupKappaBiasBoundKeepsTerminalFalse :
  terminalPromotion ≡ false
nsTypeIBlowupKappaBiasBoundKeepsTerminalFalse =
  refl
