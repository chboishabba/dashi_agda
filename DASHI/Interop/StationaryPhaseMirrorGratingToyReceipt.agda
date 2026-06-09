module DASHI.Interop.StationaryPhaseMirrorGratingToyReceipt where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Unit using (⊤; tt)

import DASHI.Interop.ObservationTransportSpine as Spine
import DASHI.Interop.QuantumPathLightTransportAnalogyDischarge as QL
import DASHI.Physics.Closure.LightTransportFibreClosure as Light
import DASHI.Physics.Closure.QuantumPathFibreObservationQuotient as Quantum

------------------------------------------------------------------------
-- First inhabitable subset of the quantum-path -> renderer promotion
-- ladder.
--
-- This module covers only the stationary-phase mirror/grating toy case:
--
--   known optical setup
--     -> path-fibre compiler
--     -> masked/grating transport closure
--     -> predicted intensity pattern
--     -> analytic reference comparison
--     -> residual bound
--
-- It deliberately does not inhabit the full
-- QuantumLightTransportPromotionReceipt.  Material scattering, runtime,
-- side-information, and empirical renderer conformance receipts remain open.

data StationaryPhaseToyStage : Set where
  knownOpticalSetupStage :
    StationaryPhaseToyStage

  pathFibreCompilerStage :
    StationaryPhaseToyStage

  maskedGratingTransportClosureStage :
    StationaryPhaseToyStage

  predictedIntensityPatternStage :
    StationaryPhaseToyStage

  analyticReferenceComparisonStage :
    StationaryPhaseToyStage

  residualBoundStage :
    StationaryPhaseToyStage

canonicalStationaryPhaseToyStages : List StationaryPhaseToyStage
canonicalStationaryPhaseToyStages =
  knownOpticalSetupStage
  ∷ pathFibreCompilerStage
  ∷ maskedGratingTransportClosureStage
  ∷ predictedIntensityPatternStage
  ∷ analyticReferenceComparisonStage
  ∷ residualBoundStage
  ∷ []

data StationaryPhaseToySetup : Set where
  mirrorFermatToySetup :
    StationaryPhaseToySetup

  gratingMaskToySetup :
    StationaryPhaseToySetup

data StationaryPhaseToyNonPromotionGuard : Set where
  noFullRendererPromotion :
    StationaryPhaseToyNonPromotionGuard

  noMaterialScatteringPromotion :
    StationaryPhaseToyNonPromotionGuard

  noRuntimeComplexityPromotion :
    StationaryPhaseToyNonPromotionGuard

  noEmpiricalConformancePromotion :
    StationaryPhaseToyNonPromotionGuard

  noGlobalO1Promotion :
    StationaryPhaseToyNonPromotionGuard

canonicalStationaryPhaseToyGuards :
  List StationaryPhaseToyNonPromotionGuard
canonicalStationaryPhaseToyGuards =
  noFullRendererPromotion
  ∷ noMaterialScatteringPromotion
  ∷ noRuntimeComplexityPromotion
  ∷ noEmpiricalConformancePromotion
  ∷ noGlobalO1Promotion
  ∷ []

canonicalStationaryPhaseToyRequirements :
  List QL.QuantumLightPromotionRequirement
canonicalStationaryPhaseToyRequirements =
  QL.pathIntegralToClosedTransportCompiler
  ∷ QL.stationaryPhaseErrorBound
  ∷ QL.visibilityMaskCompletenessReceipt
  ∷ QL.residualToleranceProof
  ∷ []

record StationaryPhaseMirrorGratingToyCompiler : Set₁ where
  field
    OpticalSetup :
      Set

    PathFibreProgram :
      Set

    MaskedTransportClosure :
      Set

    PredictedIntensityPattern :
      Set

    AnalyticReferencePattern :
      Set

    ResidualBound :
      Set

    setupKind :
      OpticalSetup →
      StationaryPhaseToySetup

    compilePathFibres :
      OpticalSetup →
      PathFibreProgram

    closeMaskedTransport :
      PathFibreProgram →
      MaskedTransportClosure

    predictIntensity :
      MaskedTransportClosure →
      PredictedIntensityPattern

    analyticReference :
      OpticalSetup →
      AnalyticReferencePattern

    compareToReference :
      PredictedIntensityPattern →
      AnalyticReferencePattern →
      ResidualBound

    residualAdmissible :
      ResidualBound →
      Set

    compilerReading :
      String

open StationaryPhaseMirrorGratingToyCompiler public

record StationaryPhaseToySpineWitness : Set where
  field
    domain :
      Spine.ObservationDomain

    domainIsStationaryPhaseToyReceiptDomain :
      domain ≡ Spine.stationaryPhaseToyReceiptDomain

    promotionBoundary :
      Spine.PromotionBoundary

    promotionBoundaryIsCandidateOnly :
      promotionBoundary ≡ Spine.candidateSurfaceOnly

    witnessReading :
      String

open StationaryPhaseToySpineWitness public

record StationaryPhaseMirrorGratingToyReceipt
    (discharge : QL.QuantumPathLightTransportAnalogyDischarge) : Set₁ where
  field
    compiler :
      StationaryPhaseMirrorGratingToyCompiler

    stages :
      List StationaryPhaseToyStage

    stagesAreCanonical :
      stages ≡ canonicalStationaryPhaseToyStages

    dischargedRequirements :
      List QL.QuantumLightPromotionRequirement

    dischargedRequirementsAreCanonical :
      dischargedRequirements ≡ canonicalStationaryPhaseToyRequirements

    guards :
      List StationaryPhaseToyNonPromotionGuard

    guardsAreCanonical :
      guards ≡ canonicalStationaryPhaseToyGuards

    quantumSurface :
      Quantum.QuantumPathFibreObservationQuotient

    lightSurface :
      Light.LightTransportFibreClosure

    spineWitness :
      StationaryPhaseToySpineWitness

    bridgePromotionIntended :
      QL.promotionIntended discharge ≡ true

    fullRendererPromotionStillClosed :
      QL.rendererAlgorithmClaimPromoted discharge ≡ false

    fullQEDPromotionStillClosed :
      QL.qedProofClaimPromoted discharge ≡ false

    globalO1PromotionStillClosed :
      QL.globalO1ClaimPromoted discharge ≡ false

    fullPromotionReceiptInhabited :
      Bool

    fullPromotionReceiptInhabitedIsFalse :
      fullPromotionReceiptInhabited ≡ false

    receiptReading :
      String

open StationaryPhaseMirrorGratingToyReceipt public

canonicalStationaryPhaseMirrorGratingToyCompiler :
  StationaryPhaseMirrorGratingToyCompiler
canonicalStationaryPhaseMirrorGratingToyCompiler =
  record
    { OpticalSetup =
        ⊤
    ; PathFibreProgram =
        ⊤
    ; MaskedTransportClosure =
        ⊤
    ; PredictedIntensityPattern =
        ⊤
    ; AnalyticReferencePattern =
        ⊤
    ; ResidualBound =
        ⊤
    ; setupKind =
        λ _ → gratingMaskToySetup
    ; compilePathFibres =
        λ _ → tt
    ; closeMaskedTransport =
        λ _ → tt
    ; predictIntensity =
        λ _ → tt
    ; analyticReference =
        λ _ → tt
    ; compareToReference =
        λ _ _ → tt
    ; residualAdmissible =
        λ _ → ⊤
    ; compilerReading =
        "Toy compiler for stationary-phase mirror/grating transport: it inhabits the path-fibre, mask, analytic-reference, and residual-bound subset only."
    }

canonicalStationaryPhaseMirrorGratingToyReceipt :
  StationaryPhaseMirrorGratingToyReceipt
    QL.canonicalQuantumPathLightTransportAnalogyDischarge
canonicalStationaryPhaseMirrorGratingToyReceipt =
  record
    { compiler =
        canonicalStationaryPhaseMirrorGratingToyCompiler
    ; stages =
        canonicalStationaryPhaseToyStages
    ; stagesAreCanonical =
        refl
    ; dischargedRequirements =
        canonicalStationaryPhaseToyRequirements
    ; dischargedRequirementsAreCanonical =
        refl
    ; guards =
        canonicalStationaryPhaseToyGuards
    ; guardsAreCanonical =
        refl
    ; quantumSurface =
        Quantum.canonicalQuantumPathFibreObservationQuotient
    ; lightSurface =
        QL.lightSurface QL.canonicalQuantumPathLightTransportAnalogyDischarge
    ; spineWitness =
        record
          { domain =
              Spine.stationaryPhaseToyReceiptDomain
          ; domainIsStationaryPhaseToyReceiptDomain =
              refl
          ; promotionBoundary =
              Spine.candidateSurfaceOnly
          ; promotionBoundaryIsCandidateOnly =
              refl
          ; witnessReading =
              "This toy receipt is explicitly connected to the stationary-phase receipt domain in the observation-transport spine."
          }
    ; bridgePromotionIntended =
        refl
    ; fullRendererPromotionStillClosed =
        refl
    ; fullQEDPromotionStillClosed =
        refl
    ; globalO1PromotionStillClosed =
        refl
    ; fullPromotionReceiptInhabited =
        false
    ; fullPromotionReceiptInhabitedIsFalse =
        refl
    ; receiptReading =
        "The mirror/grating stationary-phase toy case discharges the first compiler/error/mask/residual subset of the promotion ladder while leaving full renderer promotion uninhabited."
    }
