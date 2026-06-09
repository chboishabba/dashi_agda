module DASHI.Interop.QuantumPathLightTransportAnalogyDischarge where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

import DASHI.Interop.ObservationTransportSpine as Spine
import DASHI.Physics.Closure.LightTransportFibreClosure as Light
import DASHI.Physics.Closure.QuantumPathFibreObservationQuotient as Quantum

------------------------------------------------------------------------
-- Promotion-gated discharge between quantum path fibres and renderer light
-- transport fibres.
--
-- The fetched thread tail sharpened the physics-side vocabulary:
--
--   admissible path fibres -> phase contribution -> observation quotient
--
-- Existing renderer light transport uses:
--
--   viewport/photon carrier -> geometry/material/spectral/visibility fibres
--     -> closed transport operator -> lit viewport
--
-- This module records the shared observation-transport discipline and the
-- explicit receipt gate for the stronger promotion target.  The canonical
-- inhabitant is still fail-closed because the receipts are not supplied here,
-- but the formalism now states that promotion is intended once those receipts
-- are inhabited.

data QuantumLightSharedAnalogySurface : Set where
  weightedFibreCarrierSurface :
    QuantumLightSharedAnalogySurface

  cancellationOrResidualSurface :
    QuantumLightSharedAnalogySurface

  quotientDependentObservationSurface :
    QuantumLightSharedAnalogySurface

  maskOrVisibilityTopologySurface :
    QuantumLightSharedAnalogySurface

  receiptGatedReuseSurface :
    QuantumLightSharedAnalogySurface

canonicalQuantumLightSharedSurfaces :
  List QuantumLightSharedAnalogySurface
canonicalQuantumLightSharedSurfaces =
  weightedFibreCarrierSurface
  ∷ cancellationOrResidualSurface
  ∷ quotientDependentObservationSurface
  ∷ maskOrVisibilityTopologySurface
  ∷ receiptGatedReuseSurface
  ∷ []

data QuantumLightAnalogyGuard : Set where
  QuantumPathIsNotRendererAlgorithm :
    QuantumLightAnalogyGuard

  RendererClosureIsNotQEDProof :
    QuantumLightAnalogyGuard

  NoRetrocausalRendererClaim :
    QuantumLightAnalogyGuard

  NoGlobalO1PhysicalExactnessClaim :
    QuantumLightAnalogyGuard

  NoHiddenResidualOrSideInfoDiscard :
    QuantumLightAnalogyGuard

  NoCollapseOrMeasurementTheorem :
    QuantumLightAnalogyGuard

canonicalQuantumLightAnalogyGuards :
  List QuantumLightAnalogyGuard
canonicalQuantumLightAnalogyGuards =
  QuantumPathIsNotRendererAlgorithm
  ∷ RendererClosureIsNotQEDProof
  ∷ NoRetrocausalRendererClaim
  ∷ NoGlobalO1PhysicalExactnessClaim
  ∷ NoHiddenResidualOrSideInfoDiscard
  ∷ NoCollapseOrMeasurementTheorem
  ∷ []

data QuantumLightPromotionRequirement : Set where
  pathIntegralToClosedTransportCompiler :
    QuantumLightPromotionRequirement

  stationaryPhaseErrorBound :
    QuantumLightPromotionRequirement

  materialScatteringLawReceipt :
    QuantumLightPromotionRequirement

  visibilityMaskCompletenessReceipt :
    QuantumLightPromotionRequirement

  residualToleranceProof :
    QuantumLightPromotionRequirement

  sideInformationBudgetProof :
    QuantumLightPromotionRequirement

  rendererRuntimeComplexityProof :
    QuantumLightPromotionRequirement

  empiricalRendererConformanceReceipt :
    QuantumLightPromotionRequirement

canonicalQuantumLightPromotionRequirements :
  List QuantumLightPromotionRequirement
canonicalQuantumLightPromotionRequirements =
  pathIntegralToClosedTransportCompiler
  ∷ stationaryPhaseErrorBound
  ∷ materialScatteringLawReceipt
  ∷ visibilityMaskCompletenessReceipt
  ∷ residualToleranceProof
  ∷ sideInformationBudgetProof
  ∷ rendererRuntimeComplexityProof
  ∷ empiricalRendererConformanceReceipt
  ∷ []

canonicalQuantumLightSpineDomains :
  List Spine.ObservationDomain
canonicalQuantumLightSpineDomains =
  Spine.quantumPathFibreDomain
  ∷ Spine.lightTransportDomain
  ∷ []

record QuantumPathLightTransportAnalogyDischarge : Set₁ where
  field
    quantumSurface :
      Quantum.QuantumPathFibreObservationQuotient

    quantumCertificate :
      Quantum.QuantumPathNonPromotionCertificate quantumSurface

    lightSurface :
      Light.LightTransportFibreClosure

    lightCertificate :
      Light.LightTransportNonPromotionCertificate lightSurface

    sharedSurfaces :
      List QuantumLightSharedAnalogySurface

    sharedSurfacesAreCanonical :
      sharedSurfaces ≡ canonicalQuantumLightSharedSurfaces

    spineDomains :
      List Spine.ObservationDomain

    spineDomainsAreCanonical :
      spineDomains ≡ canonicalQuantumLightSpineDomains

    guards :
      List QuantumLightAnalogyGuard

    guardsAreCanonical :
      guards ≡ canonicalQuantumLightAnalogyGuards

    rendererAlgorithmClaimPromoted :
      Bool

    rendererAlgorithmClaimPromotedIsFalse :
      rendererAlgorithmClaimPromoted ≡ false

    qedProofClaimPromoted :
      Bool

    qedProofClaimPromotedIsFalse :
      qedProofClaimPromoted ≡ false

    globalO1ClaimPromoted :
      Bool

    globalO1ClaimPromotedIsFalse :
      globalO1ClaimPromoted ≡ false

    promotionIntended :
      Bool

    promotionIntendedIsTrue :
      promotionIntended ≡ true

    promotionRequirements :
      List QuantumLightPromotionRequirement

    promotionRequirementsAreCanonical :
      promotionRequirements ≡ canonicalQuantumLightPromotionRequirements

    analogyReading :
      String

open QuantumPathLightTransportAnalogyDischarge public

canonicalQuantumPathLightTransportAnalogyDischarge :
  QuantumPathLightTransportAnalogyDischarge
canonicalQuantumPathLightTransportAnalogyDischarge =
  record
    { quantumSurface =
        Quantum.canonicalQuantumPathFibreObservationQuotient
    ; quantumCertificate =
        Quantum.canonicalQuantumPathNonPromotionCertificate
    ; lightSurface =
        LightCodecLightSurface
    ; lightCertificate =
        Light.canonicalLightTransportNonPromotionCertificate
          LightCodecLightSurface
    ; sharedSurfaces =
        canonicalQuantumLightSharedSurfaces
    ; sharedSurfacesAreCanonical =
        refl
    ; spineDomains =
        canonicalQuantumLightSpineDomains
    ; spineDomainsAreCanonical =
        refl
    ; guards =
        canonicalQuantumLightAnalogyGuards
    ; guardsAreCanonical =
        refl
    ; rendererAlgorithmClaimPromoted =
        false
    ; rendererAlgorithmClaimPromotedIsFalse =
        refl
    ; qedProofClaimPromoted =
        false
    ; qedProofClaimPromotedIsFalse =
        refl
    ; globalO1ClaimPromoted =
        false
    ; globalO1ClaimPromotedIsFalse =
        refl
    ; promotionIntended =
        true
    ; promotionIntendedIsTrue =
        refl
    ; promotionRequirements =
        canonicalQuantumLightPromotionRequirements
    ; promotionRequirementsAreCanonical =
        refl
    ; analogyReading =
        "Quantum path fibres and renderer light transport share a weighted-fibre observation vocabulary; promotion is intended but remains gated on the explicit compiler, error-bound, material, visibility, residual, side-information, runtime, and empirical conformance receipts."
    }
  where
    LightCodecLightSurface :
      Light.LightTransportFibreClosure
    LightCodecLightSurface =
      record
        { SceneState =
            Quantum.QuantumPathToken
        ; UnlitViewport =
            Quantum.QuantumPathToken
        ; PhotonOrPixelCarrier =
            Quantum.QuantumPathToken
        ; GeometryFibre =
            Quantum.QuantumPathToken
        ; MaterialFibre =
            Quantum.QuantumPathToken
        ; SpectralFibre =
            Quantum.QuantumPathToken
        ; VisibilityFibre =
            Quantum.QuantumPathToken
        ; TransportOperator =
            Quantum.QuantumPathToken
        ; ClosureReceipt =
            Quantum.QuantumPathToken
        ; ResidualDefect =
            Quantum.QuantumPathToken
        ; LitViewport =
            Quantum.QuantumPathToken
        ; baselineViewport =
            λ _ → Quantum.observationToken
        ; carrierFromViewport =
            λ _ → Quantum.genericFibreToken
        ; geometryFibre =
            λ _ _ → Quantum.genericFibreToken
        ; materialFibre =
            λ _ _ → Quantum.genericFibreToken
        ; spectralFibre =
            λ _ → Quantum.observationToken
        ; visibilityFibre =
            λ _ _ → Quantum.observationToken
        ; mixingMode =
            λ _ → Light.diffuseSplit
        ; compositionShape =
            λ _ → Light.cachedClosureChart
        ; closeTransport =
            λ _ _ _ _ → Quantum.observationToken
        ; applyClosedTransport =
            λ _ _ → Quantum.observationToken
        ; closureReceipt =
            λ _ → Quantum.observationToken
        ; residualDefect =
            λ _ _ → Quantum.observationToken
        ; residualAdmissible =
            λ _ → Quantum.QuantumPathToken
        ; gateSatisfied =
            λ _ _ → Quantum.QuantumPathToken
        ; pipeline =
            Light.canonicalLightTransportPipeline
        ; transportReading =
            "Toy renderer-side light surface for promotion-gated linkage to quantum path fibres."
        }

record QuantumLightTransportPromotionReceipt
    (discharge : QuantumPathLightTransportAnalogyDischarge) : Set₁ where
  field
    PathIntegralToClosedTransportCompiler :
      Set

    pathIntegralCompiler :
      PathIntegralToClosedTransportCompiler

    StationaryPhaseErrorBound :
      Set

    stationaryPhaseBound :
      StationaryPhaseErrorBound

    MaterialScatteringLawReceipt :
      Set

    materialScatteringReceipt :
      MaterialScatteringLawReceipt

    VisibilityMaskCompletenessReceipt :
      Set

    visibilityMaskReceipt :
      VisibilityMaskCompletenessReceipt

    ResidualToleranceProof :
      Set

    residualTolerance :
      ResidualToleranceProof

    SideInformationBudgetProof :
      Set

    sideInformationBudget :
      SideInformationBudgetProof

    RendererRuntimeComplexityProof :
      Set

    runtimeComplexity :
      RendererRuntimeComplexityProof

    EmpiricalRendererConformanceReceipt :
      Set

    empiricalConformance :
      EmpiricalRendererConformanceReceipt

    requirementsDischarged :
      promotionRequirements discharge ≡ canonicalQuantumLightPromotionRequirements

    receiptReading :
      String

open QuantumLightTransportPromotionReceipt public

record PromotedQuantumPathLightTransport
    (discharge : QuantumPathLightTransportAnalogyDischarge) : Set₁ where
  field
    promotionReceipt :
      QuantumLightTransportPromotionReceipt discharge

    rendererAlgorithmClaimPromoted :
      Bool

    rendererAlgorithmClaimPromotedIsTrue :
      rendererAlgorithmClaimPromoted ≡ true

    qedBackedTransportClaimPromoted :
      Bool

    qedBackedTransportClaimPromotedIsTrue :
      qedBackedTransportClaimPromoted ≡ true

    globalOneShotClaimPromotedUnderReceipts :
      Bool

    globalOneShotClaimPromotedUnderReceiptsIsTrue :
      globalOneShotClaimPromotedUnderReceipts ≡ true

    promotedReading :
      String

open PromotedQuantumPathLightTransport public
