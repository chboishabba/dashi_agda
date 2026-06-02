module DASHI.Physics.Closure.ITIRPNFPressureUnificationSupportReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Interop.PNFResidualSpectralSeverityReceipt as PNF
import Ontology.Hecke.PNFResidualBridge as HeckePNF
import DASHI.Physics.Closure.IntersectionalPressureAnisotropyReceipt as Pressure
import DASHI.Physics.Closure.RGContractionExplicitReceipt as RGExplicit
import DASHI.Physics.Closure.RGOperatorNormFormalProof as RGFormal
import DASHI.Interop.LightCodecTransportCorrespondenceTheorem
import DASHI.Interop.StationaryPhaseMirrorGratingToyReceipt
import DASHI.Computation.LESGLESWorldTransportBridge
import DASHI.Biology.EvolutionaryTransportMDLBridge

------------------------------------------------------------------------
-- ITIR/PNF pressure support for the publishable unification stack.
--
-- Local audit source:
--   * ../ITIR-suite/SensibLaw/docs/pnf_itir_primer.md
--   * ../ITIR-suite/docs/planning/rg_toy_completion_findings_20260329.md
--   * ../ITIR-suite/docs/planning/spectral_post_selector_retrieval_contract_20260329.md
--   * local DASHI wave/light/simulation/nature/RG/pressure receipts imported
--     above or already aggregated in DASHI.Everything.
--
-- The result is an inclusion receipt, not a theorem promotion.  It records
-- how ITIR's domain-fenced PNF residual logic should be consumed by the
-- unification papers:
--
--   * PNF residual severity is a typed domain-specific pressure carrier.
--   * Spectral retrieval is post-selector and domain-preserving.
--   * RG evidence remains toy/conditional unless the real coarse-graining
--     and continuum transfer inhabitants are supplied.
--   * Wave/light/refraction/simulation/nature lanes are observation-transport
--     supports with explicit non-promotion boundaries.
--   * TITAN and Bryan/Blueprint material are exposition guards only.

data ITIRPNFPressureSupportStatus : Set where
  itirPNFPressureSupportRecordedNoPromotion :
    ITIRPNFPressureSupportStatus

data ITIRPNFInputSurface : Set where
  predicateCarrierWithDomainFence :
    ITIRPNFInputSurface

  structuralSignatureAndRoles :
    ITIRPNFInputSurface

  qualifiersWrapperAndProvenance :
    ITIRPNFInputSurface

  residualLatticeExactPartialNoMeetContradiction :
    ITIRPNFInputSurface

  evidenceOnlyNoAuthorityPromotion :
    ITIRPNFInputSurface

canonicalITIRPNFInputs :
  List ITIRPNFInputSurface
canonicalITIRPNFInputs =
  predicateCarrierWithDomainFence
  ∷ structuralSignatureAndRoles
  ∷ qualifiersWrapperAndProvenance
  ∷ residualLatticeExactPartialNoMeetContradiction
  ∷ evidenceOnlyNoAuthorityPromotion
  ∷ []

data DomainPressureSupportLane : Set where
  lanePNFResidualSeverity :
    DomainPressureSupportLane

  laneHeckePNFCandidatePool :
    DomainPressureSupportLane

  laneIntersectionalPressureAnisotropy :
    DomainPressureSupportLane

  laneRGCoarseGrainingConditional :
    DomainPressureSupportLane

  laneWaveObservableTransport :
    DomainPressureSupportLane

  laneSpectralPostSelectorContract :
    DomainPressureSupportLane

  laneLightRefractionRainbowToy :
    DomainPressureSupportLane

  laneSimulationNatureTransport :
    DomainPressureSupportLane

  laneTitanAnisotropyExpositionGuard :
    DomainPressureSupportLane

  laneBryanBlueprintBoundaryGuard :
    DomainPressureSupportLane

canonicalSupportLanes :
  List DomainPressureSupportLane
canonicalSupportLanes =
  lanePNFResidualSeverity
  ∷ laneHeckePNFCandidatePool
  ∷ laneIntersectionalPressureAnisotropy
  ∷ laneRGCoarseGrainingConditional
  ∷ laneWaveObservableTransport
  ∷ laneSpectralPostSelectorContract
  ∷ laneLightRefractionRainbowToy
  ∷ laneSimulationNatureTransport
  ∷ laneTitanAnisotropyExpositionGuard
  ∷ laneBryanBlueprintBoundaryGuard
  ∷ []

data InclusionRule : Set where
  pnfPressureIsTypedResidualSeverity :
    InclusionRule

  pnfComparabilityRequiresDomainFence :
    InclusionRule

  pnfEvidenceIsNotTheoremAuthority :
    InclusionRule

  spectralRetrievalRunsAfterSelector :
    InclusionRule

  spectralRetrievalMayAbstain :
    InclusionRule

  rgToyDoesNotSupplyContinuumRG :
    InclusionRule

  waveTransportReceiptsStayObservationTransport :
    InclusionRule

  refractionRainbowStayStationaryPhaseToy :
    InclusionRule

  simulationNatureStayBoundedMDLAnalogy :
    InclusionRule

  titanIsAnisotropyPressureAnalogyOnly :
    InclusionRule

  bryanBlueprintIsBoundaryWarningOnly :
    InclusionRule

canonicalInclusionRules :
  List InclusionRule
canonicalInclusionRules =
  pnfPressureIsTypedResidualSeverity
  ∷ pnfComparabilityRequiresDomainFence
  ∷ pnfEvidenceIsNotTheoremAuthority
  ∷ spectralRetrievalRunsAfterSelector
  ∷ spectralRetrievalMayAbstain
  ∷ rgToyDoesNotSupplyContinuumRG
  ∷ waveTransportReceiptsStayObservationTransport
  ∷ refractionRainbowStayStationaryPhaseToy
  ∷ simulationNatureStayBoundedMDLAnalogy
  ∷ titanIsAnisotropyPressureAnalogyOnly
  ∷ bryanBlueprintIsBoundaryWarningOnly
  ∷ []

data ForbiddenSupportPromotion : Set where
  doNotUsePNFAsRuntimeTruth :
    ForbiddenSupportPromotion

  doNotUseDomainPressureAsNSPressure :
    ForbiddenSupportPromotion

  doNotUseSpectralRetrievalAsSelectorAuthority :
    ForbiddenSupportPromotion

  doNotUseToyRGAsBalabanRG :
    ForbiddenSupportPromotion

  doNotUseWaveTransportAsGate3Proof :
    ForbiddenSupportPromotion

  doNotUseRefractionToyAsRendererProof :
    ForbiddenSupportPromotion

  doNotUseSimulationNatureMotifsAsPhysicalClosure :
    ForbiddenSupportPromotion

  doNotUseTitanOrBryanAsMathematicalEvidence :
    ForbiddenSupportPromotion

  doNotClaimClayFromSupportLanes :
    ForbiddenSupportPromotion

canonicalForbiddenSupportPromotions :
  List ForbiddenSupportPromotion
canonicalForbiddenSupportPromotions =
  doNotUsePNFAsRuntimeTruth
  ∷ doNotUseDomainPressureAsNSPressure
  ∷ doNotUseSpectralRetrievalAsSelectorAuthority
  ∷ doNotUseToyRGAsBalabanRG
  ∷ doNotUseWaveTransportAsGate3Proof
  ∷ doNotUseRefractionToyAsRendererProof
  ∷ doNotUseSimulationNatureMotifsAsPhysicalClosure
  ∷ doNotUseTitanOrBryanAsMathematicalEvidence
  ∷ doNotClaimClayFromSupportLanes
  ∷ []

data SupportLanePromotion : Set where

supportLanePromotionImpossibleHere :
  SupportLanePromotion →
  ⊥
supportLanePromotionImpossibleHere ()

supportStatement :
  String
supportStatement =
  "ITIR PNF supplies domain-fenced residual pressure evidence for the unification grammar: exact/partial/no-typed-meet/contradiction severity, structural signatures, roles, provenance, and evidence-only wrappers. It is a support lane, not NS/YM analytic closure."

rgStatement :
  String
rgStatement =
  "Existing RG receipts split normalized-average contraction from parent-sum and continuum RG; the former is inhabited, while Balaban/continuum transfer remains a separate proof obligation."

transportStatement :
  String
transportStatement =
  "Wave, light-codec, refraction/rainbow, LES/GLES simulation, and evolutionary/nature transport receipts are observation-transport supports with explicit non-promotion boundaries."

expositionStatement :
  String
expositionStatement =
  "TITAN-style anisotropy and Bryan/blueprint material may be used as exposition guards only: anisotropy-pressure failure and biology-optimization overclaim boundaries, not mathematical evidence."

record ITIRPNFPressureUnificationSupportReceipt : Setω where
  field
    status :
      ITIRPNFPressureSupportStatus

    statusIsRecordedNoPromotion :
      status ≡ itirPNFPressureSupportRecordedNoPromotion

    pnfSpectralReceipt :
      PNF.PNFResidualSpectralSeverityReceipt

    pnfNoRuntimePromotion :
      PNF.PNFResidualSpectralSeverityReceipt.runtimePNFPromotion
        pnfSpectralReceipt
      ≡ false

    pnfNoContinuumSpectralPromotion :
      PNF.PNFResidualSpectralSeverityReceipt.continuumSpectralPromotion
        pnfSpectralReceipt
      ≡ false

    pnfNoClayPromotion :
      PNF.PNFResidualSpectralSeverityReceipt.clayPromotion
        pnfSpectralReceipt
      ≡ false

    heckePNFSurface :
      HeckePNF.HeckePNFResidualBridgeSurface

    intersectionalPressureReceipt :
      Pressure.IntersectionalPressureAnisotropyReceipt

    intersectionalPressureRecorded :
      Pressure.IntersectionalPressureAnisotropyReceipt.disproportionatePressureRecorded
        intersectionalPressureReceipt
      ≡ true

    pressureRecoveryStillOpen :
      Pressure.IntersectionalPressureAnisotropyReceipt.pressureRecoveryProved
        intersectionalPressureReceipt
      ≡ false

    nsGate3StillOpen :
      Pressure.IntersectionalPressureAnisotropyReceipt.navierStokesGate3Proved
        intersectionalPressureReceipt
      ≡ false

    rgExplicitReceipt :
      RGExplicit.RGContractionExplicitReceipt

    rgParentSumContractionStillOpen :
      RGExplicit.RGContractionExplicitReceipt.rgMapContractionProvedHere
        rgExplicitReceipt
      ≡ false

    rgFormalReceipt :
      RGFormal.RGOperatorNormFormalProofReceipt

    normalizedRGContractionInhabited :
      RGFormal.RGOperatorNormFormalProofReceipt.rgContractionForNormalizedMap
        rgFormalReceipt
      ≡ true

    continuumRGStillOpen :
      RGFormal.RGOperatorNormFormalProofReceipt.continuumRGConvergenceProved
        rgFormalReceipt
      ≡ false

    pnfInputs :
      List ITIRPNFInputSurface

    pnfInputsAreCanonical :
      pnfInputs ≡ canonicalITIRPNFInputs

    supportLanes :
      List DomainPressureSupportLane

    supportLanesAreCanonical :
      supportLanes ≡ canonicalSupportLanes

    inclusionRules :
      List InclusionRule

    inclusionRulesAreCanonical :
      inclusionRules ≡ canonicalInclusionRules

    forbiddenPromotions :
      List ForbiddenSupportPromotion

    forbiddenPromotionsAreCanonical :
      forbiddenPromotions ≡ canonicalForbiddenSupportPromotions

    domainSpecificPressureIncluded :
      Bool

    domainSpecificPressureIncludedIsTrue :
      domainSpecificPressureIncluded ≡ true

    domainSpecificPressureIsNSPressure :
      Bool

    domainSpecificPressureIsNSPressureIsFalse :
      domainSpecificPressureIsNSPressure ≡ false

    pnfAuthorityPromotion :
      Bool

    pnfAuthorityPromotionIsFalse :
      pnfAuthorityPromotion ≡ false

    spectralSelectorAuthorityPromotion :
      Bool

    spectralSelectorAuthorityPromotionIsFalse :
      spectralSelectorAuthorityPromotion ≡ false

    waveTransportGate3Promotion :
      Bool

    waveTransportGate3PromotionIsFalse :
      waveTransportGate3Promotion ≡ false

    nsTheoremPromotion :
      Bool

    nsTheoremPromotionIsFalse :
      nsTheoremPromotion ≡ false

    ymTheoremPromotion :
      Bool

    ymTheoremPromotionIsFalse :
      ymTheoremPromotion ≡ false

    clayPromotion :
      Bool

    clayPromotionIsFalse :
      clayPromotion ≡ false

    statement :
      String

    statementIsCanonical :
      statement ≡ supportStatement

    rgBoundary :
      String

    rgBoundaryIsCanonical :
      rgBoundary ≡ rgStatement

    transportBoundary :
      String

    transportBoundaryIsCanonical :
      transportBoundary ≡ transportStatement

    expositionBoundary :
      String

    expositionBoundaryIsCanonical :
      expositionBoundary ≡ expositionStatement

    promotionFlags :
      List SupportLanePromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

open ITIRPNFPressureUnificationSupportReceipt public

canonicalITIRPNFPressureUnificationSupportReceipt :
  ITIRPNFPressureUnificationSupportReceipt
canonicalITIRPNFPressureUnificationSupportReceipt =
  record
    { status =
        itirPNFPressureSupportRecordedNoPromotion
    ; statusIsRecordedNoPromotion =
        refl
    ; pnfSpectralReceipt =
        PNF.canonicalPNFResidualSpectralSeverityReceipt
    ; pnfNoRuntimePromotion =
        refl
    ; pnfNoContinuumSpectralPromotion =
        refl
    ; pnfNoClayPromotion =
        refl
    ; heckePNFSurface =
        HeckePNF.heckePNFResidualBridgeSurface
    ; intersectionalPressureReceipt =
        Pressure.canonicalIntersectionalPressureAnisotropyReceipt
    ; intersectionalPressureRecorded =
        refl
    ; pressureRecoveryStillOpen =
        refl
    ; nsGate3StillOpen =
        refl
    ; rgExplicitReceipt =
        RGExplicit.canonicalRGContractionExplicitReceipt
    ; rgParentSumContractionStillOpen =
        refl
    ; rgFormalReceipt =
        RGFormal.canonicalRGOperatorNormFormalProofReceipt
    ; normalizedRGContractionInhabited =
        refl
    ; continuumRGStillOpen =
        refl
    ; pnfInputs =
        canonicalITIRPNFInputs
    ; pnfInputsAreCanonical =
        refl
    ; supportLanes =
        canonicalSupportLanes
    ; supportLanesAreCanonical =
        refl
    ; inclusionRules =
        canonicalInclusionRules
    ; inclusionRulesAreCanonical =
        refl
    ; forbiddenPromotions =
        canonicalForbiddenSupportPromotions
    ; forbiddenPromotionsAreCanonical =
        refl
    ; domainSpecificPressureIncluded =
        true
    ; domainSpecificPressureIncludedIsTrue =
        refl
    ; domainSpecificPressureIsNSPressure =
        false
    ; domainSpecificPressureIsNSPressureIsFalse =
        refl
    ; pnfAuthorityPromotion =
        false
    ; pnfAuthorityPromotionIsFalse =
        refl
    ; spectralSelectorAuthorityPromotion =
        false
    ; spectralSelectorAuthorityPromotionIsFalse =
        refl
    ; waveTransportGate3Promotion =
        false
    ; waveTransportGate3PromotionIsFalse =
        refl
    ; nsTheoremPromotion =
        false
    ; nsTheoremPromotionIsFalse =
        refl
    ; ymTheoremPromotion =
        false
    ; ymTheoremPromotionIsFalse =
        refl
    ; clayPromotion =
        false
    ; clayPromotionIsFalse =
        refl
    ; statement =
        supportStatement
    ; statementIsCanonical =
        refl
    ; rgBoundary =
        rgStatement
    ; rgBoundaryIsCanonical =
        refl
    ; transportBoundary =
        transportStatement
    ; transportBoundaryIsCanonical =
        refl
    ; expositionBoundary =
        expositionStatement
    ; expositionBoundaryIsCanonical =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    }

domainSpecificPressureIncludedButNotNSPressure :
  domainSpecificPressureIncluded
    canonicalITIRPNFPressureUnificationSupportReceipt ≡ true
domainSpecificPressureIncludedButNotNSPressure =
  refl

supportLaneDoesNotPromoteClay :
  clayPromotion canonicalITIRPNFPressureUnificationSupportReceipt ≡ false
supportLaneDoesNotPromoteClay =
  refl
