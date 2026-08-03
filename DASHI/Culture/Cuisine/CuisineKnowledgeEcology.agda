module DASHI.Culture.Cuisine.CuisineKnowledgeEcology where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Core.GenericReceipt as GenericReceipt
import DASHI.Culture.Cuisine.ControlledSuccessCore as Success
import DASHI.Culture.Cuisine.CuisineKnowledgeSourceAtlas as Sources
import DASHI.Culture.Cuisine.MoleProcessArchitecture as Process
import DASHI.Culture.Cuisine.SituatedMoleWorld as Situated
import DASHI.Culture.Preservation.ControlledDisclosureCore as Disclosure

------------------------------------------------------------------------
-- Compact assembly: complete attributed archive -> governed public view.
--
-- The example strings are public candidate descriptions.  The purpose is to
-- close the type-level relationship among sources, archive, projection,
-- process, situated world and publicity boundary without manufacturing a
-- large archive implementation or pretending sensitive content is present.
------------------------------------------------------------------------

candidateCuisineArchive : Disclosure.FullArchive String
candidateCuisineArchive =
  Disclosure.fullArchive
    "candidate situated cuisine archive"
    ( "complete process graph, source relationships, residuals, and contradictions"
    ∷ "land, labour, knowledge, commensality, representation, and publicity surfaces"
    ∷ "restricted details would remain typed but are not included in this public repository"
    ∷ [] )
    Sources.canonicalCuisineKnowledgeSourceAtlas
    "Agda 2.9 module graph and repository commit pin"
    "agda -i . DASHI/Culture/Cuisine/Everything.agda"
    Disclosure.publicSummaryPrivateSourcesEnvelope
    "Preserve reconstructible meaning and attribution; public release is a separately governed projection."

publicProcessProjection : Disclosure.PublicClaimProjection String
publicProcessProjection =
  Disclosure.publicClaimProjection
    "complete process graph, source relationships, residuals, and contradictions"
    "high-level order-sensitive mole process architecture with unresolved empirical obligations"
    Disclosure.controlledSummaryAction
    "Exact vulnerable, restricted, or community-controlled process detail is outside this public candidate archive."

publicSocialProjection : Disclosure.PublicClaimProjection String
publicSocialProjection =
  Disclosure.publicClaimProjection
    "land, labour, knowledge, commensality, representation, and publicity surfaces"
    "situated food-system, labour, commensality, representation, and controlled-success boundary"
    Disclosure.controlledSummaryAction
    "The public view states the dimensions without claiming to exhaust or speak for any community."

castilloSourceProjection : Disclosure.SourceDisclosureProjection
castilloSourceProjection =
  Disclosure.sourceDisclosureProjection
    Sources.castilloCisnerosEnMiMeroMole
    (Source.mkPublicAttributionProjection
      Sources.castilloCisnerosEnMiMeroMole
      "Maria del Carmen Castillo Cisneros, En mi mero mole, DOI 10.31644/ED.V8.N1.2021.A07")
    Disclosure.publicDisclosure

hryciukSourceProjection : Disclosure.SourceDisclosureProjection
hryciukSourceProjection =
  Disclosure.sourceDisclosureProjection
    Sources.hryciukAlquimistaSabores
    (Source.mkPublicAttributionProjection
      Sources.hryciukAlquimistaSabores
      "Renata E. Hryciuk, Alquimista de los Sabores, DOI 10.36551/2081-1160.2019.24.75-100")
    Disclosure.publicDisclosure

wovenPalateSourceProjection : Disclosure.SourceDisclosureProjection
wovenPalateSourceProjection =
  Disclosure.sourceDisclosureProjection
    Sources.wovenPalateArchitectureOfAsh
    (Source.mkPublicAttributionProjection
      Sources.wovenPalateArchitectureOfAsh
      "Eric Phanngavong, The Architecture of Ash, The Woven Palate, 2026")
    Disclosure.publicDisclosure

buildCandidatePublicProjection :
  Disclosure.FullArchive String →
  Disclosure.PublicArtifact String
buildCandidatePublicProjection archive =
  Disclosure.publicArtifact
    "attributed public situated-cuisine projection"
    (publicProcessProjection ∷ publicSocialProjection ∷ [])
    ( castilloSourceProjection
    ∷ hryciukSourceProjection
    ∷ wovenPalateSourceProjection
    ∷ [] )
    "The public artifact is intentionally incomplete; full source coverage remains in the atlas and any genuinely restricted content requires an external governed archive."
    Disclosure.attributedSummaryDisclosure

candidateCuisineProjectionPolicy : Disclosure.ProjectionPolicy String
candidateCuisineProjectionPolicy =
  Disclosure.projectionPolicy
    "attribution-first cuisine public projection"
    ( Disclosure.disclosureRule
        Disclosure.attributionSurface
        Disclosure.retainAction
        "source atlas attribution policy"
        "Public academic and practitioner sources retain author, title, DOI where recorded, and canonical URL."
    ∷ Disclosure.disclosureRule
        Disclosure.locationSurface
        Disclosure.coarsenLocationAction
        "community or ecological governance required"
        "Precise vulnerable locations are not a default public output."
    ∷ Disclosure.disclosureRule
        Disclosure.ritualSurface
        Disclosure.existenceClaimAction
        "community disclosure authority required"
        "A restricted interpretation may be acknowledged without exposing its content."
    ∷ Disclosure.disclosureRule
        Disclosure.processParameterSurface
        Disclosure.controlledSummaryAction
        "practice-specific disclosure authority required"
        "High-level process structure may be public while restricted parameters remain withheld."
    ∷ [] )
    buildCandidatePublicProjection
    "candidate attribution-first policy; no community authority is inferred"
    "This repository demonstrates a reproducible typed projection, not a complete secure publication pipeline."

candidateCuisinePublicArtifact : Disclosure.PublicArtifact String
candidateCuisinePublicArtifact =
  Disclosure.buildProjection
    candidateCuisineProjectionPolicy
    candidateCuisineArchive

candidateCuisinePublicationReceipt :
  Disclosure.PublicationReceipt
    candidateCuisineArchive
    candidateCuisineProjectionPolicy
    candidateCuisinePublicArtifact
candidateCuisinePublicationReceipt =
  Disclosure.publicationReceipt
    refl
    true
    refl
    true
    refl
    true
    refl
    "The artifact is generated by the declared policy; attribution classification and omission are demonstrated at the typed example level only."

record CuisineKnowledgeEcology : Set₁ where
  constructor cuisineKnowledgeEcology
  field
    sourceAtlas : Source.AttributedSourceAtlas
    processBoundary : Process.MoleProcessArchitectureBoundary
    situatedBoundary : Situated.SituatedMoleWorldBoundary
    controlledSuccessBoundary : Success.ControlledSuccessBoundary
    archive : Disclosure.FullArchive String
    projectionPolicy : Disclosure.ProjectionPolicy String
    publicArtifact : Disclosure.PublicArtifact String
    publicationReceipt :
      Disclosure.PublicationReceipt archive projectionPolicy publicArtifact
    archiveIsNotPublicViewClaim : Bool
    archiveIsNotPublicViewClaimIsTrue :
      archiveIsNotPublicViewClaim ≡ true
    ecologyReading : String

open CuisineKnowledgeEcology public

canonicalCuisineKnowledgeEcology : CuisineKnowledgeEcology
canonicalCuisineKnowledgeEcology =
  cuisineKnowledgeEcology
    Sources.canonicalCuisineKnowledgeSourceAtlas
    Process.canonicalMoleProcessArchitectureBoundary
    Situated.canonicalSituatedMoleWorldBoundary
    Success.canonicalControlledSuccessBoundary
    candidateCuisineArchive
    candidateCuisineProjectionPolicy
    candidateCuisinePublicArtifact
    candidateCuisinePublicationReceipt
    true
    refl
    "A situated cuisine archive may retain strong formal structure and attribution while producing a smaller public projection under a fail-closed publicity boundary."

canonicalCuisineKnowledgeEcologyReceipt : GenericReceipt.GenericReceipt
canonicalCuisineKnowledgeEcologyReceipt =
  GenericReceipt.mkNonPromotingReceipt
    "situated cuisine knowledge ecology"
    "DASHI.Culture.Cuisine.CuisineKnowledgeEcology"
    "canonicalCuisineKnowledgeEcology"
    "assembles attributed sources, mole process, situated social world, controlled success, full archive, typed public projection, and publication receipt"
    "the example does not claim a complete archive, community authority, sensitive content custody, cryptographic non-leakage, empirical closure, or permission to publish any restricted knowledge"
    "agda -i . DASHI/Culture/Cuisine/CuisineKnowledgeEcology.agda"
