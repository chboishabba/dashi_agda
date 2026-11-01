module DASHI.Finance.TrumpSpaceXPropositionGenealogyExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Finance.TrumpFamilyTradeSourceAtlasExact as Atlas
import DASHI.Finance.TrumpFamilyTradeSourceGenealogyExact as Genealogy
import DASHI.Finance.TrumpSpaceXPrimaryAcquisitionExact as SpaceX

------------------------------------------------------------------------
-- SAME ARTICLE, DIFFERENT PROPOSITION GENEALOGY
--
-- Reuters 2026-08-24 contains at least two propositionally distinct source
-- routes:
--   * transaction proposition: attributed to a public financial disclosure;
--   * portfolio-management representation: attributed to White House spokesman
--     Davis Ingle.
-- The visible carrier is one Reuters article, but upstream provenance depends on
-- the proposition being consumed. Carrier identity therefore cannot replace
-- proposition-indexed genealogy.
------------------------------------------------------------------------

spaceXManagementRepresentation : Atlas.TradeEvidenceClaim
spaceXManagementRepresentation =
  Atlas.tradeEvidenceClaim
    "Reuters-SpaceX-WhiteHouse-management-representation-2026-08-24"
    "White House spokesman Davis Ingle"
    "Donald J. Trump's reported investment portfolio"
    Atlas.financialDisclosureClaim
    "statement reported 2026-08-24"
    "2026-08-24"
    "Reuters reports White House spokesman Davis Ingle stating that third-party financial institutions independently manage President Trump's portfolio and replicate recognized indexes, and that neither President Trump nor family members can direct, influence or provide input regarding investment selection or timing."
    Atlas.independentSynthesisSupport
    (Atlas.sourceCitation
      "Reuters"
      "Trump bought shares in Elon Musk's SpaceX in June, financial disclosure shows"
      "2026-08-24"
      "no DOI"
      "https://www.reuters.com/legal/government/trump-bought-shares-elon-musks-spacex-june-financial-disclosure-shows-2026-08-24/"
      Atlas.independentReporting)
    (Atlas.sourceArtifact SpaceX.reutersSpaceXClaim)
    "Pays only Reuters' attribution of the White House representation; it does not identify the managing institutions, audit index-replication rules, or independently prove zero input."
    false true false false

transactionWitness : Genealogy.PropositionSourceWitness
transactionWitness =
  Genealogy.proposition-source-witness
    SpaceX.reutersSpaceXClaim
    Genealogy.transactionOccurred
    Genealogy.ogePrimary
    "Reuters transaction statement derives from the public financial disclosure described in the article; exact OGE row remains acquisition debt"
    "June 23 SpaceX purchase / disclosed reporting range"

managementWitness : Genealogy.PropositionSourceWitness
managementWitness =
  Genealogy.proposition-source-witness
    spaceXManagementRepresentation
    Genealogy.managementRepresentation
    Genealogy.governmentStatement
    "Reuters attributes this proposition to White House spokesman Davis Ingle"
    "third-party management / no-direction representation"

sameVisibleCarrier :
  Atlas.sourceArtifact (Genealogy.claim transactionWitness)
  ≡ Atlas.sourceArtifact (Genealogy.claim managementWitness)
sameVisibleCarrier = refl

upstreamRoutesDiffer :
  Genealogy.upstream transactionWitness ≡ Genealogy.upstream managementWitness → ⊥
upstreamRoutesDiffer ()

------------------------------------------------------------------------
-- The same article therefore cannot be assigned one universal independence or
-- authority status. Genealogy and support strength are properties of the
-- proposition-source edge.
------------------------------------------------------------------------

data SameCarrierMeansSameUpstreamForEveryProposition : Set where
data ManagementRepresentationAutomaticallyProvesMandate : Set where
data ManagementRepresentationAutomaticallyProvesNoInput : Set where

sameCarrierDoesNotMeanSameUpstream :
  SameCarrierMeansSameUpstreamForEveryProposition → ⊥
sameCarrierDoesNotMeanSameUpstream ()

representationDoesNotAuditMandate :
  ManagementRepresentationAutomaticallyProvesMandate → ⊥
representationDoesNotAuditMandate ()

representationDoesNotIndependentlyProveNoInput :
  ManagementRepresentationAutomaticallyProvesNoInput → ⊥
representationDoesNotIndependentlyProveNoInput ()

record SpaceXPropositionGenealogyBoundary : Set where
  constructor spacex-proposition-genealogy-boundary
  field
    sameCarrierCanContainDifferentSourceRoutes : Bool
    transactionAndManagementAreDifferentPropositions : Bool
    transactionRouteRetainsPrimaryRowDebt : Bool
    managementRouteIsAttributedGovernmentStatement : Bool
    attributedManagementDoesNotAuditMandate : Bool
    propositionLocalGenealogyRequired : Bool

canonicalSpaceXPropositionGenealogyBoundary : SpaceXPropositionGenealogyBoundary
canonicalSpaceXPropositionGenealogyBoundary =
  spacex-proposition-genealogy-boundary true true true true true true
