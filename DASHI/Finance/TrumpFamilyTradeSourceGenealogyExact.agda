module DASHI.Finance.TrumpFamilyTradeSourceGenealogyExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Finance.TrumpFamilyTradeSourceAtlasExact as Atlas

------------------------------------------------------------------------
-- PROPOSITION-LOCAL SOURCE GENEALOGY
--
-- Independent corroboration is proposition-indexed. A Reuters report derived
-- from one OGE filing and the filing itself are two visible artifacts but not
-- two independent upstream witnesses of the transaction proposition. The same
-- Reuters story may independently pay a different proposition (for example an
-- attributed management statement). Source count therefore cannot stand in for
-- genealogy-aware corroboration.
------------------------------------------------------------------------

data TradeEvidenceProposition : Set where
  transactionOccurred : TradeEvidenceProposition
  transactionAmountBand : TradeEvidenceProposition
  beneficialOwnership : TradeEvidenceProposition
  managementRepresentation : TradeEvidenceProposition
  hiddenInformation : TradeEvidenceProposition
  illegality : TradeEvidenceProposition
  marketCausation : TradeEvidenceProposition

data UpstreamClass : Set where
  ogePrimary : UpstreamClass
  secPrimary : UpstreamClass
  issuerPrimary : UpstreamClass
  governmentStatement : UpstreamClass
  independentReporter : UpstreamClass
  unresolvedUpstream : UpstreamClass

record PropositionSourceWitness : Set₁ where
  constructor proposition-source-witness
  field
    claim : Atlas.TradeEvidenceClaim
    proposition : TradeEvidenceProposition
    upstream : UpstreamClass
    genealogyReference : String
    propositionSupportReference : String

open PropositionSourceWitness public

record IndependentCorroboration
    (left right : PropositionSourceWitness) : Set where
  constructor independent-corroboration
  field
    sameProposition : proposition left ≡ proposition right
    upstreamIndependent : upstream left ≡ upstream right → ⊥
    independenceReference : String

open IndependentCorroboration public

------------------------------------------------------------------------
-- Exact finite collision: two visible source surfaces can share one upstream
-- provenance chain. Visible multiplicity therefore does not determine
-- independent corroboration.
------------------------------------------------------------------------

data VisibleSource : Set where
  primaryArtifact secondaryReport : VisibleSource

data UpstreamTag : Set where
  sameUnderlyingFiling : UpstreamTag

upstreamTag : VisibleSource → UpstreamTag
upstreamTag primaryArtifact = sameUnderlyingFiling
upstreamTag secondaryReport = sameUnderlyingFiling

visibleMultiplicity : VisibleSource → Nat
visibleMultiplicity primaryArtifact = 2
visibleMultiplicity secondaryReport = 2

sameVisibleMultiplicity :
  visibleMultiplicity primaryArtifact ≡ visibleMultiplicity secondaryReport
sameVisibleMultiplicity = refl

upstreamTagsCoincide :
  upstreamTag primaryArtifact ≡ upstreamTag secondaryReport
upstreamTagsCoincide = refl

IndependentVisiblePair : VisibleSource → VisibleSource → Set
IndependentVisiblePair left right = upstreamTag left ≡ upstreamTag right → ⊥

primaryPlusDerivativeReportNotIndependent :
  IndependentVisiblePair primaryArtifact secondaryReport → ⊥
primaryPlusDerivativeReportNotIndependent independent = independent refl

------------------------------------------------------------------------
-- Proposition-locality prevents a source that corroborates one statement from
-- becoming universal corroboration for another.
------------------------------------------------------------------------

data CorroboratesTransactionAutomaticallyCorroboratesManagement : Set where
data CorroboratesManagementAutomaticallyCorroboratesKnowledge : Set where
data MoreSourcesAutomaticallyIncreaseAuthority : Set where

transactionCorroborationDoesNotAutoPayManagement :
  CorroboratesTransactionAutomaticallyCorroboratesManagement → ⊥
transactionCorroborationDoesNotAutoPayManagement ()

managementCorroborationDoesNotAutoPayHiddenKnowledge :
  CorroboratesManagementAutomaticallyCorroboratesKnowledge → ⊥
managementCorroborationDoesNotAutoPayHiddenKnowledge ()

sourceCountDoesNotAutoCreateAuthority :
  MoreSourcesAutomaticallyIncreaseAuthority → ⊥
sourceCountDoesNotAutoCreateAuthority ()

record TradeSourceGenealogyBoundary : Set where
  constructor trade-source-genealogy-boundary
  field
    sourceMultiplicityDistinctFromIndependence : Bool
    genealogyIsPropositionIndexed : Bool
    secondarySynthesisMaySharePrimaryUpstream : Bool
    corroborationDoesNotTransportAcrossPropositions : Bool
    sourceCountDoesNotCreateAuthority : Bool

canonicalTradeSourceGenealogyBoundary : TradeSourceGenealogyBoundary
canonicalTradeSourceGenealogyBoundary =
  trade-source-genealogy-boundary true true true true true
