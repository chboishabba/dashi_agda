module DASHI.Biology.TrumpBannonConsentAttractorBridge where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Biology.TrumpPsychogeographicPolicyAtlasExact as Trump
import DASHI.Biology.TrumpPsychogeographyAuthorityBoundary as TrumpBoundary
import DASHI.Governance.EpistemicAttractorCore as Epistemic
import DASHI.Governance.ExternalityCarrierAttractor as Externality
import DASHI.Governance.InstitutionalTechniqueTransferCore as Transfer

------------------------------------------------------------------------
-- Trump/Bannon cross-pollination surface.
--
-- Existing Trump policy cases are connected to the new epistemic-attractor,
-- externality-carrier and institutional-technique-transfer grammars.  The
-- bridge intentionally does NOT infer that Donald Trump, Steve Bannon, any
-- campaign, movement or constituency instantiates those grammars merely by
-- being named here.  Named-actor application remains evidence-gated.
------------------------------------------------------------------------

data NamedPoliticalActor : Set where
  donaldTrumpCase : NamedPoliticalActor
  steveBannonCase : NamedPoliticalActor

record NamedActorEvidenceGate : Set where
  constructor namedActorEvidenceGate
  field
    actor : NamedPoliticalActor
    sourceSpecific : Bool
    quotationOrPrimaryRecordPreferred : Bool
    dateAndContextBound : Bool
    rhetoricalSimilarityCreatesCommonCommandClaim : Bool
    formalPatternCreatesMotiveClaim : Bool
    formalPatternCreatesExtremismClaim : Bool

canonicalTrumpEvidenceGate : NamedActorEvidenceGate
canonicalTrumpEvidenceGate =
  namedActorEvidenceGate donaldTrumpCase true true true false false false

canonicalBannonEvidenceGate : NamedActorEvidenceGate
canonicalBannonEvidenceGate =
  namedActorEvidenceGate steveBannonCase true true true false false false

------------------------------------------------------------------------
-- Existing Palantir procurement lane remains bounded.
------------------------------------------------------------------------

existingPalantirSourceDoesNotCreateLegalConclusion :
  Trump.sourceCreatesLegalConclusion Trump.palantirAwardSource ≡ false
existingPalantirSourceDoesNotCreateLegalConclusion = refl

existingPalantirProcurementDoesNotProveAbuseOrNeutrality :
  TrumpBoundary.palantirProcurementProvesAbuseOrNeutrality
    TrumpBoundary.canonicalTrumpPsychogeographicCrossPollination
  ≡ false
existingPalantirProcurementDoesNotProveAbuseOrNeutrality = refl

record TrumpBannonCrossPollinationBoundary : Set where
  constructor trumpBannonCrossPollinationBoundary
  field
    trumpPolicyAtlasImported : Bool
    palantirCaseImported : Bool
    epistemicAttractorImported : Bool
    externalityCarrierImported : Bool
    techniqueTransferImported : Bool
    namedActorInstantiationAutomatic : Bool
    sharedRhetoricProvesCoordination : Bool
    politicalOppositionProvesAntifascistOrFascistIdentity : Bool

canonicalTrumpBannonCrossPollinationBoundary :
  TrumpBannonCrossPollinationBoundary
canonicalTrumpBannonCrossPollinationBoundary =
  trumpBannonCrossPollinationBoundary
    true true true true true false false false

record TrumpBannonConsentAttractorReceipt : Set where
  constructor trumpBannonConsentAttractorReceipt
  field
    label : String
    trumpGate : NamedActorEvidenceGate
    bannonGate : NamedActorEvidenceGate
    epistemicReceipt : Epistemic.EpistemicAttractorReceipt
    externalityReceipt : Externality.ExternalityCarrierReceipt
    transferReceipt : Transfer.InstitutionalTechniqueTransferReceipt
    boundary : TrumpBannonCrossPollinationBoundary

canonicalTrumpBannonConsentAttractorReceipt :
  TrumpBannonConsentAttractorReceipt
canonicalTrumpBannonConsentAttractorReceipt =
  trumpBannonConsentAttractorReceipt
    "Trump/Bannon evidence-gated consent-attractor bridge"
    canonicalTrumpEvidenceGate
    canonicalBannonEvidenceGate
    Epistemic.canonicalEpistemicAttractorReceipt
    Externality.canonicalExternalityCarrierReceipt
    Transfer.canonicalInstitutionalTechniqueTransferReceipt
    canonicalTrumpBannonCrossPollinationBoundary
