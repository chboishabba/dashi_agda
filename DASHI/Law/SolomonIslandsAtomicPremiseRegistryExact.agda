module DASHI.Law.SolomonIslandsAtomicPremiseRegistryExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Algebra.BalancedTernary as BT
import DASHI.Core.AttributedSourceCore as Source
import DASHI.Interop.SensibLawOntologyTopology as Ontology
import DASHI.Cognition.PNF.SensibLawTypedLegalAuthorityEdgeExact as Edge
import DASHI.Cognition.PNF.SensibLawSourceFormAuthorityRoleBidiExact as SourceRole
import DASHI.Cognition.PNF.SensibLawSourceRealisedLegalRuleExact as SourceRule
import DASHI.Cognition.PNF.SensibLawUniversalLegalRuleAlgebraExact as Algebra
import DASHI.Cognition.PNF.SensibLawAtomicLegalTestBalancedTernaryExact as Atomic
import DASHI.Cognition.PNF.SensibLawAtomicCaseOutcomeCoherenceExact as Registry
import DASHI.Law.SolomonIslandsWrongTypeLegalElementDerivationExact as Deriv

------------------------------------------------------------------------
-- SOLOMON ISLANDS ATOMIC PREMISE REGISTRY
--
-- The statutes define the exact legal tests.  The current public evidence fibre
-- neither proves fit nor proves failure of the paying factual propositions, so
-- the canonical atomic outcome is zero (unresolved), not positive or negative.
-- Registry indexing is by the exact LegalProposition; a duplicate test cannot
-- silently reintroduce a contradictory case outcome.
------------------------------------------------------------------------

antiCorruptionAttributedSource : Source.AttributedSource
antiCorruptionAttributedSource = Source.mkNoDOISource
  "Attorney-General's Chambers, Solomon Islands"
  "Anti-Corruption Act 2018"
  "Solomon Islands legislation / authorised government publication"
  "2018"
  "https://attorneygenerals.gov.sb/Download/anti-corruption-act-2018-no-2-of-2018v1/"
  Source.governmentSource
  "primary statutory definition source for the s 92 atomic benefit/influence premise; citation does not establish the case fact"
  Source.publicAttribution

leadershipAttributedSource : Source.AttributedSource
leadershipAttributedSource = Source.mkNoDOISource
  "Attorney-General's Chambers, Solomon Islands"
  "Leadership Code (Further Provisions) Act 1999"
  "authorised reprint current 5 February 2024"
  "1999"
  "https://attorneygenerals.gov.sb/Download/leadership-code-further-provisions-act-1999-v4_as-at-050224/"
  Source.governmentSource
  "primary statutory definition source for the s 17 atomic inducement premise; citation does not establish the case fact"
  Source.publicAttribution

antiCorruptionAuthorityIdentity : Edge.SourceIdentity
antiCorruptionAuthorityIdentity = Edge.source-identity
  "Attorney-General's Chambers, Solomon Islands"
  "Anti-Corruption Act 2018"
  "Anti-Corruption Act 2018, s 92(1)-(2)"
  Edge.legislation

leadershipAuthorityIdentity : Edge.SourceIdentity
leadershipAuthorityIdentity = Edge.source-identity
  "Attorney-General's Chambers, Solomon Islands"
  "Leadership Code (Further Provisions) Act 1999"
  "Leadership Code (Further Provisions) Act 1999, s 17(1)-(3)"
  Edge.legislation

antiCorruptionLegislativeRole : SourceRole.SourceFormRoleReceipt
antiCorruptionLegislativeRole = SourceRole.source-form-role-receipt
  antiCorruptionAuthorityIdentity Ontology.statute Algebra.legislativeRuleRole
  "SB Anti-Corruption Act 2018 s 92 atomic premise"
  true true

leadershipLegislativeRole : SourceRole.SourceFormRoleReceipt
leadershipLegislativeRole = SourceRole.source-form-role-receipt
  leadershipAuthorityIdentity Ontology.statute Algebra.legislativeRuleRole
  "SB Leadership Code 1999 s 17 atomic premise"
  true true

s92PremiseSource : SourceRule.PropositionSourceReceipt Deriv.s92BenefitInfluenceFact
s92PremiseSource = SourceRule.proposition-source-receipt
  antiCorruptionAttributedSource
  Deriv.antiCorruptionSourceRef
  "Anti-Corruption Act 2018, s 92(1)-(2)"
  SourceRule.primarySourceLayer
  antiCorruptionLegislativeRole
  refl refl refl
  (Source.citationCreatesAuthorityIsFalse antiCorruptionAttributedSource)
  "statute defines the exact benefit/intent/official-duty test; current-event satisfaction remains evidentiary"

s17PremiseSource : SourceRule.PropositionSourceReceipt Deriv.s17InducementFact
s17PremiseSource = SourceRule.proposition-source-receipt
  leadershipAttributedSource
  Deriv.leadershipSourceRef
  "Leadership Code (Further Provisions) Act 1999, s 17(1)-(3)"
  SourceRule.primarySourceLayer
  leadershipLegislativeRole
  refl refl refl
  (Source.citationCreatesAuthorityIsFalse leadershipAttributedSource)
  "statute defines the exact consideration/inducement/reward test; current-event satisfaction remains evidentiary"

------------------------------------------------------------------------
-- Zero-gate tests: no witness is manufactured in either direction.
------------------------------------------------------------------------

data NoCurrentS92FitWitness : Set where
data NoCurrentS92FailureWitness : Set where

data NoCurrentS17FitWitness : Set where
data NoCurrentS17FailureWitness : Set where

currentS92AtomicTest : Atomic.SourceConditionedAtomicLegalTest Deriv.s92BenefitInfluenceFact
currentS92AtomicTest = Atomic.source-conditioned-atomic-legal-test
  s92PremiseSource
  (Algebra.subjectReference Deriv.s92BenefitInfluenceFact)
  refl
  NoCurrentS92FitWitness
  NoCurrentS92FailureWitness
  (λ ())
  BT.zero
  (λ ())
  (λ ())
  "Solomon s92 current public-evidence fibre: unresolved; no positive or negative element witness"

currentS17AtomicTest : Atomic.SourceConditionedAtomicLegalTest Deriv.s17InducementFact
currentS17AtomicTest = Atomic.source-conditioned-atomic-legal-test
  s17PremiseSource
  (Algebra.subjectReference Deriv.s17InducementFact)
  refl
  NoCurrentS17FitWitness
  NoCurrentS17FailureWitness
  (λ ())
  BT.zero
  (λ ())
  (λ ())
  "Solomon s17 current public-evidence fibre: unresolved; no positive or negative element witness"

------------------------------------------------------------------------
-- Exact proposition-indexed registry.
------------------------------------------------------------------------

solomonEpisodeContext : Ontology.StableId
solomonEpisodeContext = Ontology.stableId "case:SB:2026-treaty-funding-no-confidence"

data SolomonAtomicEntry : Algebra.LegalProposition → Set where
  s92Entry : SolomonAtomicEntry Deriv.s92BenefitInfluenceFact
  s17Entry : SolomonAtomicEntry Deriv.s17InducementFact

entryContext : ∀ {p} → SolomonAtomicEntry p → Ontology.StableId
entryContext s92Entry = solomonEpisodeContext
entryContext s17Entry = solomonEpisodeContext

canonicalEntryTest :
  ∀ {p} → SolomonAtomicEntry p → Atomic.SourceConditionedAtomicLegalTest p
canonicalEntryTest s92Entry = currentS92AtomicTest
canonicalEntryTest s17Entry = currentS17AtomicTest

solomonAtomicRegistry : Registry.AtomicCaseRegistry
solomonAtomicRegistry = Registry.atomic-case-registry
  SolomonAtomicEntry
  entryContext
  canonicalEntryTest
  "Solomon 2026 exact paying-premise registry: s92 and s17 only"

registeredS92 : Registry.RegisteredAtomicTest solomonAtomicRegistry s92Entry
registeredS92 = Registry.canonicalRegisteredAtomicTest solomonAtomicRegistry s92Entry

registeredS17 : Registry.RegisteredAtomicTest solomonAtomicRegistry s17Entry
registeredS17 = Registry.canonicalRegisteredAtomicTest solomonAtomicRegistry s17Entry

s92CanonicalGateIsZero : Atomic.gate currentS92AtomicTest ≡ BT.zero
s92CanonicalGateIsZero = refl

s17CanonicalGateIsZero : Atomic.gate currentS17AtomicTest ≡ BT.zero
s17CanonicalGateIsZero = refl

------------------------------------------------------------------------
-- Reporter-held / non-public primary-artifact boundary.
--
-- This is case-specific status, not a second acquisition scheduler.  The
-- existing acquisition machinery remains canonical.  It records why the zero
-- gate cannot presently be refined from the public evidence surface.
------------------------------------------------------------------------

record PublicArtifactAvailability : Set where
  constructor public-artifact-availability
  field
    journalistOrOppositionReportsPrimaryArtifact : Bool
    journalistOrOppositionReportsPrimaryArtifactIsTrue :
      journalistOrOppositionReportsPrimaryArtifact ≡ true
    publicFullThreadOrScreenshotLocated : Bool
    publicFullThreadOrScreenshotLocatedIsFalse :
      publicFullThreadOrScreenshotLocated ≡ false
    publicReviewerCanInspectSenderRecipientTimestampTopology : Bool
    publicReviewerCanInspectSenderRecipientTimestampTopologyIsFalse :
      publicReviewerCanInspectSenderRecipientTimestampTopology ≡ false
    userSideAcquisitionDebt : Bool
    userSideAcquisitionDebtIsFalse : userSideAcquisitionDebt ≡ false
    residualReference : String

open PublicArtifactAvailability public

currentPublicArtifactAvailability : PublicArtifactAvailability
currentPublicArtifactAvailability = public-artifact-availability
  true refl
  false refl
  false refl
  false refl
  "externally unavailable / reporter-held primary WhatsApp evidence: refinement requires publication or independent authentication, not repetition of secondary reports"

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data ReportedFundingAutomaticallyMakesS92Positive : Set where
data PoliticalAdvantageAutomaticallyMakesS17Positive : Set where
data MissingPublicScreenshotMakesAtomicGateNegative : Set where
data UserMustSupplyReporterHeldArtifact : Set where

data DuplicateTestMayOverrideZeroRegistry : Set where

reportedFundingDoesNotMakeS92Positive : ReportedFundingAutomaticallyMakesS92Positive → ⊥
reportedFundingDoesNotMakeS92Positive ()

politicalAdvantageDoesNotMakeS17Positive : PoliticalAdvantageAutomaticallyMakesS17Positive → ⊥
politicalAdvantageDoesNotMakeS17Positive ()

missingScreenshotDoesNotCreateNegativeWitness : MissingPublicScreenshotMakesAtomicGateNegative → ⊥
missingScreenshotDoesNotCreateNegativeWitness ()

reporterHeldArtifactIsNotUserDebt : UserMustSupplyReporterHeldArtifact → ⊥
reporterHeldArtifactIsNotUserDebt ()

duplicateCannotOverrideRegisteredZero : DuplicateTestMayOverrideZeroRegistry → ⊥
duplicateCannotOverrideRegisteredZero ()
