module DASHI.Cognition.PNF.SensibLawTypedLegalAuthorityEdgeExact where

------------------------------------------------------------------------
-- TYPED LEGAL AUTHORITY / DOCTRINAL EDGE KERNEL
--
-- Source attribution policy:
--   * external legal propositions retain recoverable authority identity;
--   * a statute, precedent, judicial policy consideration and empirical fact
--     never collapse merely because each can participate in a legal argument;
--   * DASHI graph structure below is a formal reconstruction, not a theorem
--     attributed to any cited court or author.
--
-- Calibration authorities:
--   * Donoghue v Stevenson [1932] AC 562 (UKHL) -- neighbour principle / the
--     modern negligence lineage; stable law-report citation.
--   * Mabo v Queensland (No 2) [1992] HCA 23; 175 CLR 1.
--   * Pabai v Commonwealth of Australia (No 2) [2025] FCA 796.
--   * Native Title Act 1993 (Cth), especially ss 3 and 223.
--
-- Detailed Mabo/Pabai and critical-theory source attribution is owned by:
--   SensibLawNativeTitleRecognitionCriticalSourceAtlasExact
--   SensibLawPabaiRecognitionRemedyGapExact
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Recoverable source identity.
------------------------------------------------------------------------

data AuthorityKind : Set where
  constitutionalText
  legislation
  delegatedLegislation
  bindingPrecedent
  persuasivePrecedent
  commonLawDevelopment
  judicialPolicyConsideration
  adjudicatedFact
  partySubmission
  empiricalSource
  criticalTheorySource
  dashSyntheticInference
  : AuthorityKind

record SourceIdentity : Set where
  constructor source-identity
  field
    authorOrInstitution : String
    title : String
    stableIdentifier : String
    kind : AuthorityKind

open SourceIdentity public

record TypedLegalEdge : Set where
  constructor typed-legal-edge
  field
    edgeId : String
    premise : String
    conclusion : String
    source : SourceIdentity
    directSourceSupport : Bool
    dashReconstruction : Bool
    crossSourceSynthesis : Bool

open TypedLegalEdge public

------------------------------------------------------------------------
-- A blocker is not merely a consideration that weighs against a result.
------------------------------------------------------------------------

data GateForce : Set where
  hardBlocker
  factorFor
  factorAgainst
  interpretiveConstraint
  evidentialRequirement
  : GateForce

record DoctrinalGate : Set where
  constructor doctrinal-gate
  field
    gateId : String
    predicate : String
    force : GateForce
    authority : SourceIdentity
    rationale : String

open DoctrinalGate public

data FactorAgainstIsHardBlocker : Set where
data JudicialPolicyIsLegislation : Set where
data AdjudicatedFactIsLegalHolding : Set where
data PartySubmissionIsAdjudicatedFact : Set where
data CommonLawDevelopmentIsStatutoryText : Set where

factorAgainstDoesNotBecomeHardBlocker : FactorAgainstIsHardBlocker → ⊥
factorAgainstDoesNotBecomeHardBlocker ()

judicialPolicyDoesNotBecomeLegislation : JudicialPolicyIsLegislation → ⊥
judicialPolicyDoesNotBecomeLegislation ()

adjudicatedFactDoesNotBecomeHolding : AdjudicatedFactIsLegalHolding → ⊥
adjudicatedFactDoesNotBecomeHolding ()

partySubmissionDoesNotBecomeFact : PartySubmissionIsAdjudicatedFact → ⊥
partySubmissionDoesNotBecomeFact ()

commonLawDevelopmentDoesNotBecomeStatutoryText : CommonLawDevelopmentIsStatutoryText → ⊥
commonLawDevelopmentDoesNotBecomeStatutoryText ()

------------------------------------------------------------------------
-- Stable calibration identities.
------------------------------------------------------------------------

donoghueAuthority : SourceIdentity
donoghueAuthority = source-identity
  "House of Lords"
  "Donoghue v Stevenson"
  "[1932] AC 562"
  bindingPrecedent

maboAuthority : SourceIdentity
maboAuthority = source-identity
  "High Court of Australia"
  "Mabo v Queensland (No 2)"
  "[1992] HCA 23; 175 CLR 1"
  bindingPrecedent

pabaiAuthority : SourceIdentity
pabaiAuthority = source-identity
  "Federal Court of Australia; Wigney J"
  "Pabai v Commonwealth of Australia (No 2)"
  "[2025] FCA 796"
  bindingPrecedent

nativeTitleActAuthority : SourceIdentity
nativeTitleActAuthority = source-identity
  "Parliament of Australia"
  "Native Title Act 1993 (Cth)"
  "C2004A04665; https://www.legislation.gov.au/C2004A04665/latest/text"
  legislation

------------------------------------------------------------------------
-- Minimal-obstruction queries must preserve edge type and provenance.
------------------------------------------------------------------------

data LegalRouteState : Set where
  routeOpen
  routeBlocked
  routeContested
  : LegalRouteState

record RouteObstruction : Set where
  constructor route-obstruction
  field
    target : String
    blocker : DoctrinalGate
    currentState : LegalRouteState
    removalWouldBeLegalChange : Bool
    sourceMustBeReopenedBeforePromotion : Bool

open RouteObstruction public

record MinimalLegalTransformation : Set where
  constructor minimal-legal-transformation
  field
    targetResult : String
    changedPredicate : String
    changeKind : AuthorityKind
    sourceOrProposedAuthority : SourceIdentity
    claimThatResultAlreadyFollows : Bool
    requiresIndependentProof : Bool

open MinimalLegalTransformation public

------------------------------------------------------------------------
-- Structural firewalls for corpus-scale search.
------------------------------------------------------------------------

data EveryEdgeHasSameNormativeForce : Set where
data SourceIdentityMayBeDiscardedAfterParsing : Set where
data LargePlaintiffClassMeansIndeterminateAsMatterOfLogic : Set where
data ForeseeabilityAloneCreatesDutyAsMatterOfLogic : Set where

everyEdgeDoesNotHaveSameForce : EveryEdgeHasSameNormativeForce → ⊥
everyEdgeDoesNotHaveSameForce ()

parsedEdgeRetainsAuthority : SourceIdentityMayBeDiscardedAfterParsing → ⊥
parsedEdgeRetainsAuthority ()

largeClassDoesNotLogicallyEntailIndeterminacy :
  LargePlaintiffClassMeansIndeterminateAsMatterOfLogic → ⊥
largeClassDoesNotLogicallyEntailIndeterminacy ()

foreseeabilityIsNotEncodedAsSufficientByDefinition :
  ForeseeabilityAloneCreatesDutyAsMatterOfLogic → ⊥
foreseeabilityIsNotEncodedAsSufficientByDefinition ()
