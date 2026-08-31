module DASHI.Reasoning.PredicateNormalFormEvidenceAuditExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- PREDICATE NORMAL FORM FOR EVIDENCE-BEARING ASSERTIONS
--
-- "PNF" here means Predicate Normal Form.  The purpose is not to claim a
-- complete logical normalisation procedure for natural language.  It is a
-- typed audit surface which forces consequential assertions to expose the
-- quantifiers, domains, predicates, relations and inferential force that can
-- otherwise be hidden by prose.
------------------------------------------------------------------------

data QuantifierForce : Set where
  existentialQ
  studyPopulationQ
  boundedUniversalQ
  universalQ : QuantifierForce

data InferentialForce : Set where
  descriptiveF
  associationalF
  comparativeF
  causalF
  bestPracticeF
  normativeF : InferentialForce

data PredicateRole : Set where
  populationPredicate
  contextPredicate
  interventionPredicate
  comparatorPredicate
  outcomePredicate
  temporalPredicate
  causalPredicate
  transportPredicate
  significancePredicate
  authorityPredicate : PredicateRole

record PredicateAtom : Set where
  constructor predicateAtom
  field
    predicateName : String
    predicateRole : PredicateRole
    predicateDomain : String
    predicateReading : String

open PredicateAtom public

record AssertionScope : Set where
  constructor assertionScope
  field
    population : String
    setting : String
    intervention : String
    comparator : String
    outcome : String
    timeWindow : String

open AssertionScope public

record PredicateNormalAssertion : Set where
  constructor predicateNormalAssertion
  field
    assertionKey : String
    naturalLanguage : String
    quantifier : QuantifierForce
    inferentialForce : InferentialForce
    scope : AssertionScope
    predicates : List PredicateAtom
    provenance : String

open PredicateNormalAssertion public

------------------------------------------------------------------------
-- Each dimension can generate its own proof obligation.  A citation can
-- discharge some obligations while leaving others open; there is no forced
-- all-or-nothing "match" judgement at the generic layer.
------------------------------------------------------------------------

data ObligationKind : Set where
  predicateContentObligation
  quantifierObligation
  populationScopeObligation
  contextScopeObligation
  comparatorObligation
  outcomeObligation
  temporalObligation
  causalForceObligation
  transportObligation
  practicalSignificanceObligation
  normativePromotionObligation : ObligationKind

record AssertionObligation : Set where
  constructor assertionObligation
  field
    parentAssertion : String
    obligationKind : ObligationKind
    obligationReading : String

open AssertionObligation public

data ObligationStatus : Set where
  discharged
  partiallyDischarged
  unresolved
  contradictedAtSameScope
  inadmissibleEvidence : ObligationStatus

record ObligationAudit : Set where
  constructor obligationAudit
  field
    obligation : AssertionObligation
    status : ObligationStatus
    evidenceReceipt : String
    auditReason : String

open ObligationAudit public

------------------------------------------------------------------------
-- Promotion deltas.  These constructors make the common forms of claim
-- amplification visible instead of allowing them to disappear in prose.
------------------------------------------------------------------------

data PromotionDelta : Set where
  sameAssertionStrength
  widensPopulation
  widensContext
  strengthensQuantifier
  strengthensCausalForce
  strengthensComparativeForce
  strengthensNormativeForce
  dropsContextPredicate
  dropsComparator
  dropsUncertainty : PromotionDelta

record ProposedPromotion : Set where
  constructor proposedPromotion
  field
    upstream : PredicateNormalAssertion
    downstream : PredicateNormalAssertion
    delta : PromotionDelta

open ProposedPromotion public

-- Promotion is proof-relevant.  The unchanged case can proceed on the existing
-- warrant.  Any strengthening must name a NEW evidence receipt.  This is the
-- logical analogue of the repository's existing proof-relevant transition
-- admission discipline.

data PromotionReceipt : PromotionDelta → Set where
  preservedReceipt : PromotionReceipt sameAssertionStrength
  additionalEvidenceReceipt :
    {delta : PromotionDelta} →
    String →
    PromotionReceipt delta

data MayPromote (proposal : ProposedPromotion) : Set where
  promote : PromotionReceipt (delta proposal) → MayPromote proposal

promotionHasReceipt :
  {proposal : ProposedPromotion} →
  MayPromote proposal →
  PromotionReceipt (delta proposal)
promotionHasReceipt (promote receipt) = receipt

------------------------------------------------------------------------
-- Quantifier logic boundaries used by the education audit.
------------------------------------------------------------------------

data LogicalShape : Set where
  someInstance
  allInstances
  noInstance : LogicalShape

some≢all : ¬ (someInstance ≡ allInstances)
some≢all ()

all≢none : ¬ (allInstances ≡ noInstance)
all≢none ()

some≢none : ¬ (someInstance ≡ noInstance)
some≢none ()

-- Failure of a universal is not definitionally the assertion that every
-- instance fails.  The two logical shapes remain constructor-disjoint.
failedUniversal≢universalFailure :
  ¬ (someInstance ≡ noInstance)
failedUniversal≢universalFailure = some≢none

------------------------------------------------------------------------
-- Canonical complex educational specimen.
------------------------------------------------------------------------

explicitInstructionScope : AssertionScope
explicitInstructionScope =
  assertionScope
    "all students"
    "all Australian classrooms"
    "explicit instruction"
    "relevant comparator"
    "learning outcome"
    "unspecified"

explicitInstructionPredicates : List PredicateAtom
explicitInstructionPredicates =
  predicateAtom "receives" interventionPredicate "student × instruction × context"
    "student receives the nominated instructional practice"
  ∷ predicateAtom "improves" outcomePredicate "student × outcome × context"
    "the nominated outcome improves"
  ∷ predicateAtom "causally-attributed" causalPredicate "intervention × outcome"
    "improvement is attributable to the intervention rather than merely associated"
  ∷ predicateAtom "transportable" transportPredicate "study context × target context"
    "the result transports to the target population and setting"
  ∷ []

explicitInstructionUniversalAssertion : PredicateNormalAssertion
explicitInstructionUniversalAssertion =
  predicateNormalAssertion
    "education-example-explicit-instruction-universal"
    "Explicit instruction is effective for all students."
    universalQ
    causalF
    explicitInstructionScope
    explicitInstructionPredicates
    "generic audit specimen; not an empirical DASHI claim"

record PredicateNormalFormBoundary : Set where
  constructor predicateNormalFormBoundary
  field
    naturalLanguageClaimIsAtomicByDefault : Bool
    citationPresenceDischargesEveryPredicate : Bool
    failedUniversalMeansEveryInstanceFails : Bool
    contextPredicateMayBeDroppedWithoutReceipt : Bool
    strongerDownstreamClaimNeedsNewEvidenceReceipt : Bool

canonicalPredicateNormalFormBoundary : PredicateNormalFormBoundary
canonicalPredicateNormalFormBoundary =
  predicateNormalFormBoundary false false false false true
