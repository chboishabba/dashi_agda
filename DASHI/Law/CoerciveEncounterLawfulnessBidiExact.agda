module DASHI.Law.CoerciveEncounterLawfulnessBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
import DASHI.Core.IntersectionalNonFactorability as NF
import DASHI.Law.QueenslandWandingReachabilityBidiExact as Wand

------------------------------------------------------------------------
-- Occurrence, authority, lawfulness and evidentiary state are independent.
------------------------------------------------------------------------

data OccurrenceState : Set where
  occurred didNotOccur occurrenceUnresolved : OccurrenceState

data AuthorityState : Set where
  authorityPresent authorityAbsent authorityUnresolved : AuthorityState

data LawfulnessState : Set where
  lawful unlawful lawfulnessUnresolved notApplicable : LawfulnessState

data EvidenceState : Set where
  positiveReceipt negativeReceipt conflictingReceipts missingReceipt inadmissibleReceipt : EvidenceState

data SafeguardKind : Set where
  identityNotice purposeNotice nonComplianceNotice leastInvasive detentionDuration separateSearchPredicate : SafeguardKind

record LegalTransitionFibre : Set where
  constructor legalTransitionFibre
  field
    fromPhase toPhase : Wand.EncounterPhase
    occurrence : OccurrenceState
    authority : AuthorityState
    lawfulness : LawfulnessState
    evidence : EvidenceState
    safeguardEvidence : SafeguardKind → EvidenceState
    producer : Wand.ProducerObligation
    legalReference : String

open LegalTransitionFibre public

------------------------------------------------------------------------
-- No-promotion boundaries.
------------------------------------------------------------------------

record LawfulnessBoundary : Set where
  constructor lawfulnessBoundary
  field
    occurrenceImpliesAuthority : Bool
    occurrenceImpliesAuthorityIsFalse : occurrenceImpliesAuthority ≡ false
    authorityImpliesLawfulExercise : Bool
    authorityImpliesLawfulExerciseIsFalse : authorityImpliesLawfulExercise ≡ false
    successfulOutcomeRetroactivelyLegalisesPriorEdge : Bool
    successfulOutcomeRetroactivelyLegalisesPriorEdgeIsFalse :
      successfulOutcomeRetroactivelyLegalisesPriorEdge ≡ false
    missingEvidenceIsNegativeEvidence : Bool
    missingEvidenceIsNegativeEvidenceIsFalse : missingEvidenceIsNegativeEvidence ≡ false
    unlawfulAutomaticallyMeansEvidenceExcluded : Bool
    unlawfulAutomaticallyMeansEvidenceExcludedIsFalse :
      unlawfulAutomaticallyMeansEvidenceExcluded ≡ false

canonicalLawfulnessBoundary : LawfulnessBoundary
canonicalLawfulnessBoundary =
  lawfulnessBoundary false refl false refl false refl false refl false refl

------------------------------------------------------------------------
-- Distinct concrete witnesses with the same occurrence but different legal
-- state.  This makes lawfulness non-factorable through mere occurrence.
------------------------------------------------------------------------

data OccurrenceSurface : Set where
  occurredSurface : OccurrenceSurface

data LegalOutcome : Set where
  legalOutcome lawfulOutcome : LegalOutcome

data LawfulnessWitnessState : Set where
  happenedUnlawfully happenedLawfully : LawfulnessWitnessState

occurrenceProjection : LawfulnessWitnessState → OccurrenceSurface
occurrenceProjection happenedUnlawfully = occurredSurface
occurrenceProjection happenedLawfully = occurredSurface

legalOutcomeProjection : LawfulnessWitnessState → LegalOutcome
legalOutcomeProjection happenedUnlawfully = legalOutcome
legalOutcomeProjection happenedLawfully = lawfulOutcome

lawfulnessOutcomesDiffer :
  legalOutcomeProjection happenedUnlawfully ≡ legalOutcomeProjection happenedLawfully → ⊥
lawfulnessOutcomesDiffer ()

occurrenceDoesNotDetermineLawfulness :
  NF.NonFactorabilityWitness occurrenceProjection legalOutcomeProjection
occurrenceDoesNotDetermineLawfulness =
  NF.nonFactorabilityWitness
    happenedUnlawfully happenedLawfully refl lawfulnessOutcomesDiffer

occurrenceCannotReconstructLawfulness :
  NF.FactorsThrough occurrenceProjection legalOutcomeProjection → ⊥
occurrenceCannotReconstructLawfulness =
  NF.witnessRulesOutEveryFlatFactorisation occurrenceDoesNotDetermineLawfulness

------------------------------------------------------------------------
-- Lawfulness cutset.  A lawful edge requires independently closed coordinates.
------------------------------------------------------------------------

record LawfulnessCutset (edge : LegalTransitionFibre) : Set where
  constructor lawfulnessCutset
  field
    occurrenceClosed : occurrence edge ≡ occurred
    authorityClosed : authority edge ≡ authorityPresent
    exerciseClosed : lawfulness edge ≡ lawful
    producerReceiptClosed : evidence edge ≡ positiveReceipt
    cutsetReference : String

open LawfulnessCutset public

record SafeguardClosure (edge : LegalTransitionFibre) : Set where
  constructor safeguardClosure
  field
    identityNoticeClosed : safeguardEvidence edge identityNotice ≡ positiveReceipt
    purposeNoticeClosed : safeguardEvidence edge purposeNotice ≡ positiveReceipt
    nonComplianceNoticeClosed : safeguardEvidence edge nonComplianceNotice ≡ positiveReceipt
    leastInvasiveClosed : safeguardEvidence edge leastInvasive ≡ positiveReceipt
    detentionDurationClosed : safeguardEvidence edge detentionDuration ≡ positiveReceipt
    safeguardReference : String

open SafeguardClosure public

------------------------------------------------------------------------
-- Reachability and lawful reachability are distinct.
------------------------------------------------------------------------

data ReachabilityState : Set where
  unreachable reachable lawfullyReachable : ReachabilityState

record ReachabilityLawfulnessWitness : Set where
  constructor reachabilityLawfulnessWitness
  field
    physicalReachability : ReachabilityState
    legalReachability : ReachabilityState
    physicallyReachable : physicalReachability ≡ reachable
    notYetLawfullyReachable : legalReachability ≡ unreachable
    reachabilityReference : String

open ReachabilityLawfulnessWitness public

canonicalReachableButNotLawfullyClosed : ReachabilityLawfulnessWitness
canonicalReachableButNotLawfullyClosed =
  reachabilityLawfulnessWitness reachable unreachable refl refl
    "physical search reachability does not establish legal closure"

------------------------------------------------------------------------
-- Remedies are a separate consumer fibre.
------------------------------------------------------------------------

data RemedyState : Set where
  exclusion suppression civilRemedy disciplinaryRemedy criminalConsequence
  noAvailableRemedy remedyUnresolved : RemedyState

record RemedyConsumer : Set where
  constructor remedyConsumer
  field
    edgeLawfulness : LawfulnessState
    applicableRemedy : RemedyState
    remedyEvidence : EvidenceState
    remedyReference : String

open RemedyConsumer public

------------------------------------------------------------------------
-- Evidence-state routing: missing is not negative; conflict is not closure.
------------------------------------------------------------------------

data ClosureState : Set where
  closed openMissing openConflict openInadmissible openNegative : ClosureState

closureOf : EvidenceState → ClosureState
closureOf positiveReceipt = closed
closureOf negativeReceipt = openNegative
closureOf conflictingReceipts = openConflict
closureOf missingReceipt = openMissing
closureOf inadmissibleReceipt = openInadmissible

missingReceiptRemainsOpen : closureOf missingReceipt ≡ openMissing
missingReceiptRemainsOpen = refl

conflictingReceiptsRemainOpen : closureOf conflictingReceipts ≡ openConflict
conflictingReceiptsRemainOpen = refl

------------------------------------------------------------------------
-- Queensland-specific legal reference kept as provenance, not proof by string.
------------------------------------------------------------------------

queenslandWandingSafeguardReference : String
queenslandWandingSafeguardReference =
  "Police Powers and Responsibilities Act 2000 (Qld), s 39H safeguards; ss 29, 30(1)(l), 39K downstream separation"
