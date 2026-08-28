module DASHI.Foundations.Wette1969Rule915CertifiedObligationApplicationExact where

------------------------------------------------------------------------
-- CERTIFIED 9.1.5 APPLICATION FROM FACTORED OBLIGATION EVIDENCE
------------------------------------------------------------------------

open import DASHI.Core.Prelude
import Data.Fin as Fin

import DASHI.Core.ProofCarryingRuleApplicationExact as PCRA
import DASHI.Foundations.Wette1969HistoricalSignatureExact as Signature
import DASHI.Foundations.Wette1969Rule915PredicateProducerExact as Rule915
import DASHI.Foundations.Wette1969Rule915ObligationSubgraphsExact as Obligations
import DASHI.Foundations.Wette1969ProofCarryingRuleApplicationExact as Historical
import DASHI.Foundations.Wette1969FiniteDerivationContextExact as Finite

WordTerm = Signature.WordTerm
Context = Finite.DerivationContext

------------------------------------------------------------------------
-- The historical premise vector is ordered p01..p27.  The following eliminator
-- is intentionally boring: it is the exact weld between the source-indexed
-- obligation package and the existing Fin-indexed HistoricalRuleBody API.
------------------------------------------------------------------------

premisesHoldFromObligationEvidence :
  (context : Context) →
  (transcription : Rule915.Rule915PremiseTranscription) →
  (arity recursivePredicate : WordTerm) →
  Obligations.Rule915ObligationEvidence context transcription →
  Historical.PremisesHold
    Finite.finiteHistoricalContextSystem
    context
    (Rule915.rule9-1-5 transcription arity recursivePredicate)
premisesHoldFromObligationEvidence context transcription arity recursivePredicate evidence Fin.zero =
  Obligations.slotEvidence evidence _
premisesHoldFromObligationEvidence context transcription arity recursivePredicate evidence (Fin.suc Fin.zero) =
  Obligations.slotEvidence evidence _
premisesHoldFromObligationEvidence context transcription arity recursivePredicate evidence (Fin.suc (Fin.suc Fin.zero)) =
  Obligations.slotEvidence evidence _
premisesHoldFromObligationEvidence context transcription arity recursivePredicate evidence (Fin.suc (Fin.suc (Fin.suc Fin.zero))) =
  Obligations.slotEvidence evidence _
premisesHoldFromObligationEvidence context transcription arity recursivePredicate evidence (Fin.suc (Fin.suc (Fin.suc (Fin.suc Fin.zero)))) =
  Obligations.slotEvidence evidence _
premisesHoldFromObligationEvidence context transcription arity recursivePredicate evidence (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc Fin.zero))))) =
  Obligations.slotEvidence evidence _
premisesHoldFromObligationEvidence context transcription arity recursivePredicate evidence (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc Fin.zero)))))) =
  Obligations.slotEvidence evidence _
premisesHoldFromObligationEvidence context transcription arity recursivePredicate evidence (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc Fin.zero))))))) =
  Obligations.slotEvidence evidence _
premisesHoldFromObligationEvidence context transcription arity recursivePredicate evidence (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc Fin.zero)))))))) =
  Obligations.slotEvidence evidence _
premisesHoldFromObligationEvidence context transcription arity recursivePredicate evidence (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc Fin.zero))))))))) =
  Obligations.slotEvidence evidence _
premisesHoldFromObligationEvidence context transcription arity recursivePredicate evidence (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc Fin.zero)))))))))) =
  Obligations.slotEvidence evidence _
premisesHoldFromObligationEvidence context transcription arity recursivePredicate evidence (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc Fin.zero))))))))))) =
  Obligations.slotEvidence evidence _
premisesHoldFromObligationEvidence context transcription arity recursivePredicate evidence (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc Fin.zero)))))))))))) =
  Obligations.slotEvidence evidence _
premisesHoldFromObligationEvidence context transcription arity recursivePredicate evidence (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc Fin.zero))))))))))))) =
  Obligations.slotEvidence evidence _
premisesHoldFromObligationEvidence context transcription arity recursivePredicate evidence (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc Fin.zero)))))))))))))) =
  Obligations.slotEvidence evidence _
premisesHoldFromObligationEvidence context transcription arity recursivePredicate evidence (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc Fin.zero))))))))))))))) =
  Obligations.slotEvidence evidence _
premisesHoldFromObligationEvidence context transcription arity recursivePredicate evidence (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc Fin.zero)))))))))))))))) =
  Obligations.slotEvidence evidence _
premisesHoldFromObligationEvidence context transcription arity recursivePredicate evidence (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc Fin.zero))))))))))))))))) =
  Obligations.slotEvidence evidence _
premisesHoldFromObligationEvidence context transcription arity recursivePredicate evidence (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc Fin.zero)))))))))))))))))) =
  Obligations.slotEvidence evidence _
premisesHoldFromObligationEvidence context transcription arity recursivePredicate evidence (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc Fin.zero))))))))))))))))))) =
  Obligations.slotEvidence evidence _
premisesHoldFromObligationEvidence context transcription arity recursivePredicate evidence (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc Fin.zero)))))))))))))))))))) =
  Obligations.slotEvidence evidence _
premisesHoldFromObligationEvidence context transcription arity recursivePredicate evidence (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc Fin.zero))))))))))))))))))))) =
  Obligations.slotEvidence evidence _
premisesHoldFromObligationEvidence context transcription arity recursivePredicate evidence (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc Fin.zero)))))))))))))))))))))) =
  Obligations.slotEvidence evidence _
premisesHoldFromObligationEvidence context transcription arity recursivePredicate evidence (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc Fin.zero))))))))))))))))))))))) =
  Obligations.slotEvidence evidence _
premisesHoldFromObligationEvidence context transcription arity recursivePredicate evidence (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc Fin.zero)))))))))))))))))))))))) =
  Obligations.slotEvidence evidence _
premisesHoldFromObligationEvidence context transcription arity recursivePredicate evidence (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc Fin.zero))))))))))))))))))))))))) =
  Obligations.slotEvidence evidence _
premisesHoldFromObligationEvidence context transcription arity recursivePredicate evidence (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc Fin.zero)))))))))))))))))))))))))) =
  Obligations.slotEvidence evidence _

selectRule915FromObligationEvidence :
  (context : Context) →
  (transcription : Rule915.Rule915PremiseTranscription) →
  (arity recursivePredicate : WordTerm) →
  Obligations.Rule915ObligationEvidence context transcription →
  PCRA.SelectedRuleApplication
    (Historical.historicalRuleApplicationSystem Finite.finiteHistoricalContextSystem)
    context
selectRule915FromObligationEvidence context transcription arity recursivePredicate evidence =
  Rule915.selectRule915
    context transcription arity recursivePredicate
    (premisesHoldFromObligationEvidence
      context transcription arity recursivePredicate evidence)

record Wette1969Rule915CertifiedObligationApplicationBoundary : Set where
  constructor wette1969Rule915CertifiedObligationApplicationBoundary
  field
    factoredObligationEvidenceNowCertifiesRule915 : Bool
    factoredObligationEvidenceNowCertifiesRule915IsTrue :
      factoredObligationEvidenceNowCertifiesRule915 ≡ true
    shared1015EvidenceIsNotDuplicatedAtApplicationBoundary : Bool
    shared1015EvidenceIsNotDuplicatedAtApplicationBoundaryIsTrue :
      shared1015EvidenceIsNotDuplicatedAtApplicationBoundary ≡ true
    certified915StillRequiresHistoricalPremiseEvidence : Bool
    certified915StillRequiresHistoricalPremiseEvidenceIsTrue :
      certified915StillRequiresHistoricalPremiseEvidence ≡ true

canonicalWette1969Rule915CertifiedObligationApplicationBoundary :
  Wette1969Rule915CertifiedObligationApplicationBoundary
canonicalWette1969Rule915CertifiedObligationApplicationBoundary =
  wette1969Rule915CertifiedObligationApplicationBoundary
    true refl true refl true refl
