module DASHI.Governance.GovernanceQuotientCoreBridge where

open import Agda.Builtin.Bool using (false; true)
import DASHI.Core.FibreRestrictionCore as Fibre
import DASHI.Core.ProvenanceBearingQuotient as CoreQuotient
import DASHI.Governance.QuotientDefectResidualRouting as Governance

------------------------------------------------------------------------
-- Adapter: the governance quotient does not own another quotient theory.
-- It packages policy/proposition-specific defect + provenance data into the
-- canonical DASHI.Core provenance-bearing quotient interface.
------------------------------------------------------------------------

record GovernanceReceipt (Q : Governance.QuotientReceiptSystem) : Set where
  constructor governanceReceipt
  field
    defectReceipt : Governance.Defect Q
    provenanceReceipt : Governance.Provenance Q

open GovernanceReceipt public

record GovernanceCoreView
    (Q : Governance.QuotientReceiptSystem) : Set₁ where
  field
    restrictsFibre : Governance.Proposition Q → Governance.Coarse Q → Set

open GovernanceCoreView public

toFibreRestrictionCore :
  (Q : Governance.QuotientReceiptSystem) →
  GovernanceCoreView Q →
  Fibre.FibreRestrictionCore
toFibreRestrictionCore Q view =
  Fibre.fibreRestrictionCore
    (Governance.Fine Q)
    (Governance.Coarse Q)
    (Governance.Proposition Q)
    (Governance.project Q)
    (λ _ → Governance.Defect Q)
    (restrictsFibre view)
    true
    false

receiptOf :
  (Q : Governance.QuotientReceiptSystem) →
  Governance.Fine Q → GovernanceReceipt Q
receiptOf Q x =
  governanceReceipt
    (Governance.defect Q x)
    (Governance.provenance Q x)

reopenAt :
  (Q : Governance.QuotientReceiptSystem) →
  Governance.Proposition Q →
  Governance.Coarse Q →
  GovernanceReceipt Q →
  Governance.Fine Q
reopenAt Q proposition surface receipt =
  Governance.resolveFor Q proposition surface
    (defectReceipt receipt)
    (provenanceReceipt receipt)

------------------------------------------------------------------------
-- The existing governance relevant-reopening theorem becomes literally an
-- instance of DASHI.Core.RelevantProvenanceBearingQuotient at a fixed consumer
-- proposition.  The relevant relation is flipped only to match the core's
-- (reopened, original) argument order.
------------------------------------------------------------------------

toRelevantCoreQuotientAt :
  (Q : Governance.QuotientReceiptSystem) →
  (view : GovernanceCoreView Q) →
  (reopening : Governance.PropositionRelevantReopening Q) →
  (proposition : Governance.Proposition Q) →
  CoreQuotient.RelevantProvenanceBearingQuotient
    (toFibreRestrictionCore Q view)
    (λ reopened original →
      Governance.RelevantEquivalent reopening proposition original reopened)
toRelevantCoreQuotientAt Q view reopening proposition =
  CoreQuotient.relevantProvenanceBearingQuotient
    (GovernanceReceipt Q)
    (receiptOf Q)
    (reopenAt Q proposition)
    (Governance.reopenRelevant reopening proposition)
