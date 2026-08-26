module DASHI.Cognition.PNF.FreshReplayAuthorityAdmissionExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)

------------------------------------------------------------------------
-- Fresh-vs-replay authority admission.
--
-- Runtime correspondence: SensibLaw's producer-complete numeric token writer
-- uses PostgreSQL INSERT ... ON CONFLICT DO NOTHING RETURNING. A row returned
-- by that exact INSERT is a proof-relevant witness that the current statement
-- admitted the producer row. It therefore needs no second persistent readback
-- merely to prove equality with itself. A token absent from RETURNING belongs to
-- the conflict/replay fibre and must carry an explicit authority-equality proof.
--
-- This is deliberately not a claim that replay never needs I/O. It moves the
-- verification obligation from the whole proposed fibre onto precisely the
-- pre-existing/conflicting fibre.
------------------------------------------------------------------------

data AdmissionKind : Set where
  freshAdmission : AdmissionKind
  replayAdmission : AdmissionKind

record AuthorityAdmission
  (Row : Set)
  (producerRow : Row)
  : Set where
  constructor authorityAdmission
  field
    kind : AdmissionKind
    authorityRow : Row
    authorityExact : authorityRow ≡ producerRow
    persistentParityReads : Nat

open AuthorityAdmission public

-- RETURNING supplies the row admitted by this statement. The final authority
-- row is therefore definitionally the producer row; no equality reread is a
-- semantic obligation.
freshAuthorityAdmission :
  ∀ {Row : Set} (producerRow : Row) →
  AuthorityAdmission Row producerRow
freshAuthorityAdmission producerRow =
  authorityAdmission freshAdmission producerRow refl zero

freshNeedsNoParityRead :
  ∀ {Row : Set} (producerRow : Row) →
  persistentParityReads (freshAuthorityAdmission producerRow) ≡ zero
freshNeedsNoParityRead producerRow = refl

freshAuthorityIsProducerRow :
  ∀ {Row : Set} (producerRow : Row) →
  authorityRow (freshAuthorityAdmission producerRow) ≡ producerRow
freshAuthorityIsProducerRow producerRow = refl

-- A replay/conflict row predates the current admission. It is accepted only
-- when an explicit proof establishes equality with the producer's proposed
-- authority row. The unit read count represents one set-wise replay evidence
-- operation for this abstract item, not a mandate for one SQL query per row.
replayAuthorityAdmission :
  ∀ {Row : Set}
    (producer existing : Row) →
  existing ≡ producer →
  AuthorityAdmission Row producer
replayAuthorityAdmission producer existing exact =
  authorityAdmission replayAdmission existing exact (suc zero)

replayCarriesExactParity :
  ∀ {Row : Set}
    (producer existing : Row)
    (exact : existing ≡ producer) →
  authorityRow (replayAuthorityAdmission producer existing exact) ≡ producer
replayCarriesExactParity producer existing exact = exact

replayCarriesParityEvidence :
  ∀ {Row : Set}
    (producer existing : Row)
    (exact : existing ≡ producer) →
  persistentParityReads (replayAuthorityAdmission producer existing exact)
    ≡ suc zero
replayCarriesParityEvidence producer existing exact = refl

-- Every consumer sees the producer row after either certified route.
mapEquality :
  ∀ {A B : Set} (observe : A → B) {left right : A} →
  left ≡ right →
  observe left ≡ observe right
mapEquality observe refl = refl

freshConsumerExact :
  ∀ {Row Observation : Set}
    (observe : Row → Observation)
    (producer : Row) →
  observe (authorityRow (freshAuthorityAdmission producer)) ≡ observe producer
freshConsumerExact observe producer = refl

replayConsumerExact :
  ∀ {Row Observation : Set}
    (observe : Row → Observation)
    (producer existing : Row)
    (exact : existing ≡ producer) →
  observe (authorityRow (replayAuthorityAdmission producer existing exact))
    ≡ observe producer
replayConsumerExact observe producer existing exact =
  mapEquality observe exact

------------------------------------------------------------------------
-- Fibre-level admissibility boundary.
--
-- Classification into fresh/replay is supplied by the physical authority
-- operation. The theorem requires no readback certificate for fresh members and
-- an explicit equality witness for every replay member.
------------------------------------------------------------------------

record FreshReplayAdmissionPolicy (Item Row : Set) : Set₁ where
  field
    producerRow : Item → Row
    admission : (item : Item) → AuthorityAdmission Row (producerRow item)
    finalAuthorityExact :
      ∀ item → authorityRow (admission item) ≡ producerRow item

open FreshReplayAdmissionPolicy public

compileFreshOnlyPolicy :
  ∀ {Item Row : Set}
    (row : Item → Row) →
  FreshReplayAdmissionPolicy Item Row
compileFreshOnlyPolicy row = record
  { producerRow = row
  ; admission = λ item → freshAuthorityAdmission (row item)
  ; finalAuthorityExact = λ item → refl
  }

-- Internal DASHI/ITIR theorem; no external DOI is asserted.
