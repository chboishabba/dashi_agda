module DASHI.Ontology.LeanWikidataVerdictBridge where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List)
open import Agda.Builtin.String using (String)

open import DASHI.Ontology.EpistemicTrit
open import DASHI.Ontology.LeanWikidataTheoremSurfaceBridge

------------------------------------------------------------------------
-- A source theorem can certify either P = true or P = false.  That is
-- different from merely running a positive checker and observing failure.
--
-- `notObserved` is the open-world/no-certificate case and remains unresolved.
-- `certifiedHolds` and `certifiedRefuted` are both positive statements about
-- what the pinned Lean theorem proves; only when we interpret them relative to
-- an expected-positive proposition does certifiedRefuted become contradicted.
------------------------------------------------------------------------

data ObjectVerdict : Set where
  notObserved certifiedHolds certifiedRefuted : ObjectVerdict

record LeanCertifiedVerdict : Set where
  constructor leanCertifiedVerdict
  field
    theoremContract : LeanTheoremContract
    propositionLabel : String
    sourceMatched : Bool
    theoremAccepted : Bool
    objectVerdict : ObjectVerdict
    sourceReferences : List String

open LeanCertifiedVerdict public

-- Evidence for the *reported theorem proposition* is supported whenever the
-- exact source and theorem are accepted, irrespective of whether that theorem
-- says an object-level Boolean is true or false.
verdictReportState : LeanCertifiedVerdict → EpistemicTrit
verdictReportState verdict with sourceMatched verdict | theoremAccepted verdict
... | true | true = supported
... | _ | _ = unresolved

-- Interpretation relative to a positive proposition P.
positivePropositionState : LeanCertifiedVerdict → EpistemicTrit
positivePropositionState verdict with sourceMatched verdict | theoremAccepted verdict | objectVerdict verdict
... | true | true | certifiedHolds = supported
... | true | true | certifiedRefuted = contradicted
... | _ | _ | _ = unresolved

certifiedTrueSupportsPositive :
  (contract : LeanTheoremContract) (label : String) (refs : List String) →
  positivePropositionState
    (leanCertifiedVerdict contract label true true certifiedHolds refs)
  ≡ supported
certifiedTrueSupportsPositive contract label refs = refl

certifiedFalseContradictsPositive :
  (contract : LeanTheoremContract) (label : String) (refs : List String) →
  positivePropositionState
    (leanCertifiedVerdict contract label true true certifiedRefuted refs)
  ≡ contradicted
certifiedFalseContradictsPositive contract label refs = refl

-- A failed/absent observation without a source-matched negative theorem is not
-- converted into contradiction. This retains the existing open-world rule.
uncertifiedAbsenceIsUnresolved :
  (contract : LeanTheoremContract) (label : String) (refs : List String) →
  positivePropositionState
    (leanCertifiedVerdict contract label true false notObserved refs)
  ≡ unresolved
uncertifiedAbsenceIsUnresolved contract label refs = refl

sourceMismatchIsUnresolvedVerdict :
  (contract : LeanTheoremContract) (label : String)
  (v : ObjectVerdict) (refs : List String) →
  positivePropositionState
    (leanCertifiedVerdict contract label false true v refs)
  ≡ unresolved
sourceMismatchIsUnresolvedVerdict contract label v refs = refl

------------------------------------------------------------------------
-- Imported verdicts remain evidence only.
------------------------------------------------------------------------

verdictCarriesTruthAuthority : LeanCertifiedVerdict → Bool
verdictCarriesTruthAuthority _ = false

verdictCarriesEditAuthority : LeanCertifiedVerdict → Bool
verdictCarriesEditAuthority _ = false

verdictTruthAuthorityFalse :
  (v : LeanCertifiedVerdict) → verdictCarriesTruthAuthority v ≡ false
verdictTruthAuthorityFalse v = refl

verdictEditAuthorityFalse :
  (v : LeanCertifiedVerdict) → verdictCarriesEditAuthority v ≡ false
verdictEditAuthorityFalse v = refl
