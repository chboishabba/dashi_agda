module DASHI.Ontology.LeanWikidataDerivationFibreAdapter where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

open import DASHI.Ontology.EpistemicTrit
open import DASHI.Ontology.LeanWikidataVerdictBridge
open import DASHI.Ontology.LeanWikidataSourceRegressionBridge
import DASHI.Interop.WikidataDerivationFibreBridge as Fibre

------------------------------------------------------------------------
-- James's theorem-certified positive/negative/open verdicts map exactly onto
-- the existing DASHI derivation-fibre polarity.  This is stronger than carrying
-- the Lean result only as metadata: it can now participate in the existing
-- support/contradiction/both/undetermined validation machinery.
------------------------------------------------------------------------

polarityFromVerdict : LeanCertifiedVerdict → Fibre.DerivationPolarity
polarityFromVerdict verdict with positivePropositionState verdict
... | supported = Fibre.supporting
... | contradicted = Fibre.contradicting
... | unresolved = Fibre.unresolved

certifiedPositiveBecomesSupporting :
  polarityFromVerdict artistUnionVerdict ≡ Fibre.supporting
certifiedPositiveBecomesSupporting = refl

certifiedNegativeBecomesContradicting :
  polarityFromVerdict artistNotDisjointUnionVerdict ≡ Fibre.contradicting
certifiedNegativeBecomesContradicting = refl

uncertifiedVerdict : LeanCertifiedVerdict
uncertifiedVerdict =
  leanCertifiedVerdict
    artistUnionComputed
    "unexecuted artist union candidate"
    true
    false
    notObserved
    refs

uncertifiedBecomesUnresolved :
  polarityFromVerdict uncertifiedVerdict ≡ Fibre.unresolved
uncertifiedBecomesUnresolved = refl

------------------------------------------------------------------------
-- Generic adapter into an existing claim fibre.
------------------------------------------------------------------------

derivationFromLeanVerdict :
  (claim : Fibre.ClaimBase) →
  LeanCertifiedVerdict →
  String →
  List Fibre.OntologyAxis →
  String →
  List String →
  Fibre.Derivation claim
derivationFromLeanVerdict claim verdict derivationId axes evidence obligations =
  Fibre.derivation
    derivationId
    (polarityFromVerdict verdict)
    axes
    evidence
    (propositionLabel verdict)
    obligations

------------------------------------------------------------------------
-- Concrete fibre regression: the same surface proposition can carry a source
-- theorem that supports it and another theorem that contradicts a stronger
-- formulation.  DASHI's existing presence semantics preserve both rather than
-- collapsing one into the other.
------------------------------------------------------------------------

artistClassClaim : Fibre.ClaimBase
artistClassClaim =
  Fibre.claimBase
    "class-algebra:artist"
    "artist is union/disjoint-union of painter and sculptor"
    Fibre.wikidataStatementClaim
    Fibre.mainValueRole
    "artistKB:05ba35f5ca702fd446a8dc290244e299e717f63bcc571b4aaf3b78e3c7927a8b"

artistUnionDerivation : Fibre.Derivation artistClassClaim
artistUnionDerivation =
  derivationFromLeanVerdict
    artistClassClaim
    artistUnionVerdict
    "lean:artistKB_unionOk"
    (Fibre.externalAxis "James-ClassAlgebra" ∷ [])
    "Wikidata.ClassAlgebraExample.artistKB_unionOk"
    []

artistDisjointUnionDerivation : Fibre.Derivation artistClassClaim
artistDisjointUnionDerivation =
  derivationFromLeanVerdict
    artistClassClaim
    artistNotDisjointUnionVerdict
    "lean:artistKB_not_dunOk"
    (Fibre.externalAxis "James-ClassAlgebra" ∷ [])
    "Wikidata.ClassAlgebraExample.artistKB_not_dunOk"
    []

artistUnionPolaritySupporting :
  Fibre.derivationPolarity artistUnionDerivation ≡ Fibre.supporting
artistUnionPolaritySupporting = refl

artistDisjointUnionPolarityContradicting :
  Fibre.derivationPolarity artistDisjointUnionDerivation ≡ Fibre.contradicting
artistDisjointUnionPolarityContradicting = refl

-- At the fibre-presence layer, simultaneous support and contradiction is kept
-- explicitly as `both`; the bridge does not force a binary winner.
sourceDisagreementPreservedAsBoth :
  Fibre.fibreOutcomeFromPresence true true ≡ Fibre.both
sourceDisagreementPreservedAsBoth = refl

sourceAbsencePreservedUndetermined :
  Fibre.validateRequiredSubfibre Fibre.axisRequired false false
  ≡ Fibre.fibreShape Fibre.undetermined
sourceAbsencePreservedUndetermined = refl
