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
-- Concrete fibre regressions.
--
-- The source proves two DIFFERENT propositions about artistKB: the ordinary
-- union claim holds, while the stronger disjoint-union claim is refuted because
-- the parts overlap.  They therefore live over separate ClaimBase values.
------------------------------------------------------------------------

artistUnionClaim : Fibre.ClaimBase
artistUnionClaim =
  Fibre.claimBase
    "class-algebra:artist:union"
    "artist is the union of painter and sculptor"
    Fibre.wikidataStatementClaim
    Fibre.mainValueRole
    "artistKB:6e7c185bd7d97fa0eff022e9e3f51219158215bd15f2e79f938645e86c1c3723"

artistDisjointUnionClaim : Fibre.ClaimBase
artistDisjointUnionClaim =
  Fibre.claimBase
    "class-algebra:artist:disjoint-union"
    "artist is the disjoint union of painter and sculptor"
    Fibre.wikidataStatementClaim
    Fibre.mainValueRole
    "artistKB:6e7c185bd7d97fa0eff022e9e3f51219158215bd15f2e79f938645e86c1c3723"

artistUnionDerivation : Fibre.Derivation artistUnionClaim
artistUnionDerivation =
  derivationFromLeanVerdict
    artistUnionClaim
    artistUnionVerdict
    "lean:artistKB_unionOk"
    (Fibre.externalAxis "James-ClassAlgebra" ∷ [])
    "Wikidata.ClassAlgebraExample.artistKB_unionOk"
    []

artistDisjointUnionDerivation : Fibre.Derivation artistDisjointUnionClaim
artistDisjointUnionDerivation =
  derivationFromLeanVerdict
    artistDisjointUnionClaim
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

-- Existing fibre semantics remain available for genuinely competing derivations
-- of one and the same ClaimBase. The source bridge does not manufacture such a
-- conflict merely because one proposition strengthens another.
genuineSameClaimDisagreementWouldRemainBoth :
  Fibre.fibreOutcomeFromPresence true true ≡ Fibre.both
genuineSameClaimDisagreementWouldRemainBoth = refl

sourceAbsencePreservedUndetermined :
  Fibre.validateRequiredSubfibre Fibre.axisRequired false false
  ≡ Fibre.fibreShape Fibre.undetermined
sourceAbsencePreservedUndetermined = refl
