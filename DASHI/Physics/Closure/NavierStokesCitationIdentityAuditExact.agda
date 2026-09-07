module DASHI.Physics.Closure.NavierStokesCitationIdentityAuditExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Wikimedia.ScientificCitationQidBindingsExact as Citation

------------------------------------------------------------------------
-- BIBLIOGRAPHIC IDENTITY AUDIT
--
-- The current repository contains three comments that name the Caffarelli-
-- Kohn-Nirenberg Navier-Stokes paper but attach DOI
-- 10.1080/03605308208820218. Publisher metadata identifies that DOI as the
-- Fabes-Kenig-Serapioni paper "The local regularity of solutions of degenerate
-- elliptic equations". The canonical CKN DOI is 10.1002/cpa.3160350604.
--
-- This owner records the mismatch without rewriting theorem semantics. QID
-- alignment cannot repair a wrong publication identifier.
------------------------------------------------------------------------

record CitationIdentityMismatch : Set where
  constructor citation-identity-mismatch
  field
    declaredSourceName : String
    incorrectIdentifier : String
    canonicalIdentifier : String
    affectedFileReference : String
    correctionReference : String
open CitationIdentityMismatch public

cknMismatchLocalizationAbsorption : CitationIdentityMismatch
cknMismatchLocalizationAbsorption = citation-identity-mismatch
  "Caffarelli-Kohn-Nirenberg partial regularity"
  "doi:10.1080/03605308208820218"
  "doi:10.1002/cpa.3160350604"
  "DASHI/Physics/Closure/NSTriadKNYuFiniteLocalizationAbsorptionExact.agda"
  "publisher identity audit 2026-09-08"

cknMismatchLocalizationTail : CitationIdentityMismatch
cknMismatchLocalizationTail = citation-identity-mismatch
  "Caffarelli-Kohn-Nirenberg partial regularity"
  "doi:10.1080/03605308208820218"
  "doi:10.1002/cpa.3160350604"
  "DASHI/Physics/Closure/NSTriadKNYuLocalizationTailCriterionExact.agda"
  "publisher identity audit 2026-09-08"

cknMismatchCaccioppoliTail : CitationIdentityMismatch
cknMismatchCaccioppoliTail = citation-identity-mismatch
  "Caffarelli-Kohn-Nirenberg partial regularity"
  "doi:10.1080/03605308208820218"
  "doi:10.1002/cpa.3160350604"
  "DASHI/Physics/Closure/NSTriadKNYuLocalizationCaccioppoliTailExact.agda"
  "publisher identity audit 2026-09-08"

canonicalCKNBinding : Citation.CitationEntityBinding
canonicalCKNBinding = Citation.ckn

data QidRepairsWrongDoi : Set where
data SameAuthorNamesMakeWrongDoiHarmless : Set where

qidDoesNotRepairWrongDoi : QidRepairsWrongDoi → ⊥
qidDoesNotRepairWrongDoi ()
sameAuthorsDoNotRepairWrongDoi : SameAuthorNamesMakeWrongDoiHarmless → ⊥
sameAuthorsDoNotRepairWrongDoi ()

record NavierStokesCitationIdentityAuditBoundary : Set where
  constructor ns-citation-identity-audit-boundary
  field
    canonicalCknDoiPinned : Bool
    staleMismatchCountAtLeastThree : Bool
    qidCanReplaceDoiCorrection : Bool

canonicalNavierStokesCitationIdentityAuditBoundary : NavierStokesCitationIdentityAuditBoundary
canonicalNavierStokesCitationIdentityAuditBoundary =
  ns-citation-identity-audit-boundary true true false
