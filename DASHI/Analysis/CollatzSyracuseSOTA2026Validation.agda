module DASHI.Analysis.CollatzSyracuseSOTA2026Validation where

open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Analysis.CollatzSyracuseSOTA2026Exact as SOTA

sourceAtlasPaid :
  SOTA.CollatzSOTA2026Boundary.attributedSourceAtlasPaid
    SOTA.canonicalCollatzSOTA2026Boundary
  ≡ 1
sourceAtlasPaid = refl

peerReviewedAndPreprintSeparated :
  SOTA.CollatzSOTA2026Boundary.peerReviewedAndPreprintRolesSeparated
    SOTA.canonicalCollatzSOTA2026Boundary
  ≡ 1
peerReviewedAndPreprintSeparated = refl

sourcesDoNotImportProof :
  SOTA.CollatzSOTA2026Boundary.externalSourcesImportCollatzProof
    SOTA.canonicalCollatzSOTA2026Boundary
  ≡ 0
sourcesDoNotImportProof = refl
