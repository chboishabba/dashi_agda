{-# OPTIONS --safe #-}
module DASHI.Mathematics.Complexity.Karp21CookAllWordCertificateBoundExact where

------------------------------------------------------------------------
-- K00 SAME-WORD CERTIFICATE BOUND.
--
-- Source-owner cut:
--  * Karp21CookStrictWordCanonicalReencodeExact proves the strong
--    decoder LEFT INVERSE using only Golden-safe Cook syntax owners.
--  * This file imports the finite occurrence verifier separately.
--    Its own Golden import closure remains OPEN until that entire
--    verifier and sparse-graph dependency chain is marked/checked safe.
--
-- The theorem is over every accepted STRICT Cook input word.
-- No alternative SAT grammar or unbounded max-var-ID certificate.
-- Cook (1971); Leonid A. Levin (1973); DASHI K00 source owners.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Maybe.Base using (nothing; just)
open import Data.Empty using (⊥-elim)
open import Data.Nat.Base using (_≤_)
open import Relation.Binary.PropositionalEquality using (subst)

import DASHI.Mathematics.Complexity.FiniteWordSizeExact as Word
import DASHI.Mathematics.Complexity.Karp21CookStrictTripleBitBoundaryExact as Strict
import DASHI.Mathematics.Complexity.Karp21CookExecutableFiniteVerifierBidiExact as Verifier
import DASHI.Mathematics.Complexity.Karp21CookStrictWordCanonicalReencodeExact as Canonical
import DASHI.Mathematics.Complexity.Karp21SparseEndpointConsistencySoundExact as N21

k00StrictAcceptedWordCertificateBound :
  (word bits : Word.BitWord) →
  Verifier.verifyStrictCookSATWord word bits ≡ true →
  Word.encodingSize bits ≤ Word.encodingSize word
k00StrictAcceptedWordCertificateBound word bits verified
  with Strict.strictDecodeCookFormulaBits word
... | nothing = ⊥-elim (N21.falseNotTrue verified)
... | just formula =
  subst
    (λ actualWord →
      Word.encodingSize bits ≤ Word.encodingSize actualWord)
    (Canonical.k00StrictAcceptedWordCanonicalReencode word formula refl)
    (Verifier.cookExecutableCertificateCanonicalSize
      formula bits verified)
