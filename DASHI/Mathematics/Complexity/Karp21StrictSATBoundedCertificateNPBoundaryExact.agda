{-# OPTIONS --safe #-}
module DASHI.Mathematics.Complexity.Karp21StrictSATBoundedCertificateNPBoundaryExact where

------------------------------------------------------------------------
-- K00: SAME STRICT SAT WORD, FINITE POLYNOMIALLY SHORT CERTIFICATE.
--
-- The earlier strict Cook verifier is a real Boolean procedure.
-- The canonical-input decoder left inverse now bounds its accepted
-- certificate by the *input word itself*, even for an arbitrary input.
--
-- This module closes all semantic and certificate-size inequalities
-- needed by the same-word SAT InNP result. It then exposes precisely
-- the two independent executable-machine resource obligations.
-- These remain parameters until the concrete machine-clock/size
-- definitions certify them; this file never promotes their existence.
--
-- The concrete-tape exact-run BIDI is kept in the separate
-- Karp21StrictSATConcreteRunBidiExact source owner. This semantic
-- certificate/conditional InNP module now depends only on Golden
-- Cook syntax, verification and polynomial-reduction cores.
-- Sources: Cook 1971, Leonid Levin 1973; DASHI prior theorem owners.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Nat.Base using (_≤_)
open import Data.Product using (Σ; _×_; _,_)
import DASHI.Mathematics.Complexity.PolynomialReductionExact as PR
import DASHI.Mathematics.Complexity.FiniteWordSizeExact as Word
import DASHI.Mathematics.Complexity.Karp21CookStrictSATLanguageExact as SAT
import DASHI.Mathematics.Complexity.Karp21CookExecutableFiniteVerifierBidiExact as Verify
import DASHI.Mathematics.Complexity.Karp21CookAllWordCertificateBoundExact as Canonical

-- The certificate is exactly List Bool; length is measured by the
-- canonical FiniteWordSizeExact source owner, NOT a separate metric.
strictSATCertificateAdmissible :
  Word.BitWord → Word.BitWord → Set
strictSATCertificateAdmissible word certificate =
  Word.encodingSize certificate ≤ Word.encodingSize word

BoundedStrictSATWitnessYES : Word.BitWord → Set
BoundedStrictSATWitnessYES word =
  Σ Word.BitWord
    (λ certificate →
      strictSATCertificateAdmissible word certificate
      × Verify.verifyStrictCookSATWord word certificate ≡ true)

strictSATToBoundedWitness :
  (word : Word.BitWord) →
  PR.accepts SAT.strictSATLanguage word →
  BoundedStrictSATWitnessYES word
strictSATToBoundedWitness word sat
  with Verify.strictCookExecutableVerifierComplete word sat
... | certificate , verified =
  certificate ,
    ( Canonical.k00StrictAcceptedWordCertificateBound
        word certificate verified
    , verified )

boundedWitnessToStrictSAT :
  (word : Word.BitWord) →
  BoundedStrictSATWitnessYES word →
  PR.accepts SAT.strictSATLanguage word
boundedWitnessToStrictSAT word
  (certificate , (bounded , verified)) =
  Verify.strictCookExecutableVerifierSound word
    (certificate , verified)

k00StrictSATBoundedWitnessBidi :
  (word : Word.BitWord) →
  PR.Iff
    (PR.accepts SAT.strictSATLanguage word)
    (BoundedStrictSATWitnessYES word)
k00StrictSATBoundedWitnessBidi word =
  PR.iff
    (strictSATToBoundedWitness word)
    (boundedWitnessToStrictSAT word)

-- An actual PR.InNP result from *exactly* the remaining clock and
-- generic model bound certificates. These are not filled by opaque
-- Bool "done" markers; they must inhabit the chosen nondegenerate
-- machine-cost interpretation.
k00StrictSATInNPFromConcreteResourceReceipts :
  (cost : PR.PolynomialCostModel Word.BitWord) →
  PR.polynomialTimeVerifier cost Verify.verifyStrictCookSATWord →
  PR.polynomialCertificateBound cost strictSATCertificateAdmissible →
  PR.InNP cost SAT.strictSATLanguage
k00StrictSATInNPFromConcreteResourceReceipts
  cost verifierClock certificateBound =
  record
    { PR.Certificate = Word.BitWord
    ; PR.verifies = Verify.verifyStrictCookSATWord
    ; PR.certificateAdmissible = strictSATCertificateAdmissible
    ; PR.sound = λ word certificate _ verified →
        Verify.strictCookExecutableVerifierSound word
          (certificate , verified)
    ; PR.complete = strictSATToBoundedWitness
    ; PR.polynomialVerification = verifierClock
    ; PR.polynomialCertificateSize = certificateBound
    }

