{-# OPTIONS --safe #-}

module DASHI.Mathematics.Complexity.Karp21CookExecutableFiniteVerifierBidiExact where

------------------------------------------------------------------------
-- K00: EXECUTABLE BOOLEAN SAT VERIFIER ON FINITE BINARY CERTIFICATES.
--
-- Cook's original BooleanFormula is the SAME source-owned AST;
-- a certificate has ONE Bool per syntactic variable occurrence.
-- Repeated-index consistency is checked, not assumed.
--
-- Previous Karp21CookFiniteOccurrenceWitnessExact supplied the
-- finite mathematical search relation and formula-size bound.
-- Here the concrete checker returns Bool, rejects wrong-length and
-- conflicting repeated-variable certificates, and is proved SOUND
-- and COMPLETE for actual Cook.Satisfiable.
--
-- The SAME checker is then placed behind the existing strict
-- three-bit SAT Word parser, so malformed source words fail closed.
-- We do not yet claim a bit-machine polynomial verifier clock or
-- a certificate bound in EVERY arbitrary accepted SAT word length.
--
-- Origins: Stephen Cook 1971; Leonid Levin 1973 (search formulation).
-- Reused DASHI owners: Cook AST, strict parser, finite witness and
-- sparse endpoint consistency Boolean algebra. No new SAT language.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥-elim)
open import Data.List.Base using (List; length)
open import Data.Maybe.Base using (just; nothing)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Nullary.Decidable.Core using (yes; no)
import Data.Nat.Properties as NatP
import Data.Nat.Base
import DASHI.Mathematics.Complexity.PNotEqualsNPCookFormulaBinaryCodecExact

import DASHI.Mathematics.Complexity.PolynomialReductionExact as PR
import DASHI.Mathematics.Complexity.FiniteWordSizeExact as Word
import DASHI.Mathematics.Complexity.CookLevinCircuitGCTBoundary as Cook
import DASHI.Mathematics.Complexity.Karp21CookFiniteOccurrenceWitnessExact as Finite
import DASHI.Mathematics.Complexity.Karp21CookStrictTripleBitBoundaryExact as Strict
import DASHI.Mathematics.Complexity.Karp21CookStrictSATLanguageExact as SAT
import DASHI.Mathematics.Complexity.Karp21BoolGoldenExact as Golden

natEqualBool : Nat → Nat → Bool
natEqualBool a b with NatP._≟_ a b
... | yes _ = true
... | no _ = false

natEqualBoolSound :
  (a b : Nat) →
  natEqualBool a b ≡ true → a ≡ b
natEqualBoolSound a b accepted with NatP._≟_ a b
... | yes equal = equal
... | no _ = Golden.falseNotTrue accepted

natEqualBoolComplete :
  (a b : Nat) →
  a ≡ b → natEqualBool a b ≡ true
natEqualBoolComplete a .a refl with NatP._≟_ a a
... | yes _ = refl
... | no impossible = ⊥-elim (impossible refl)

-- This concrete verifier reads exactly the source-owned Cook AST,
-- pairs the given bitstring with its syntactic variable occurrences,
-- rejects inconsistent repeated labels, and checks actual evaluation.
verifyCompactCookBits :
  Cook.BooleanFormula → Word.BitWord → Bool
verifyCompactCookBits formula bits =
  Golden.andBool
    (natEqualBool
      (length bits) (length (Finite.formulaVariables formula)))
    (Golden.andBool
      (Finite.allCookObservationsConsistent
        (Finite.pairObservations (Finite.formulaVariables formula) bits))
      (Cook.evaluate formula
        (Finite.recoverAssignment
          (Finite.pairObservations (Finite.formulaVariables formula) bits))))

verifyCompactCookBitsSound :
  (formula : Cook.BooleanFormula)
  (bits : Word.BitWord) →
  verifyCompactCookBits formula bits ≡ true →
  (length bits ≡ length (Finite.formulaVariables formula))
  × ((Finite.allCookObservationsConsistent
        (Finite.pairObservations (Finite.formulaVariables formula) bits)
        ≡ true)
    × (Cook.evaluate formula
         (Finite.recoverAssignment
           (Finite.pairObservations
             (Finite.formulaVariables formula) bits)) ≡ true))
verifyCompactCookBitsSound formula bits verified =
  ( natEqualBoolSound
      (length bits) (length (Finite.formulaVariables formula))
      (Golden.andLeftTrue
        (natEqualBool
          (length bits) (length (Finite.formulaVariables formula)))
        (Golden.andBool
          (Finite.allCookObservationsConsistent
            (Finite.pairObservations (Finite.formulaVariables formula) bits))
          (Cook.evaluate formula
            (Finite.recoverAssignment
              (Finite.pairObservations
                (Finite.formulaVariables formula) bits))))
        verified)
  , ( Golden.andLeftTrue
        (Finite.allCookObservationsConsistent
          (Finite.pairObservations (Finite.formulaVariables formula) bits))
        (Cook.evaluate formula
          (Finite.recoverAssignment
            (Finite.pairObservations
              (Finite.formulaVariables formula) bits)))
        (Golden.andRightTrue
          (natEqualBool
            (length bits) (length (Finite.formulaVariables formula)))
          (Golden.andBool
            (Finite.allCookObservationsConsistent
              (Finite.pairObservations (Finite.formulaVariables formula) bits))
            (Cook.evaluate formula
              (Finite.recoverAssignment
                (Finite.pairObservations
                  (Finite.formulaVariables formula) bits))))
          verified)
    , Golden.andRightTrue
        (Finite.allCookObservationsConsistent
          (Finite.pairObservations (Finite.formulaVariables formula) bits))
        (Cook.evaluate formula
          (Finite.recoverAssignment
            (Finite.pairObservations
              (Finite.formulaVariables formula) bits)))
        (Golden.andRightTrue
          (natEqualBool
            (length bits) (length (Finite.formulaVariables formula)))
          (Golden.andBool
            (Finite.allCookObservationsConsistent
              (Finite.pairObservations (Finite.formulaVariables formula) bits))
            (Cook.evaluate formula
              (Finite.recoverAssignment
                (Finite.pairObservations
                  (Finite.formulaVariables formula) bits))))
          verified)
    )
  )

verifyCompactCookBitsComplete :
  (formula : Cook.BooleanFormula)
  (bits : Word.BitWord) →
  (length bits ≡ length (Finite.formulaVariables formula))
  × ((Finite.allCookObservationsConsistent
        (Finite.pairObservations (Finite.formulaVariables formula) bits)
        ≡ true)
    × (Cook.evaluate formula
         (Finite.recoverAssignment
           (Finite.pairObservations
             (Finite.formulaVariables formula) bits)) ≡ true)) →
  verifyCompactCookBits formula bits ≡ true
verifyCompactCookBitsComplete formula bits
  (size , (consistent , accepted))
  rewrite natEqualBoolComplete
    (length bits) (length (Finite.formulaVariables formula)) size
        | consistent | accepted = refl

CompactCookVerifierYES : Cook.BooleanFormula → Set
CompactCookVerifierYES formula =
  Σ Word.BitWord (λ bits → verifyCompactCookBits formula bits ≡ true)

cookSATToExecutableCertificate :
  (formula : Cook.BooleanFormula) →
  Cook.Satisfiable formula → CompactCookVerifierYES formula
cookSATToExecutableCertificate formula sat
  with Finite.cookSatisfiableToCompact formula sat
... | bits , properties =
  bits , verifyCompactCookBitsComplete formula bits properties

cookExecutableCertificateToSAT :
  (formula : Cook.BooleanFormula) →
  CompactCookVerifierYES formula → Cook.Satisfiable formula
cookExecutableCertificateToSAT formula (bits , accepted) =
  Finite.compactToCookSatisfiable formula
    (bits , verifyCompactCookBitsSound formula bits accepted)

cookExecutableVerifierBidi :
  (formula : Cook.BooleanFormula) →
  PR.Iff (Cook.Satisfiable formula) (CompactCookVerifierYES formula)
cookExecutableVerifierBidi formula =
  PR.iff (cookSATToExecutableCertificate formula)
         (cookExecutableCertificateToSAT formula)

-- The existing canonical formula-size theorem applies to every
-- checker-accepted certificate. This is genuine witness-size evidence
-- for canonical words, without claiming a machine runtime theorem.
cookExecutableCertificateCanonicalSize :
  (formula : Cook.BooleanFormula)
  (bits : Word.BitWord) →
  verifyCompactCookBits formula bits ≡ true →
  Data.Nat.Base._≤_
    (Word.encodingSize bits)
    (Word.encodingSize
      (DASHI.Mathematics.Complexity.PNotEqualsNPCookFormulaBinaryCodecExact.encodeFormulaBits formula))
cookExecutableCertificateCanonicalSize formula bits accepted =
  Finite.compactCookWitnessAtMostCanonicalFormulaWord formula
    (bits , verifyCompactCookBitsSound formula bits accepted)

------------------------------------------------------------------------
-- BIDI on the ACTUAL strict SAT language, not an alternate decoder.
------------------------------------------------------------------------

verifyStrictCookSATWord :
  Word.BitWord → Word.BitWord → Bool
verifyStrictCookSATWord word bits
  with Strict.strictDecodeCookFormulaBits word
... | nothing = false
... | just formula = verifyCompactCookBits formula bits

StrictCookExecutableVerifierYES : Word.BitWord → Set
StrictCookExecutableVerifierYES word =
  Σ Word.BitWord
    (λ bits → verifyStrictCookSATWord word bits ≡ true)

strictCookExecutableVerifierSound :
  (word : Word.BitWord) →
  StrictCookExecutableVerifierYES word →
  PR.accepts SAT.strictSATLanguage word
strictCookExecutableVerifierSound word (bits , verified)
  with Strict.strictDecodeCookFormulaBits word
... | nothing = ⊥-elim (Golden.falseNotTrue verified)
... | just formula =
  cookExecutableCertificateToSAT formula (bits , verified)

strictCookExecutableVerifierComplete :
  (word : Word.BitWord) →
  PR.accepts SAT.strictSATLanguage word →
  StrictCookExecutableVerifierYES word
strictCookExecutableVerifierComplete word accepted
  with Strict.strictDecodeCookFormulaBits word
... | nothing = ⊥-elim accepted
... | just formula =
  cookSATToExecutableCertificate formula accepted

strictCookExecutableVerifierBidi :
  (word : Word.BitWord) →
  PR.Iff (PR.accepts SAT.strictSATLanguage word)
    (StrictCookExecutableVerifierYES word)
strictCookExecutableVerifierBidi word =
  PR.iff (strictCookExecutableVerifierComplete word)
         (strictCookExecutableVerifierSound word)

------------------------------------------------------------------------
-- Explicit encoded-word BIDI triangle. The formula encoder, strict
-- parser and Boolean certificate verifier act on the SAME Cook object.
-- This pays the canonical-word length comparison without asserting
-- arbitrary-input canonical re-encoding or an actual tape clock.
------------------------------------------------------------------------

strictCanonicalCookVerifierBidi :
  (formula : Cook.BooleanFormula) →
  PR.Iff (Cook.Satisfiable formula)
    (StrictCookExecutableVerifierYES
      (DASHI.Mathematics.Complexity.PNotEqualsNPCookFormulaBinaryCodecExact.encodeFormulaBits formula))
strictCanonicalCookVerifierBidi formula
  rewrite Strict.strictCookFormulaRoundTrip formula =
  cookExecutableVerifierBidi formula

strictCanonicalCookCertificateBound :
  (formula : Cook.BooleanFormula)
  (bits : Word.BitWord) →
  verifyStrictCookSATWord
    (DASHI.Mathematics.Complexity.PNotEqualsNPCookFormulaBinaryCodecExact.encodeFormulaBits formula)
    bits ≡ true →
  Data.Nat.Base._≤_
    (Word.encodingSize bits)
    (Word.encodingSize
      (DASHI.Mathematics.Complexity.PNotEqualsNPCookFormulaBinaryCodecExact.encodeFormulaBits formula))
strictCanonicalCookCertificateBound formula bits checked
  rewrite Strict.strictCookFormulaRoundTrip formula =
  cookExecutableCertificateCanonicalSize formula bits checked
