module DASHI.Analysis.CollatzSyracuseTrailingZeroCertificateExact where

------------------------------------------------------------------------
-- TRAILING-EVEN EXTENSION OF UNIFORM AFFINE DESCENT CERTIFICATES
--
-- If a literal parity word w of length m has
--
--   2^m = 3^(ones w) + g
--   A(w) < g N,
--
-- then appending a final even step preserves both the odd count and the
-- affine correction A, while the denominator doubles.  Hence w0 has a new
-- positive gap and the SAME minimum start N.  Iterating gives w0^r.
--
-- This is useful for residual-cylinder search because one proved word pays an
-- entire trailing-zero family.  It does not create coverage of all residual
-- starts and therefore does not promote finite search to universal stopping.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl; cong)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Data.Nat using (_≤_; _<_)
import Data.Nat.Properties as NatP
open import Data.Nat.Solver using (module +-*-Solver)
open +-*-Solver using (solve; _:+_; _:*_; con; _:=_)
open import Relation.Binary.PropositionalEquality using (subst)

import DASHI.Core.BinaryBranchOutcomeEnumerationExact as Binary
import DASHI.NumberTheory.Collatz.SyracuseAffineIterateExact as Affine
import DASHI.Analysis.CollatzSyracuseUniformWordDescentCertificateExact as Cert

------------------------------------------------------------------------
-- Append a LATE even step to the indexed word.  Constructors encode the
-- earliest step outermost, so appending traverses to the terminal `end`.
------------------------------------------------------------------------

appendZero :
  {m : Nat} →
  Binary.BinaryWord m →
  Binary.BinaryWord (suc m)
appendZero Binary.end = Binary.bit0 Binary.end
appendZero (Binary.bit0 tail) = Binary.bit0 (appendZero tail)
appendZero (Binary.bit1 tail) = Binary.bit1 (appendZero tail)

parityCountAppendZero :
  {m : Nat} →
  (word : Binary.BinaryWord m) →
  Affine.parityCount (appendZero word) ≡ Affine.parityCount word
parityCountAppendZero Binary.end = refl
parityCountAppendZero (Binary.bit0 tail) = parityCountAppendZero tail
parityCountAppendZero (Binary.bit1 tail) =
  cong suc (parityCountAppendZero tail)

affineTermAppendZero :
  {m : Nat} →
  (word : Binary.BinaryWord m) →
  Affine.affineAdditiveTerm (appendZero word)
  ≡ Affine.affineAdditiveTerm word
affineTermAppendZero Binary.end = refl
affineTermAppendZero (Binary.bit0 tail)
  rewrite affineTermAppendZero tail = refl
affineTermAppendZero (Binary.bit1 tail)
  rewrite parityCountAppendZero tail | affineTermAppendZero tail = refl

------------------------------------------------------------------------
-- One trailing zero.
------------------------------------------------------------------------

extendedGap :
  {m : Nat} →
  (word : Binary.BinaryWord m) →
  Cert.UniformWordDescentCertificate word →
  Nat
extendedGap word certificate =
  Cert.gap certificate
  +
  (Affine.powNat 3 (Affine.parityCount word) + Cert.gap certificate)

doubleSplitNormalize :
  (p g : Nat) →
  2 * (p + g) ≡ p + (g + (p + g))
doubleSplitNormalize =
  solve 2
    (λ p g →
      con 2 :* (p :+ g)
      :=
      p :+ (g :+ (p :+ g)))
    refl

trailingZeroDenominatorSplit :
  {m : Nat} →
  (word : Binary.BinaryWord m) →
  (certificate : Cert.UniformWordDescentCertificate word) →
  Affine.powNat 2 (suc m)
  ≡
  Affine.powNat 3 (Affine.parityCount (appendZero word))
  + extendedGap word certificate
trailingZeroDenominatorSplit {m} word certificate
  rewrite parityCountAppendZero word
        | Cert.denominatorSplit certificate =
  doubleSplitNormalize
    (Affine.powNat 3 (Affine.parityCount word))
    (Cert.gap certificate)

trailingZeroCorrectionFits :
  {m : Nat} →
  (word : Binary.BinaryWord m) →
  (certificate : Cert.UniformWordDescentCertificate word) →
  Affine.affineAdditiveTerm (appendZero word)
  < extendedGap word certificate * Cert.minimumStart certificate
trailingZeroCorrectionFits word certificate
  rewrite affineTermAppendZero word =
  let
    g = Cert.gap certificate
    p = Affine.powNat 3 (Affine.parityCount word)
    minimum = Cert.minimumStart certificate

    gapLeExtended : g ≤ g + (p + g)
    gapLeExtended = NatP.m≤m+n g (p + g)

    scaled : g * minimum ≤ (g + (p + g)) * minimum
    scaled = NatP.*-monoˡ-≤ minimum gapLeExtended
  in
  NatP.<-≤-trans
    (Cert.correctionBelowGapAtMinimum certificate)
    scaled

appendZeroCertificate :
  {m : Nat} →
  (word : Binary.BinaryWord m) →
  Cert.UniformWordDescentCertificate word →
  Cert.UniformWordDescentCertificate (appendZero word)
appendZeroCertificate word certificate = record
  { Cert.gap = extendedGap word certificate
  ; Cert.minimumStart = Cert.minimumStart certificate
  ; Cert.denominatorSplit = trailingZeroDenominatorSplit word certificate
  ; Cert.correctionBelowGapAtMinimum =
      trailingZeroCorrectionFits word certificate
  }

------------------------------------------------------------------------
-- Arbitrarily many trailing zeroes.
------------------------------------------------------------------------

appendZeros :
  (r : Nat) →
  {m : Nat} →
  Binary.BinaryWord m →
  Binary.BinaryWord (r + m)
appendZeros zero word = word
appendZeros (suc r) word = appendZero (appendZeros r word)

appendZerosCertificate :
  (r : Nat) →
  {m : Nat} →
  (word : Binary.BinaryWord m) →
  Cert.UniformWordDescentCertificate word →
  Cert.UniformWordDescentCertificate (appendZeros r word)
appendZerosCertificate zero word certificate = certificate
appendZerosCertificate (suc r) word certificate =
  appendZeroCertificate
    (appendZeros r word)
    (appendZerosCertificate r word certificate)

appendZerosPreservesMinimumStart :
  (r : Nat) →
  {m : Nat} →
  (word : Binary.BinaryWord m) →
  (certificate : Cert.UniformWordDescentCertificate word) →
  Cert.minimumStart (appendZerosCertificate r word certificate)
  ≡ Cert.minimumStart certificate
appendZerosPreservesMinimumStart zero word certificate = refl
appendZerosPreservesMinimumStart (suc r) word certificate =
  appendZerosPreservesMinimumStart r word certificate

record TrailingZeroCertificateBoundary : Set where
  constructor trailingZeroCertificateBoundary
  field
    parityCountPreserved : Nat
    affineCorrectionPreserved : Nat
    minimumStartPreserved : Nat
    oneTrailingZeroCompilerPaid : Nat
    arbitraryTrailingZerosCompilerPaid : Nat
    finiteSearchCompressionPaid : Nat
    trailingZeroCompilerCreatesResidualCoverage : Nat
    trailingZeroCompilerCreatesUniversalStopping : Nat

canonicalTrailingZeroCertificateBoundary : TrailingZeroCertificateBoundary
canonicalTrailingZeroCertificateBoundary =
  trailingZeroCertificateBoundary 1 1 1 1 1 1 0 0
