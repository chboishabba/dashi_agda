module DASHI.Analysis.CollatzSyracuseUniformWordDescentCertificateExact where

------------------------------------------------------------------------
-- GENERIC UNIFORM DESCENT CERTIFICATE FOR ONE LITERAL PARITY CYLINDER
--
-- For a fixed parity word w of length m, the exact affine iterate is
--
--   2^m T^m(x) = 3^(ones w) x + A(w).
--
-- A reusable cylinder certificate consists of a natural gap g and threshold N
-- with
--
--   2^m = 3^(ones w) + g
--   A(w) < g N.
--
-- Every literal Syracuse start x >= N whose actual parity word is w then
-- strictly descends after m shortcut steps.  This is a same-object theorem:
-- the word match is an equality with the actual orbit observer, not a sampled
-- or independent Bernoulli word.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl; cong)
open import Agda.Builtin.Nat using (Nat; _+_; _*_)
open import Data.Nat using (_≤_; _<_)
import Data.Nat.Properties as NatP
open import Data.Nat.Solver using (module +-*-Solver)
open +-*-Solver using (solve; _:+_; _:*_; _:=_)
open import Relation.Binary.PropositionalEquality using (subst; sym; trans)

import DASHI.Core.BinaryBranchOutcomeEnumerationExact as Binary
import DASHI.NumberTheory.Collatz.SyracuseExact as Syracuse
import DASHI.NumberTheory.Collatz.SyracuseParityItineraryExact as Itinerary
import DASHI.NumberTheory.Collatz.SyracuseAffineIterateExact as Affine
import DASHI.NumberTheory.Collatz.SyracuseAffineDescentMarginExact as Margin

record UniformWordDescentCertificate
    {m : Nat}
    (word : Binary.BinaryWord m) : Set where
  field
    gap : Nat
    minimumStart : Nat

    denominatorSplit :
      Affine.powNat 2 m
      ≡ Affine.powNat 3 (Affine.parityCount word) + gap

    correctionBelowGapAtMinimum :
      Affine.affineAdditiveTerm word
      < gap * minimumStart

open UniformWordDescentCertificate public

correctionBelowGapAtStart :
  {m : Nat} →
  (word : Binary.BinaryWord m) →
  (certificate : UniformWordDescentCertificate word) →
  (x : Syracuse.PositiveNat) →
  minimumStart certificate ≤ Syracuse.toNat x →
  Affine.affineAdditiveTerm word
  < gap certificate * Syracuse.toNat x
correctionBelowGapAtStart word certificate x lower =
  NatP.<-≤-trans
    (correctionBelowGapAtMinimum certificate)
    (NatP.*-monoʳ-≤ (gap certificate) lower)

sumGapNormalize :
  (p g x : Nat) →
  p * x + g * x ≡ (p + g) * x
sumGapNormalize =
  solve 3
    (λ p g x →
      (p :* x) :+ (g :* x)
      :=
      (p :+ g) :* x)
    refl

uniformWordCertificateImpliesAffineMargin :
  {m : Nat} →
  (word : Binary.BinaryWord m) →
  (certificate : UniformWordDescentCertificate word) →
  (x : Syracuse.PositiveNat) →
  minimumStart certificate ≤ Syracuse.toNat x →
  Itinerary.parityWord m x ≡ word →
  Margin.literalAffineNumerator m x
  < Affine.powNat 2 m * Syracuse.toNat x
uniformWordCertificateImpliesAffineMargin
  {m} word certificate x lower wordMatch
  rewrite wordMatch =
  let
    p = Affine.powNat 3 (Affine.parityCount word)
    g = gap certificate
    value = Syracuse.toNat x

    correctionFits :
      Affine.affineAdditiveTerm word < g * value
    correctionFits =
      correctionBelowGapAtStart word certificate x lower

    shifted :
      p * value + Affine.affineAdditiveTerm word
      < p * value + g * value
    shifted =
      NatP.+-monoˡ-< (p * value) correctionFits

    combined :
      p * value + g * value ≡ (p + g) * value
    combined = sumGapNormalize p g value

    splitAtValue :
      (p + g) * value ≡ Affine.powNat 2 m * value
    splitAtValue =
      cong (_* value) (sym (denominatorSplit certificate))
  in
  subst
    (λ right →
      p * value + Affine.affineAdditiveTerm word < right)
    splitAtValue
    (subst
      (λ right →
        p * value + Affine.affineAdditiveTerm word < right)
      combined
      shifted)

uniformWordCertificateImpliesDescent :
  {m : Nat} →
  (word : Binary.BinaryWord m) →
  (certificate : UniformWordDescentCertificate word) →
  (x : Syracuse.PositiveNat) →
  minimumStart certificate ≤ Syracuse.toNat x →
  Itinerary.parityWord m x ≡ word →
  Syracuse.toNat (Syracuse.syracuseIterate m x)
  < Syracuse.toNat x
uniformWordCertificateImpliesDescent
  {m} word certificate x lower wordMatch =
  Margin.strictAffineMarginImpliesDescent
    m x
    (uniformWordCertificateImpliesAffineMargin
      word certificate x lower wordMatch)

record UniformWordDescentCertificateBoundary : Set where
  constructor uniformWordDescentCertificateBoundary
  field
    exactAffineWordCertificatePaid : Nat
    literalParityMatchRequired : Nat
    uniformThresholdCompilerPaid : Nat
    finiteSearchMayProduceCertificates : Nat
    certificateCollectionAutomaticallyCoversAllStarts : Nat
    universalStoppingPromotedFromOneCertificate : Nat

canonicalUniformWordDescentCertificateBoundary :
  UniformWordDescentCertificateBoundary
canonicalUniformWordDescentCertificateBoundary =
  uniformWordDescentCertificateBoundary 1 1 1 1 0 0
