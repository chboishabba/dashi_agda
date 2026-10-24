module DASHI.Biology.IITF81F9NormInverseBridgeExact where

open import DASHI.Core.Prelude
open import Relation.Binary.PropositionalEquality using (sym; trans)

import DASHI.Analysis.RiemannQuarticTriadicCodecKernelBridgeExact as Kernel4
import DASHI.Biology.IITProjectiveF9Pointed80Exact as Projective
import DASHI.Biology.IITJFineSelectedCrossPunctured79Exact as JFine
import DASHI.Moonshine.OggSSPP3F9FrobeniusCandidateNoGoExact as F9

------------------------------------------------------------------------
-- Concrete SAME ORIGINAL CARRIER; conditional algebraic field certificate.
--
-- The source of the underlying 80-element unit set is literally
-- Kernel4.PuncturedKernel4; the nine+infinity chart is literally
-- Projective.ProjectiveF9Chart.  NOT an unnamed 80-element toy.
--
-- The selected multiplication is F3[X]/(X^4+X+2), with the independently
-- checked explicit F9 tower basis
-- gamma=(0,1,2,2), beta=(0,0,1,1):
--   gamma²=-1; beta²=1+gamma.
-- The numerical script checked ALL 81^2 additions and multiplications,
-- plus 81 Frobenius and norm equalities. This file does NOT pretend
-- those finite computation receipts are Agda kernel proofs.
------------------------------------------------------------------------

record PuncturedF81PowerLaws : Set₁ where
  field
    multiplyUnit :
      Kernel4.PuncturedKernel4 →
      Kernel4.PuncturedKernel4 →
      Kernel4.PuncturedKernel4
    identityUnit : Kernel4.PuncturedKernel4

    power9 power10 power79 power80 :
      Kernel4.PuncturedKernel4 → Kernel4.PuncturedKernel4

    power10Successor :
      (a : Kernel4.PuncturedKernel4) →
      multiplyUnit a (power9 a) ≡ power10 a

    power80Successor :
      (a : Kernel4.PuncturedKernel4) →
      multiplyUnit a (power79 a) ≡ power80 a

    fermat80 :
      (a : Kernel4.PuncturedKernel4) →
      power80 a ≡ identityUnit

    multiplyLeftCancellation :
      (a b c : Kernel4.PuncturedKernel4) →
      multiplyUnit a b ≡ multiplyUnit a c →
      b ≡ c

    power8 : Kernel4.PuncturedKernel4 → Kernel4.PuncturedKernel4

    normOneOnImage8 :
      (a : Kernel4.PuncturedKernel4) →
      power10 (power8 a) ≡ identityUnit

open PuncturedF81PowerLaws public

-- 79 = |F81×|-1 = 3^4-2; we use a *power law* rather than pretending
-- the integer 81 itself is invertible in characteristic 3.

inverseExponent79 :
  (laws : PuncturedF81PowerLaws)
  (a : Kernel4.PuncturedKernel4) →
  multiplyUnit laws a (power79 laws a) ≡ identityUnit laws
inverseExponent79 laws a =
  trans (power80Successor laws a) (fermat80 laws a)

relativeFrobeniusEqualsInverseOnNormOne :
  (laws : PuncturedF81PowerLaws)
  (a : Kernel4.PuncturedKernel4) →
  power10 laws a ≡ identityUnit laws →
  power9 laws a ≡ power79 laws a
relativeFrobeniusEqualsInverseOnNormOne laws a normOne =
  multiplyLeftCancellation laws a
    (power9 laws a)
    (power79 laws a)
    (trans
      (power10Successor laws a)
      (trans normOne (sym (inverseExponent79 laws a))))

projectiveExponent8HasFrobeniusInverse :
  (laws : PuncturedF81PowerLaws)
  (a : Kernel4.PuncturedKernel4) →
  power9 laws (power8 laws a) ≡ power79 laws (power8 laws a)
projectiveExponent8HasFrobeniusInverse laws a =
  relativeFrobeniusEqualsInverseOnNormOne
    laws (power8 laws a) (normOneOnImage8 laws a)

------------------------------------------------------------------------
-- Projectivisation has an EXPLICIT admission record using the actual
-- source P1(F9) chart and the actual 80-element punctured Kernel4.
-- A section trivialisation is a chosen chart, unlike the canonical
-- F81× / F9× quotient at the level of abstract group actions.
------------------------------------------------------------------------

record SourceProjectiveNormOneWeld
    (laws : PuncturedF81PowerLaws) : Set₁ where
  field
    originalPunctured80Chart :
      Projective.Projective80Trivialisation

    projectiveClassAsNormOne :
      Projective.ProjectiveF9Chart →
      Kernel4.PuncturedKernel4

    normOneSection :
      (point : Projective.ProjectiveF9Chart) →
      power10 laws (projectiveClassAsNormOne point)
      ≡ identityUnit laws

    originalF9CoordinatesReused : F9.F9Point → Projective.ProjectiveF9Chart
    originalF9CoordinatesReusedPointwise :
      (coordinate : F9.F9Point) →
      originalF9CoordinatesReused coordinate ≡ Projective.affine coordinate

open SourceProjectiveNormOneWeld public

normOneProjectivePointFrobeniusIsInverse :
  (laws : PuncturedF81PowerLaws)
  (weld : SourceProjectiveNormOneWeld laws)
  (point : Projective.ProjectiveF9Chart) →
  power9 laws (projectiveClassAsNormOne weld point)
  ≡ power79 laws (projectiveClassAsNormOne weld point)
normOneProjectivePointFrobeniusIsInverse laws weld point =
  relativeFrobeniusEqualsInverseOnNormOne
    laws
    (projectiveClassAsNormOne weld point)
    (normOneSection weld point)

field81Order : 3 * 3 * 3 * 3 ≡ 81
field81Order = refl

unitGroupOrder : 81 ≡ 80 + 1
unitGroupOrder = refl

inverseExponentGap : 81 ≡ 79 + 2
inverseExponentGap = refl

ternaryPredecessorGap : 3 ≡ 2 + 1
ternaryPredecessorGap = refl

inverseAsMinusOneModulo80 : 79 + 1 ≡ 80
inverseAsMinusOneModulo80 = refl

normAndFrobeniusExponents : 9 + 1 ≡ 10
normAndFrobeniusExponents = refl

projectiveQuotientOrder : 8 * 10 ≡ 80
projectiveQuotientOrder = refl

affineAndInfinityFibres : 9 * 8 + 8 ≡ 80
affineAndInfinityFibres = refl

------------------------------------------------------------------------
-- Authority:
-- above are *conditional* algebraic consequences on exact source types.
-- To inhabit PuncturedF81PowerLaws and SourceProjectiveNormOneWeld
-- in the kernel requires literal polynomial/finite-field computations.
-- Local independent exhaustive arithmetic is a separate receipt.
-- Original Ogg F9 source has a formal Frobenius, NOT a confirmed
-- external marked supersingular moduli identifier.
------------------------------------------------------------------------

record F81F9NormInverseBoundary : Set where
  constructor f81-f9-norm-inverse-boundary
  field
    qMinusTwoInverseTheoremDerived : Bool
    relativeFrobeniusOnNormOneDerived : Bool
    actualSourcePuncturedAndF9ChartReferenced : Bool
    concreteKernelPolynomialMultiplicationPaid : Bool
    concreteKernelProjective80TrivialisationPaid : Bool
    local81SquaredOperationPairsChecked : Bool
    originalSSP79Claimed : Bool
    externalMonsterOrConsciousnessIdentityClaimed : Bool

canonicalF81F9NormInverseBoundary : F81F9NormInverseBoundary
canonicalF81F9NormInverseBoundary =
  f81-f9-norm-inverse-boundary true true true false false true false false
