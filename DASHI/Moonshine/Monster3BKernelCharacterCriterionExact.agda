module DASHI.Moonshine.Monster3BKernelCharacterCriterionExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- I. M. Isaacs,
-- "Character Theory of Finite Groups",
-- Dover Publications, 1994 reprint of the 1976 edition.
-- ISBN: 978-0-486-68014-9; no DOI assigned.
--
-- R. W. Barraclough and R. A. Wilson,
-- "The Character Table of a Maximal Subgroup of the Monster",
-- LMS Journal of Computation and Mathematics 10 (2007), 161--175.
-- DOI: 10.1112/S1461157000001352.
--
-- DASHI CONTRIBUTION
--
-- State the full class-character signature needed to promote the concrete
-- 729 x 90 model to the actual zeta sector.  The cyclotomic trace is retained
-- coefficientwise in the basis 1,zeta,zeta^2, so no complex-number equality is
-- hidden inside a natural-number trace.  This upgraded owner also proves the
-- complete extraspecial degree-square budget and the nonlinear character norm
-- numerator 3 * 729^2 = 3^13.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_; _*_)

import DASHI.Moonshine.Monster3BHeisenbergMultiplicityExact as H

data ExtraspecialClassKind : Set where
  identityClass : ExtraspecialClassKind
  centralZetaClass : ExtraspecialClassKind
  centralZetaSquaredClass : ExtraspecialClassKind
  noncentralClass : ExtraspecialClassKind

record CyclotomicTrace3 : Set where
  constructor cyclotomic-trace3
  field
    coefficientOne : Nat
    coefficientZeta : Nat
    coefficientZetaSquared : Nat

open CyclotomicTrace3 public

zeroTrace : CyclotomicTrace3
zeroTrace = cyclotomic-trace3 0 0 0

scaleTrace : Nat → CyclotomicTrace3 → CyclotomicTrace3
scaleTrace scale (cyclotomic-trace3 c0 c1 c2) =
  cyclotomic-trace3
    (scale * c0)
    (scale * c1)
    (scale * c2)

heisenbergKernelTrace : ExtraspecialClassKind → CyclotomicTrace3
heisenbergKernelTrace identityClass = cyclotomic-trace3 729 0 0
heisenbergKernelTrace centralZetaClass = cyclotomic-trace3 0 729 0
heisenbergKernelTrace centralZetaSquaredClass = cyclotomic-trace3 0 0 729
heisenbergKernelTrace noncentralClass = zeroTrace

conjugateHeisenbergKernelTrace : ExtraspecialClassKind → CyclotomicTrace3
conjugateHeisenbergKernelTrace identityClass = cyclotomic-trace3 729 0 0
conjugateHeisenbergKernelTrace centralZetaClass = cyclotomic-trace3 0 0 729
conjugateHeisenbergKernelTrace centralZetaSquaredClass = cyclotomic-trace3 0 729 0
conjugateHeisenbergKernelTrace noncentralClass = zeroTrace

------------------------------------------------------------------------
-- Complete extraspecial character-degree arithmetic.
------------------------------------------------------------------------

heisenbergDegree : Nat
heisenbergDegree = H.threePowerSix

linearCharacterCount : Nat
linearCharacterCount = H.symplecticQuotientOrder

nonlinearCharacterCount : Nat
nonlinearCharacterCount = 2

extraspecialOrder : Nat
extraspecialOrder = H.extraspecialOrder

nonlinearDegreeSquare : Nat
nonlinearDegreeSquare = heisenbergDegree * heisenbergDegree

extraspecialCharacterDegreeSquareSum : Nat
extraspecialCharacterDegreeSquareSum =
  linearCharacterCount
  + nonlinearCharacterCount * nonlinearDegreeSquare

extraspecialCharacterDegreeSquareSumIsOrder :
  extraspecialCharacterDegreeSquareSum ≡ extraspecialOrder
extraspecialCharacterDegreeSquareSumIsOrder = refl

heisenbergNormNumerator : Nat
heisenbergNormNumerator = 3 * nonlinearDegreeSquare

heisenbergNormNumeratorIsExtraspecialOrder :
  heisenbergNormNumerator ≡ extraspecialOrder
heisenbergNormNumeratorIsExtraspecialOrder = refl

------------------------------------------------------------------------
-- Ninety-fold model signature.
------------------------------------------------------------------------

ninetyFoldModelKernelTrace : ExtraspecialClassKind → CyclotomicTrace3
ninetyFoldModelKernelTrace kind =
  scaleTrace 90 (heisenbergKernelTrace kind)

ninetyFoldConjugateKernelTrace : ExtraspecialClassKind → CyclotomicTrace3
ninetyFoldConjugateKernelTrace kind =
  scaleTrace 90 (conjugateHeisenbergKernelTrace kind)

modelIdentityTraceIs65610 :
  coefficientOne (ninetyFoldModelKernelTrace identityClass) ≡ 65610
modelIdentityTraceIs65610 = refl

modelCentralZetaTraceAmplitudeIs65610 :
  coefficientZeta (ninetyFoldModelKernelTrace centralZetaClass) ≡ 65610
modelCentralZetaTraceAmplitudeIs65610 = refl

modelCentralZetaSquaredTraceAmplitudeIs65610 :
  coefficientZetaSquared
    (ninetyFoldModelKernelTrace centralZetaSquaredClass) ≡ 65610
modelCentralZetaSquaredTraceAmplitudeIs65610 = refl

modelNoncentralTraceIsZero :
  ninetyFoldModelKernelTrace noncentralClass ≡ zeroTrace
modelNoncentralTraceIsZero = refl

modelConjugateNoncentralTraceIsZero :
  ninetyFoldConjugateKernelTrace noncentralClass ≡ zeroTrace
modelConjugateNoncentralTraceIsZero = refl

modelTraceIsNinetyHeisenbergCopies :
  (kind : ExtraspecialClassKind) →
  ninetyFoldModelKernelTrace kind
  ≡ scaleTrace H.multiplicityDegree (heisenbergKernelTrace kind)
modelTraceIsNinetyHeisenbergCopies identityClass = refl
modelTraceIsNinetyHeisenbergCopies centralZetaClass = refl
modelTraceIsNinetyHeisenbergCopies centralZetaSquaredClass = refl
modelTraceIsNinetyHeisenbergCopies noncentralClass = refl

------------------------------------------------------------------------
-- Actual class coverage and immediate consequences.
------------------------------------------------------------------------

record ActualKernelCharacterCertificate (ActualClass : Set) : Set where
  constructor actual-kernel-character-certificate
  field
    classify : ActualClass → ExtraspecialClassKind
    actualTrace : ActualClass → CyclotomicTrace3
    traceMatchesNinetyFoldModel :
      (class : ActualClass) →
      actualTrace class ≡ ninetyFoldModelKernelTrace (classify class)

open ActualKernelCharacterCertificate public

actualKernelCharacterIdentity :
  ∀ {ActualClass} →
  (certificate : ActualKernelCharacterCertificate ActualClass) →
  (class : ActualClass) →
  actualTrace certificate class
  ≡ ninetyFoldModelKernelTrace (classify certificate class)
actualKernelCharacterIdentity = traceMatchesNinetyFoldModel

actualNoncentralTraceVanishes :
  ∀ {ActualClass} →
  (certificate : ActualKernelCharacterCertificate ActualClass) →
  (class : ActualClass) →
  classify certificate class ≡ noncentralClass →
  actualTrace certificate class ≡ zeroTrace
actualNoncentralTraceVanishes certificate class classifies
  rewrite traceMatchesNinetyFoldModel certificate class
        | classifies = refl

actualCentralZetaTraceAmplitude :
  ∀ {ActualClass} →
  (certificate : ActualKernelCharacterCertificate ActualClass) →
  (class : ActualClass) →
  classify certificate class ≡ centralZetaClass →
  coefficientZeta (actualTrace certificate class) ≡ 65610
actualCentralZetaTraceAmplitude certificate class classifies
  rewrite traceMatchesNinetyFoldModel certificate class
        | classifies = refl

actualIdentityTraceAmplitude :
  ∀ {ActualClass} →
  (certificate : ActualKernelCharacterCertificate ActualClass) →
  (class : ActualClass) →
  classify certificate class ≡ identityClass →
  coefficientOne (actualTrace certificate class) ≡ 65610
actualIdentityTraceAmplitude certificate class classifies
  rewrite traceMatchesNinetyFoldModel certificate class
        | classifies = refl

record KernelCharacterPromotionBoundary : Set where
  constructor kernel-character-promotion-boundary
  field
    modelIdentityAmplitude :
      coefficientOne (ninetyFoldModelKernelTrace identityClass) ≡ 65610
    modelCentralAmplitude :
      coefficientZeta (ninetyFoldModelKernelTrace centralZetaClass) ≡ 65610
    modelNoncentralVanishing :
      ninetyFoldModelKernelTrace noncentralClass ≡ zeroTrace
    degreeSquareBudgetCloses :
      extraspecialCharacterDegreeSquareSum ≡ extraspecialOrder
    nonlinearCharacterNormCloses :
      heisenbergNormNumerator ≡ extraspecialOrder
    actualMN3BClassCoverageCertified : Bool
    actualMN3BClassCoverageCertifiedIsFalse :
      actualMN3BClassCoverageCertified ≡ false
    actualKernelCharacterCertificateConstructed : Bool
    actualKernelCharacterCertificateConstructedIsFalse :
      actualKernelCharacterCertificateConstructed ≡ false
    actualCharacterEqualityPromotedToIntertwiner : Bool
    actualCharacterEqualityPromotedToIntertwinerIsFalse :
      actualCharacterEqualityPromotedToIntertwiner ≡ false

canonicalKernelCharacterPromotionBoundary :
  KernelCharacterPromotionBoundary
canonicalKernelCharacterPromotionBoundary =
  kernel-character-promotion-boundary
    modelIdentityTraceIs65610
    modelCentralZetaTraceAmplitudeIs65610
    modelNoncentralTraceIsZero
    extraspecialCharacterDegreeSquareSumIsOrder
    heisenbergNormNumeratorIsExtraspecialOrder
    false refl
    false refl
    false refl
