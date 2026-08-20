module DASHI.Physics.Closure.NSTriadKNDeviatoricPressureAlignmentEnableRound78Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: Dhawal Buaria; Alain Pumir.
-- Title: "Role of pressure in generation of intense velocity gradients in
-- turbulent flows".
-- DOI: 10.48550/arXiv.2308.03902.
--
-- ROUND78 / DEVIATORIC PRESSURE ALIGNMENT ENDPOINT
--
-- If vorticity is exactly aligned with an eigenvector of the deviatoric
-- pressure Hessian H^D with eigenvalue lambda, then
--
--   omega^T H^D omega = lambda |omega|^2 = lambda Omega.
--
-- For ordered trace-free eigenvalues lambda1>=lambda2>=lambda3, the smallest
-- eigenvalue is automatically nonpositive: 3 lambda3 <= sum_i lambda_i = 0.
-- Hence exact alignment with e3 and Omega>=0 makes the deviatoric contraction
-- nonpositive.  Since the stretching-acceleration equation contains
-- -omega^T H omega, its negation is a nonnegative enabling channel.
--
-- Buaria--Pumir observe near-alignment with the smallest pressure-Hessian
-- eigenvector in intense-vorticity DNS.  That observation motivates the branch
-- but is not used as a pointwise premise here.  The selected-event PDE theorem
-- must quantify imperfect alignment and the competition with isotropic and
-- other depletion.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
import Data.Integer.Base as Int
open import Data.Rational.Base using
  (ℚ; 0ℚ; _/_; _+_; _*_; -_; _≤_; _<_; nonNegative; positive)
import Data.Rational.Properties as ℚP
open ℚP using (_<?_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst; sym)
open import Relation.Nullary.Decidable.Core using (toWitness)

three : ℚ
three = Int.+ 3 / 1

threePositive : 0ℚ < three
threePositive = toWitness {a? = 0ℚ <? three} _

record OrderedTraceFreeDeviatoricSpectrum : Set where
  constructor ordered-trace-free-deviatoric-spectrum
  field
    lambda1 lambda2 lambda3 : ℚ
    lambda2BelowLambda1 : lambda2 ≤ lambda1
    lambda3BelowLambda2 : lambda3 ≤ lambda2
    traceFree : (lambda1 + lambda2) + lambda3 ≡ 0ℚ

open OrderedTraceFreeDeviatoricSpectrum public

smallestDeviatoricEigenvalueNonpositive :
  ∀ spectrum → lambda3 spectrum ≤ 0ℚ
smallestDeviatoricEigenvalueNonpositive spectrum =
  let
    l1 = lambda1 spectrum
    l2 = lambda2 spectrum
    l3 = lambda3 spectrum

    l3BelowL1 : l3 ≤ l1
    l3BelowL1 =
      ℚP.≤-trans
        (lambda3BelowLambda2 spectrum)
        (lambda2BelowLambda1 spectrum)

    twoTerms : l3 + l3 ≤ l1 + l2
    twoTerms =
      ℚP.+-mono-≤ l3BelowL1 (lambda3BelowLambda2 spectrum)

    threeTerms : (l3 + l3) + l3 ≤ (l1 + l2) + l3
    threeTerms = ℚP.+-mono-≤ twoTerms ℚP.≤-refl

    belowZero : (l3 + l3) + l3 ≤ 0ℚ
    belowZero =
      subst
        (λ right → (l3 + l3) + l3 ≤ right)
        (traceFree spectrum)
        threeTerms

    leftMeaning : (l3 + l3) + l3 ≡ three * l3
    leftMeaning = solve (l3 ∷ [])

    threeTimesBelowZero : three * l3 ≤ 0ℚ
    threeTimesBelowZero =
      subst (λ left → left ≤ 0ℚ) leftMeaning belowZero

    threeZeroMeaning : three * 0ℚ ≡ 0ℚ
    threeZeroMeaning = solve []

    scaled : three * l3 ≤ three * 0ℚ
    scaled =
      subst
        (λ right → three * l3 ≤ right)
        (sym threeZeroMeaning)
        threeTimesBelowZero

    instance threeIsPositive = positive threePositive
  in
  ℚP.*-cancelˡ-≤-pos three scaled

alignedDeviatoricContraction : ℚ → ℚ → ℚ
alignedDeviatoricContraction eigenvalue enstrophy = eigenvalue * enstrophy

alignedNonpositiveEigenvalueGivesNonpositiveContraction :
  ∀ eigenvalue enstrophy →
  eigenvalue ≤ 0ℚ →
  0ℚ ≤ enstrophy →
  alignedDeviatoricContraction eigenvalue enstrophy ≤ 0ℚ
alignedNonpositiveEigenvalueGivesNonpositiveContraction
    eigenvalue enstrophy eigenvalue≤0 enstrophyNN =
  let
    instance enstrophyNonnegative = nonNegative enstrophyNN
    raw : eigenvalue * enstrophy ≤ 0ℚ * enstrophy
    raw = ℚP.*-monoʳ-≤-nonNeg enstrophy eigenvalue≤0
  in
  subst
    (λ right → eigenvalue * enstrophy ≤ right)
    (solve (enstrophy ∷ []))
    raw

smallestAlignedDeviatoricContractionNonpositive :
  ∀ spectrum enstrophy →
  0ℚ ≤ enstrophy →
  alignedDeviatoricContraction (lambda3 spectrum) enstrophy ≤ 0ℚ
smallestAlignedDeviatoricContractionNonpositive spectrum enstrophy enstrophyNN =
  alignedNonpositiveEigenvalueGivesNonpositiveContraction
    (lambda3 spectrum)
    enstrophy
    (smallestDeviatoricEigenvalueNonpositive spectrum)
    enstrophyNN

alignedDeviatoricPressureEnablesAfterMinusSign :
  ∀ eigenvalue enstrophy →
  eigenvalue ≤ 0ℚ →
  0ℚ ≤ enstrophy →
  0ℚ ≤ - alignedDeviatoricContraction eigenvalue enstrophy
alignedDeviatoricPressureEnablesAfterMinusSign
    eigenvalue enstrophy eigenvalue≤0 enstrophyNN =
  let
    contraction≤0 =
      alignedNonpositiveEigenvalueGivesNonpositiveContraction
        eigenvalue enstrophy eigenvalue≤0 enstrophyNN
    negated = ℚP.neg-antimono-≤ contraction≤0
  in
  subst
    (λ left → left ≤ - alignedDeviatoricContraction eigenvalue enstrophy)
    (solve [])
    negated

smallestAlignedDeviatoricPressureEnables :
  ∀ spectrum enstrophy →
  0ℚ ≤ enstrophy →
  0ℚ ≤ - alignedDeviatoricContraction (lambda3 spectrum) enstrophy
smallestAlignedDeviatoricPressureEnables spectrum enstrophy enstrophyNN =
  alignedDeviatoricPressureEnablesAfterMinusSign
    (lambda3 spectrum)
    enstrophy
    (smallestDeviatoricEigenvalueNonpositive spectrum)
    enstrophyNN

round78TraceFreeOrderingForcesSmallestDeviatoricEigenvalueNonpositive : Bool
round78TraceFreeOrderingForcesSmallestDeviatoricEigenvalueNonpositive = true

round78AlignedSmallestDeviatoricEigenvectorGivesEnablingSign : Bool
round78AlignedSmallestDeviatoricEigenvectorGivesEnablingSign = true

round78DNSNearAlignmentPromotedToExactSelectedEventAlignment : Bool
round78DNSNearAlignmentPromotedToExactSelectedEventAlignment = false

round78AlignedSmallestDeviatoricEigenvectorGivesEnablingSignIsTrue :
  round78AlignedSmallestDeviatoricEigenvectorGivesEnablingSign ≡ true
round78AlignedSmallestDeviatoricEigenvectorGivesEnablingSignIsTrue = refl
