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
-- For the smallest trace-free eigenvalue lambda<=0 and Omega>=0 this
-- contraction is nonpositive.  Since the stretching-acceleration equation
-- contains -omega^T H omega, its negation is a nonnegative enabling channel.
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
open import Data.Rational.Base using (ℚ; 0ℚ; _*_; -_; _≤_; nonNegative)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst)

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

round78AlignedSmallestDeviatoricEigenvectorGivesEnablingSign : Bool
round78AlignedSmallestDeviatoricEigenvectorGivesEnablingSign = true

round78DNSNearAlignmentPromotedToExactSelectedEventAlignment : Bool
round78DNSNearAlignmentPromotedToExactSelectedEventAlignment = false

round78AlignedSmallestDeviatoricEigenvectorGivesEnablingSignIsTrue :
  round78AlignedSmallestDeviatoricEigenvectorGivesEnablingSign ≡ true
round78AlignedSmallestDeviatoricEigenvectorGivesEnablingSignIsTrue = refl
