module DASHI.Physics.Closure.NSTriadKNDeviatoricPressureAlignmentDefectRound78Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: Dhawal Buaria; Alain Pumir.
-- Title: "Role of pressure in generation of intense velocity gradients in
-- turbulent flows".
-- DOI: 10.48550/arXiv.2308.03902.
--
-- Authors: Peter Constantin; Charles Fefferman.
-- Title: "Direction of Vorticity and the Problem of Global Regularity for the
-- Navier-Stokes Equations".
-- DOI: 10.1512/iumj.1993.42.42034.
--
-- ROUND78 / IMPERFECT PRESSURE-EIGENFRAME ALIGNMENT
--
-- The existing packet-coherence lane already tracks squared alignment weights
-- alpha_i=(xi.e_i)^2.  For a unit vorticity direction in the ordered
-- deviatoric pressure-Hessian eigenframe, alpha1+alpha2+alpha3=1 and
--
--   (omega^T H^D omega)/Omega
--     = lambda1 alpha1 + lambda2 alpha2 + lambda3 alpha3
--     = lambda3
--       + (lambda1-lambda3) alpha1
--       + (lambda2-lambda3) alpha2.
--
-- Thus departure from the smallest-eigenvector enabling endpoint has the exact
-- defect currency
--
--   D_align = (lambda1-lambda3) alpha1
--             + (lambda2-lambda3) alpha2.
--
-- No DNS near-alignment statement is promoted.  This module supplies the exact
-- algebra needed for a selected-event theorem to quantify how much imperfect
-- alignment eats the nonlocal pressure enabling term.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base using (ℚ; 1ℚ; _+_; _*_; _-_; -_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; trans)

record PressureEigenframeAlignment : Set where
  constructor pressure-eigenframe-alignment
  field
    lambda1 lambda2 lambda3 : ℚ
    alpha1 alpha2 alpha3 : ℚ
    alignmentWeightsSumOne : (alpha1 + alpha2) + alpha3 ≡ 1ℚ

open PressureEigenframeAlignment public

normalizedDeviatoricContraction : PressureEigenframeAlignment → ℚ
normalizedDeviatoricContraction alignment =
  lambda1 alignment * alpha1 alignment
  + lambda2 alignment * alpha2 alignment
  + lambda3 alignment * alpha3 alignment

alignmentDefectCost : PressureEigenframeAlignment → ℚ
alignmentDefectCost alignment =
  (lambda1 alignment - lambda3 alignment) * alpha1 alignment
  + (lambda2 alignment - lambda3 alignment) * alpha2 alignment

normalizedContractionEqualsSmallestPlusAlignmentDefect :
  ∀ alignment →
  normalizedDeviatoricContraction alignment
  ≡ lambda3 alignment + alignmentDefectCost alignment
normalizedContractionEqualsSmallestPlusAlignmentDefect alignment =
  let
    l1 = lambda1 alignment
    l2 = lambda2 alignment
    l3 = lambda3 alignment
    a1 = alpha1 alignment
    a2 = alpha2 alignment
    a3 = alpha3 alignment

    regrouped :
      normalizedDeviatoricContraction alignment
      ≡ (l1 - l3) * a1 + (l2 - l3) * a2 + l3 * ((a1 + a2) + a3)
    regrouped = solve (l1 ∷ l2 ∷ l3 ∷ a1 ∷ a2 ∷ a3 ∷ [])

    weightsClosed :
      (l1 - l3) * a1 + (l2 - l3) * a2 + l3 * ((a1 + a2) + a3)
      ≡ (l1 - l3) * a1 + (l2 - l3) * a2 + l3 * 1ℚ
    weightsClosed =
      cong
        (λ sumWeights →
          (l1 - l3) * a1 + (l2 - l3) * a2 + l3 * sumWeights)
        (alignmentWeightsSumOne alignment)

    endpoint :
      (l1 - l3) * a1 + (l2 - l3) * a2 + l3 * 1ℚ
      ≡ l3 + alignmentDefectCost alignment
    endpoint = solve (l1 ∷ l2 ∷ l3 ∷ a1 ∷ a2 ∷ [])
  in
  trans regrouped (trans weightsClosed endpoint)

negatedNormalizedContractionExact :
  ∀ alignment →
  - normalizedDeviatoricContraction alignment
  ≡ (- lambda3 alignment) - alignmentDefectCost alignment
negatedNormalizedContractionExact alignment =
  trans
    (cong -_ (normalizedContractionEqualsSmallestPlusAlignmentDefect alignment))
    (solve (lambda3 alignment ∷ alignmentDefectCost alignment ∷ []))

fullDeviatoricContraction : ℚ → PressureEigenframeAlignment → ℚ
fullDeviatoricContraction enstrophy alignment =
  enstrophy * normalizedDeviatoricContraction alignment

negatedFullDeviatoricContractionFactors :
  ∀ enstrophy alignment →
  - fullDeviatoricContraction enstrophy alignment
  ≡ enstrophy
      * ((- lambda3 alignment) - alignmentDefectCost alignment)
negatedFullDeviatoricContractionFactors enstrophy alignment =
  trans
    (solve (enstrophy ∷ normalizedDeviatoricContraction alignment ∷ []))
    (cong
      (enstrophy *_)
      (negatedNormalizedContractionExact alignment))

round78PressureAlignmentDefectIdentityConstructed : Bool
round78PressureAlignmentDefectIdentityConstructed = true

round78DNSNearAlignmentPromotedToSelectedEventDefectBound : Bool
round78DNSNearAlignmentPromotedToSelectedEventDefectBound = false

round78PressureAlignmentDefectIdentityConstructedIsTrue :
  round78PressureAlignmentDefectIdentityConstructed ≡ true
round78PressureAlignmentDefectIdentityConstructedIsTrue = refl
