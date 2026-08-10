module DASHI.Physics.Closure.NSTriadKNNineOwnerRobustReservePolytopeRound36Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- DOI: 10.1007/978-3-642-16830-7.
--
-- Author: Xiaoyutao Luo.
-- Title: "A Beale--Kato--Majda Criterion with Optimal Frequency and
-- Temporal Localization".
-- DOI: 10.1007/s00021-019-0411-z.
--
-- DASHI CONTRIBUTION
--
-- Round 33 proved positivity of the viscosity reserve for one literal strict
-- owner allocation.  The continuation analysis asks for a more robust object:
-- a feasible region of allocations that stays uniformly inside the simplex
-- sum eta_i < 1.
--
-- This module formalizes an exact axis-aligned inner polytope.  A list of
-- upper envelopes u_i is safe when every physical eta_i <= u_i and
--
--   sum_i u_i < 1.
--
-- Then automatically
--
--   sum_i eta_i <= sum_i u_i < 1.
--
-- Hence every allocation represented by the box has a strict viscosity
-- reserve; closure is not tied to one brittle point.  The physical task is to
-- construct such a box from the nine owner producer constants.  No numerical
-- or analytic optimizer is postulated here.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _+_; _-_; _≤_; _<_)
import Data.Rational.Properties as ℚP
open import Relation.Binary.PropositionalEquality using (cong)

import DASHI.Physics.Closure.NSTriadKNAdmissibleOwnerTaxLanguageRound28Exact as Owner

sumUpper : List ℚ → ℚ
sumUpper [] = 0ℚ
sumUpper (upper ∷ rest) = upper + sumUpper rest

data PointwiseEtaUpper
    {environment : Owner.TaxEnvironment} :
    (estimates : List (Owner.AdmissibleOwnerEstimate environment)) →
    List ℚ → Set where
  upper[] : PointwiseEtaUpper [] []
  upper∷ :
    ∀ {estimate rest upper uppers} →
    Owner.eta estimate ≤ upper →
    PointwiseEtaUpper rest uppers →
    PointwiseEtaUpper (estimate ∷ rest) (upper ∷ uppers)

etaTotalBelowEnvelope :
  ∀ {environment}
    {estimates : List (Owner.AdmissibleOwnerEstimate environment)}
    {uppers : List ℚ} →
  PointwiseEtaUpper estimates uppers →
  Owner.sumEta estimates ≤ sumUpper uppers
etaTotalBelowEnvelope upper[] = ℚP.≤-refl
etaTotalBelowEnvelope (upper∷ current rest) =
  ℚP.+-mono-≤ current (etaTotalBelowEnvelope rest)

record RobustOwnerBudgetBox
    {environment : Owner.TaxEnvironment}
    (estimates : List (Owner.AdmissibleOwnerEstimate environment)) : Set where
  constructor robust-owner-budget-box
  field
    upperCoordinates : List ℚ
    pointwiseUpper : PointwiseEtaUpper estimates upperCoordinates
    eachActualEtaNonnegative : Owner.AllEtasNonnegative estimates
    envelopeTotalStrict : sumUpper upperCoordinates < 1ℚ

open RobustOwnerBudgetBox public

actualEtaTotalBelowEnvelope :
  ∀ {environment estimates}
    (box : RobustOwnerBudgetBox {environment} estimates) →
  Owner.sumEta estimates ≤ sumUpper (upperCoordinates box)
actualEtaTotalBelowEnvelope box =
  etaTotalBelowEnvelope (pointwiseUpper box)

robustActualEtaTotalStrict :
  ∀ {environment estimates}
    (box : RobustOwnerBudgetBox {environment} estimates) →
  Owner.sumEta estimates < 1ℚ
robustActualEtaTotalStrict box =
  ℚP.≤-<-trans
    (actualEtaTotalBelowEnvelope box)
    (envelopeTotalStrict box)

robustReserveFloor :
  ∀ {environment estimates} →
  RobustOwnerBudgetBox {environment} estimates → ℚ
robustReserveFloor box = 1ℚ - sumUpper (upperCoordinates box)

actualViscosityReserve :
  ∀ {environment}
    (estimates : List (Owner.AdmissibleOwnerEstimate environment)) → ℚ
actualViscosityReserve estimates = 1ℚ - Owner.sumEta estimates

record RobustNineOwnerBudgetPolytope
    {environment : Owner.TaxEnvironment}
    (family : Owner.NineOwnerEstimateFamily environment) : Set where
  constructor robust-nine-owner-budget-polytope
  field
    safeBox : RobustOwnerBudgetBox (Owner.nineOwnerList family)

open RobustNineOwnerBudgetPolytope public

robustNineOwnerEtaStrict :
  ∀ {environment} {family : Owner.NineOwnerEstimateFamily environment} →
  RobustNineOwnerBudgetPolytope family →
  Owner.sumEta (Owner.nineOwnerList family) < 1ℚ
robustNineOwnerEtaStrict polytope =
  robustActualEtaTotalStrict (safeBox polytope)

robustNineOwnerReserveFloor :
  ∀ {environment} {family : Owner.NineOwnerEstimateFamily environment} →
  RobustNineOwnerBudgetPolytope family → ℚ
robustNineOwnerReserveFloor polytope =
  robustReserveFloor (safeBox polytope)

robustOwnerReservePolytopeAlgebraClosed : Bool
robustOwnerReservePolytopeAlgebraClosed = true

physicalRobustNineOwnerBudgetPolytopeConstructed : Bool
physicalRobustNineOwnerBudgetPolytopeConstructed = false

robustOwnerReservePolytopeAlgebraClosedIsTrue :
  robustOwnerReservePolytopeAlgebraClosed ≡ true
robustOwnerReservePolytopeAlgebraClosedIsTrue = refl

physicalRobustNineOwnerBudgetPolytopeConstructedIsFalse :
  physicalRobustNineOwnerBudgetPolytopeConstructed ≡ false
physicalRobustNineOwnerBudgetPolytopeConstructedIsFalse = refl
