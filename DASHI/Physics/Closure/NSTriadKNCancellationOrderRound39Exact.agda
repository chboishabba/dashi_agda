module DASHI.Physics.Closure.NSTriadKNCancellationOrderRound39Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: Peter Constantin; Charles Fefferman.
-- Title: "Direction of Vorticity and the Problem of Global Regularity for
-- the Navier--Stokes Equations".
-- DOI: 10.1512/iumj.1993.42.42034.
--
-- Authors: Tosio Kato; Gustavo Ponce.
-- Title: "Commutator Estimates and the Euler and Navier--Stokes Equations".
-- DOI: 10.1002/cpa.3160410704.
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- DOI: 10.1007/978-3-642-16830-7.
--
-- DASHI CONTRIBUTION
--
-- NS now has three genuinely different cancellations:
--
--   1. exact algebraic cancellation (triad skew/reality identities),
--   2. geometric or spectral cancellation (vorticity-line residual / Gram),
--   3. signed cross-owner cancellation before the final positive tax.
--
-- Taking absolute values before these stages destroys usable reserve.  This
-- module formalizes the numerical consequence rather than merely naming a
-- pipeline.  A physical term supplies exact nonnegative savings A and G with
--
--   rawPositive = preTaxPositive + A + G.
--
-- Hence pre-tax production can never exceed raw production, and every further
-- witnessed signed-owner flow can only reduce it again.  The future physical
-- proof must identify A and G with actual triad/geometric/spectral identities;
-- no saving is created by this record.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _≤_)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst)

import DASHI.Physics.Closure.NSTriadKNSignedOwnerCancellationFlowRound38Exact as Flow

record PreTaxCancellationDecomposition : Set where
  constructor pre-tax-cancellation-decomposition
  field
    rawPositive : ℚ
    exactAlgebraicSaving : ℚ
    geometricOrSpectralSaving : ℚ
    preTaxPositive : ℚ

    rawPositiveNonnegative : 0ℚ ≤ rawPositive
    exactAlgebraicSavingNonnegative : 0ℚ ≤ exactAlgebraicSaving
    geometricOrSpectralSavingNonnegative : 0ℚ ≤ geometricOrSpectralSaving
    preTaxPositiveNonnegative : 0ℚ ≤ preTaxPositive

    exactCancellationAccounting :
      rawPositive
      ≡ preTaxPositive + exactAlgebraicSaving + geometricOrSpectralSaving

open PreTaxCancellationDecomposition public

cancellationSavingsNonnegative :
  ∀ decomposition →
  0ℚ ≤ exactAlgebraicSaving decomposition
    + geometricOrSpectralSaving decomposition
cancellationSavingsNonnegative decomposition =
  ℚP.+-mono-≤
    (exactAlgebraicSavingNonnegative decomposition)
    (geometricOrSpectralSavingNonnegative decomposition)

preTaxPositiveCannotExceedRaw :
  ∀ decomposition →
  preTaxPositive decomposition ≤ rawPositive decomposition
preTaxPositiveCannotExceedRaw decomposition =
  let
    addSavings :
      preTaxPositive decomposition + 0ℚ
      ≤ preTaxPositive decomposition
        + (exactAlgebraicSaving decomposition
          + geometricOrSpectralSaving decomposition)
    addSavings = ℚP.+-monoʳ-≤
      (preTaxPositive decomposition)
      (cancellationSavingsNonnegative decomposition)

    rightMeaning :
      preTaxPositive decomposition
        + (exactAlgebraicSaving decomposition
          + geometricOrSpectralSaving decomposition)
      ≡ rawPositive decomposition
    rightMeaning =
      subst
        (λ value →
          preTaxPositive decomposition
            + (exactAlgebraicSaving decomposition
              + geometricOrSpectralSaving decomposition)
          ≡ value)
        (exactCancellationAccounting decomposition)
        (solve
          ( preTaxPositive decomposition
          ∷ exactAlgebraicSaving decomposition
          ∷ geometricOrSpectralSaving decomposition
          ∷ []))
  in
  subst
    (λ upper → preTaxPositive decomposition ≤ upper)
    rightMeaning
    (subst
      (λ lower → lower ≤
        preTaxPositive decomposition
          + (exactAlgebraicSaving decomposition
            + geometricOrSpectralSaving decomposition))
      (solve (preTaxPositive decomposition ∷ []))
      addSavings)

record OrderedCancellationThenOwnerFlow : Set₁ where
  field
    cancellation : PreTaxCancellationDecomposition
    ownerEdge : Flow.PhysicalCancellationEdge
    edgeStartsAtPreTax :
      Flow.positiveTaxBefore (Flow.flow ownerEdge)
      ≡ preTaxPositive cancellation

open OrderedCancellationThenOwnerFlow public

finalTaxAfterAllCancellations : OrderedCancellationThenOwnerFlow → ℚ
finalTaxAfterAllCancellations path =
  Flow.positiveTaxAfter (Flow.flow (ownerEdge path))

finalTaxCannotExceedRawPositive :
  ∀ path →
  finalTaxAfterAllCancellations path
  ≤ rawPositive (cancellation path)
finalTaxCannotExceedRawPositive path =
  ℚP.≤-trans
    (subst
      (λ upper → finalTaxAfterAllCancellations path ≤ upper)
      (edgeStartsAtPreTax path)
      (Flow.physicalCancellationEdgeDoesNotIncreaseTax (ownerEdge path)))
    (preTaxPositiveCannotExceedRaw (cancellation path))

cancellationOrderAlgebraClosed : Bool
cancellationOrderAlgebraClosed = true

physicalCancellationHierarchyIdentified : Bool
physicalCancellationHierarchyIdentified = false

cancellationOrderAlgebraClosedIsTrue :
  cancellationOrderAlgebraClosed ≡ true
cancellationOrderAlgebraClosedIsTrue = refl
