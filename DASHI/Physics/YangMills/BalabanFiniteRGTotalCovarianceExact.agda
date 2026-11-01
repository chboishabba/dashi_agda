module DASHI.Physics.YangMills.BalabanFiniteRGTotalCovarianceExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- P. K. Mitter,
-- "The Exact Renormalization Group", Encyclopedia of Mathematical Physics
-- (Elsevier, 2006), arXiv:math-ph/0505008.
-- Persistent identifier: arXiv:math-ph/0505008.
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. I:
-- Generation of Effective Actions in a Small Field Approximation and a
-- Coupling Constant Renormalization in Four Dimensions",
-- Communications in Mathematical Physics 109 (1987), 249--301.
-- DOI: 10.1007/BF01215223.
--
-- DASHI CONTRIBUTION
--
-- Extend the exact finite reopening/disintegration theorem from raw moments
-- to connected two-point functions.  For a fine observable pair X,Y and the
-- coarse variable C carried by an RG reopening kernel, prove the finite law
-- of total covariance exactly over Q:
--
--   Cov_fine(X,Y)
--     = Cov_coarse(E[X|C],E[Y|C])
--       + E_coarse[ Cov(X,Y|C) ].
--
-- The variance identity is the diagonal case.  No factorization assumption is
-- made: the conditional covariance retains the fibre/residual correlation.
-- This is the proof-bearing algebraic bridge needed by an eventual
-- scale-uniform RG clustering argument; no all-scale decay claim is made here.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base as ℚ using
  (ℚ; _+_; _-_; _*_)
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact as Sums
import DASHI.Physics.YangMills.BalabanFiniteRGObservableReopeningExact as Reopen

------------------------------------------------------------------------
-- Fine/coarse connected moments and the residual fibre covariance.
------------------------------------------------------------------------

fineCovariance :
  ∀ {Fine Coarse} →
  Reopen.FiniteRGReopeningStep Fine Coarse →
  Reopen.Observable Fine → Reopen.Observable Fine → ℚ
fineCovariance step left right =
  Reopen.fineExpectation step (λ fine → left fine * right fine)
  - Reopen.fineExpectation step left * Reopen.fineExpectation step right

coarseCovariance :
  ∀ {Fine Coarse} →
  Reopen.FiniteRGReopeningStep Fine Coarse →
  Reopen.Observable Coarse → Reopen.Observable Coarse → ℚ
coarseCovariance step left right =
  Reopen.coarseExpectation step (λ coarse → left coarse * right coarse)
  - Reopen.coarseExpectation step left * Reopen.coarseExpectation step right

conditionalCovariance :
  ∀ {Fine Coarse} →
  Reopen.FiniteRGReopeningStep Fine Coarse →
  Reopen.Observable Fine → Reopen.Observable Fine →
  Reopen.Observable Coarse
conditionalCovariance step left right coarse =
  Reopen.transportComposite step left right coarse
  - Reopen.transportObservable step left coarse
      * Reopen.transportObservable step right coarse

fineVariance :
  ∀ {Fine Coarse} →
  Reopen.FiniteRGReopeningStep Fine Coarse →
  Reopen.Observable Fine → ℚ
fineVariance step observable = fineCovariance step observable observable

coarseVariance :
  ∀ {Fine Coarse} →
  Reopen.FiniteRGReopeningStep Fine Coarse →
  Reopen.Observable Coarse → ℚ
coarseVariance step observable = coarseCovariance step observable observable

conditionalVariance :
  ∀ {Fine Coarse} →
  Reopen.FiniteRGReopeningStep Fine Coarse →
  Reopen.Observable Fine → Reopen.Observable Coarse
conditionalVariance step observable =
  conditionalCovariance step observable observable

------------------------------------------------------------------------
-- Weighted finite expectations commute with subtraction.
------------------------------------------------------------------------

sumWeightedSubtract :
  ∀ {A : Set} (values : List A)
    (weight left right : A → ℚ) →
  Sums.sumRational values
    (λ value → weight value * (left value - right value))
  ≡ Sums.sumRational values (λ value → weight value * left value)
    - Sums.sumRational values (λ value → weight value * right value)
sumWeightedSubtract [] weight left right = ℚRing.solve []
sumWeightedSubtract (value ∷ values) weight left right
  rewrite sumWeightedSubtract values weight left right =
  ℚRing.solve-∀
    (weight value) (left value) (right value)
    (Sums.sumRational values (λ selected → weight selected * left selected))
    (Sums.sumRational values (λ selected → weight selected * right selected))

coarseExpectationSubtractExact :
  ∀ {Fine Coarse}
    (step : Reopen.FiniteRGReopeningStep Fine Coarse)
    (left right : Reopen.Observable Coarse) →
  Reopen.coarseExpectation step (λ coarse → left coarse - right coarse)
  ≡ Reopen.coarseExpectation step left
    - Reopen.coarseExpectation step right
coarseExpectationSubtractExact step left right =
  sumWeightedSubtract
    (Reopen.coarseStates step) (Reopen.coarseWeight step) left right

------------------------------------------------------------------------
-- Law of total covariance.
------------------------------------------------------------------------

finiteRGTotalCovariance :
  ∀ {Fine Coarse}
    (step : Reopen.FiniteRGReopeningStep Fine Coarse)
    (left right : Reopen.Observable Fine) →
  fineCovariance step left right
  ≡ coarseCovariance step
      (Reopen.transportObservable step left)
      (Reopen.transportObservable step right)
    + Reopen.coarseExpectation step
        (conditionalCovariance step left right)
finiteRGTotalCovariance {Coarse = Coarse} step left right =
  let
    transportedLeft = Reopen.transportObservable step left
    transportedRight = Reopen.transportObservable step right
    transportedProduct = Reopen.transportComposite step left right

    coarseProduct : Reopen.Observable Coarse
    coarseProduct coarse = transportedLeft coarse * transportedRight coarse

    productMoment =
      Reopen.finiteRGCompositeExpectationPreserved step left right
    leftMoment = Reopen.finiteRGObservableExpectationPreserved step left
    rightMoment = Reopen.finiteRGObservableExpectationPreserved step right
    residualMoment =
      coarseExpectationSubtractExact step transportedProduct coarseProduct
  in
  trans
    (cong
      (λ selectedProduct →
        selectedProduct
        - Reopen.fineExpectation step left
            * Reopen.fineExpectation step right)
      productMoment)
    (trans
      (cong
        (λ selectedLeft →
          Reopen.coarseExpectation step transportedProduct
          - selectedLeft * Reopen.fineExpectation step right)
        leftMoment)
      (trans
        (cong
          (λ selectedRight →
            Reopen.coarseExpectation step transportedProduct
            - Reopen.coarseExpectation step transportedLeft * selectedRight)
          rightMoment)
        (let
          productCoarse = Reopen.coarseExpectation step coarseProduct
          meanLeft = Reopen.coarseExpectation step transportedLeft
          meanRight = Reopen.coarseExpectation step transportedRight
          productTransport = Reopen.coarseExpectation step transportedProduct

          residualExact :
            Reopen.coarseExpectation step
              (conditionalCovariance step left right)
            ≡ productTransport - productCoarse
          residualExact = residualMoment
        in
        trans
          (ℚRing.solve-∀ productTransport productCoarse meanLeft meanRight)
          (cong
            (λ residual →
              (productCoarse - meanLeft * meanRight) + residual)
            (sym residualExact)))))

------------------------------------------------------------------------
-- Variance and connected-observable forms.
------------------------------------------------------------------------

finiteRGTotalVariance :
  ∀ {Fine Coarse}
    (step : Reopen.FiniteRGReopeningStep Fine Coarse)
    (observable : Reopen.Observable Fine) →
  fineVariance step observable
  ≡ coarseVariance step (Reopen.transportObservable step observable)
    + Reopen.coarseExpectation step
        (conditionalVariance step observable)
finiteRGTotalVariance step observable =
  finiteRGTotalCovariance step observable observable

finiteRGConnectedObservableReopening :
  ∀ {Fine Coarse}
    (step : Reopen.FiniteRGReopeningStep Fine Coarse)
    (left right : Reopen.Observable Fine) →
  fineCovariance step left right
  ≡ coarseCovariance step
      (Reopen.transportObservable step left)
      (Reopen.transportObservable step right)
    + Reopen.coarseExpectation step
        (conditionalCovariance step left right)
finiteRGConnectedObservableReopening = finiteRGTotalCovariance

finiteRGTotalCovarianceLevel : ProofLevel
finiteRGTotalCovarianceLevel = machineChecked

finiteRGTotalVarianceLevel : ProofLevel
finiteRGTotalVarianceLevel = machineChecked

finiteRGConnectedObservableReopeningLevel : ProofLevel
finiteRGConnectedObservableReopeningLevel = machineChecked
