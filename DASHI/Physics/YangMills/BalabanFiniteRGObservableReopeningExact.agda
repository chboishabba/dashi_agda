module DASHI.Physics.YangMills.BalabanFiniteRGObservableReopeningExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- P. K. Mitter,
-- "The Exact Renormalization Group", Encyclopedia of Mathematical Physics
-- (Elsevier, 2006), arXiv:math-ph/0505008.
-- No DOI is used here; the persistent source identifier is math-ph/0505008.
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. I:
-- Generation of Effective Actions in a Small Field Approximation and a
-- Coupling Constant Renormalization in Four Dimensions",
-- Communications in Mathematical Physics 109 (1987), 249--301.
-- No DOI is asserted in this module.
--
-- DASHI CONTRIBUTION
--
-- A finite RG coarse-graining is represented together with its reopening
-- kernel kappa(y,x).  Exact disintegration
--
--   mu_fine(x) = sum_y mu_coarse(y) kappa(y,x)
--
-- implies exact observable transport
--
--   (T O)(y) = sum_x kappa(y,x) O(x),
--
--   E_fine[O] = E_coarse[T O].
--
-- The same theorem is proved for composite observables without a factorization
-- assumption.  Thus the coarse state is not a terminal classification: the
-- proof-relevant reopening kernel retains the fine observable information that
-- downstream Schwinger functions need.  This is finite algebra only; locality,
-- positivity and all-scale bounds remain genuine later analytic producers.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List)
open import Data.Empty using (⊥)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; 1ℚ; _*_; _+_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact as Sums
import DASHI.Physics.YangMills.BalabanFiniteSumFubiniExact as Fubini

Observable : Set → Set
Observable State = State → ℚ

record FiniteRGReopeningStep (Fine Coarse : Set) : Set₁ where
  field
    fineStates : List Fine
    coarseStates : List Coarse
    project : Fine → Coarse

    fineWeight : Fine → ℚ
    coarseWeight : Coarse → ℚ
    reopeningKernel : Coarse → Fine → ℚ

    FibreSupport : Coarse → Fine → Set
    fibreSupportProjects : ∀ {coarse fine} →
      FibreSupport coarse fine → project fine ≡ coarse
    reopeningOffFibreZero : ∀ coarse fine →
      (FibreSupport coarse fine → ⊥) →
      reopeningKernel coarse fine ≡ 0ℚ

    reopeningNormalized : ∀ coarse →
      Sums.sumRational fineStates (reopeningKernel coarse) ≡ 1ℚ

    disintegrationExact : ∀ fine →
      fineWeight fine
      ≡ Sums.sumRational coarseStates
          (λ coarse → coarseWeight coarse * reopeningKernel coarse fine)

open FiniteRGReopeningStep public

transportObservable :
  ∀ {Fine Coarse} →
  FiniteRGReopeningStep Fine Coarse →
  Observable Fine → Observable Coarse
transportObservable step observable coarse =
  Sums.sumRational (fineStates step)
    (λ fine → reopeningKernel step coarse fine * observable fine)

fineExpectation :
  ∀ {Fine Coarse} →
  FiniteRGReopeningStep Fine Coarse → Observable Fine → ℚ
fineExpectation step observable =
  Sums.sumRational (fineStates step)
    (λ fine → fineWeight step fine * observable fine)

coarseExpectation :
  ∀ {Fine Coarse} →
  FiniteRGReopeningStep Fine Coarse → Observable Coarse → ℚ
coarseExpectation step observable =
  Sums.sumRational (coarseStates step)
    (λ coarse → coarseWeight step coarse * observable coarse)

finiteRGObservableExpectationPreserved :
  ∀ {Fine Coarse}
    (step : FiniteRGReopeningStep Fine Coarse)
    (observable : Observable Fine) →
  fineExpectation step observable
  ≡ coarseExpectation step (transportObservable step observable)
finiteRGObservableExpectationPreserved step observable =
  let
    expandedFine : Fine → ℚ
    expandedFine fine =
      Sums.sumRational (coarseStates step)
        (λ coarse →
          (coarseWeight step coarse * reopeningKernel step coarse fine)
            * observable fine)

    expand :
      fineExpectation step observable
      ≡ Sums.sumRational (fineStates step) expandedFine
    expand = Sums.sumRationalCong (fineStates step) _ _
      (λ fine →
        trans
          (cong (_* observable fine) (disintegrationExact step fine))
          (trans
            (sym
              (Sums.sumRationalScale
                (observable fine)
                (coarseStates step)
                (λ coarse →
                  coarseWeight step coarse
                    * reopeningKernel step coarse fine)))
            (Sums.sumRationalCong (coarseStates step) _ _
              (λ coarse → ℚRing.solve-∀
                (coarseWeight step coarse)
                (reopeningKernel step coarse fine)
                (observable fine)))))

    swap :
      Sums.sumRational (fineStates step) expandedFine
      ≡ Sums.sumRational (coarseStates step)
          (λ coarse →
            Sums.sumRational (fineStates step)
              (λ fine →
                (coarseWeight step coarse
                  * reopeningKernel step coarse fine)
                  * observable fine))
    swap = Fubini.sumSwap
      (fineStates step) (coarseStates step)
      (λ fine coarse →
        (coarseWeight step coarse * reopeningKernel step coarse fine)
          * observable fine)

    factor : ∀ coarse →
      Sums.sumRational (fineStates step)
        (λ fine →
          (coarseWeight step coarse * reopeningKernel step coarse fine)
            * observable fine)
      ≡ coarseWeight step coarse
          * transportObservable step observable coarse
    factor coarse =
      trans
        (Sums.sumRationalCong (fineStates step) _ _
          (λ fine → ℚRing.solve-∀
            (coarseWeight step coarse)
            (reopeningKernel step coarse fine)
            (observable fine)))
        (Sums.sumRationalScale
          (coarseWeight step coarse)
          (fineStates step)
          (λ fine → reopeningKernel step coarse fine * observable fine))
  in
  trans expand
    (trans swap
      (Sums.sumRationalCong (coarseStates step) _ _ factor))

transportComposite :
  ∀ {Fine Coarse} →
  FiniteRGReopeningStep Fine Coarse →
  Observable Fine → Observable Fine → Observable Coarse
transportComposite step left right =
  transportObservable step (λ fine → left fine * right fine)

finiteRGCompositeExpectationPreserved :
  ∀ {Fine Coarse}
    (step : FiniteRGReopeningStep Fine Coarse)
    (left right : Observable Fine) →
  fineExpectation step (λ fine → left fine * right fine)
  ≡ coarseExpectation step (transportComposite step left right)
finiteRGCompositeExpectationPreserved step left right =
  finiteRGObservableExpectationPreserved step
    (λ fine → left fine * right fine)

transportConstantOneExact :
  ∀ {Fine Coarse}
    (step : FiniteRGReopeningStep Fine Coarse) coarse →
  transportObservable step (λ _ → 1ℚ) coarse ≡ 1ℚ
transportConstantOneExact step coarse =
  trans
    (Sums.sumRationalCong (fineStates step) _ _
      (λ fine → ℚP.*-identityʳ (reopeningKernel step coarse fine)))
    (reopeningNormalized step coarse)

finiteRGObservableReopeningLevel : ProofLevel
finiteRGObservableReopeningLevel = machineChecked

finiteRGCompositeObservableTransportLevel : ProofLevel
finiteRGCompositeObservableTransportLevel = machineChecked

scaleUniformRGAnalyticProducerStillRequiredLevel : ProofLevel
scaleUniformRGAnalyticProducerStillRequiredLevel = conditional
