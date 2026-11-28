module DASHI.Moonshine.Y443FLMBilinearProductSpanWeldExact where

-- Actual weight-two span owner. Compare two transported products on
-- that SAME source, with bilinearity into a common target. This is
-- the remaining mode-one product comparison reduction, not a new VOA.
-- The source map and its actual bilinearity witnesses are still needed.

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Fin.Base using (Fin)
import DASHI.Moonshine.VertexOperatorAlgebraCore as VOA
import DASHI.Moonshine.Y443FLMGriessFullAutSelectedVOAExact as FLM
import DASHI.Moonshine.Y443FLMWeightTwoBasisUVExact as Basis

module Selected (V : VOA.VertexOperatorAlgebra) where
  module A = FLM.Selected V
  module B = Basis.Selected V
  open Basis using (sym; trans; cong; cong₂)

  module WithSpan
    (griess : A.ConcreteGriessProduct)
    where
    module L = B.WithGriess griess

    module Compare
      (span : L.ActualWeightTwoSpan)
      (T : Set)
      (add : T → T → T)
      (scale : A.Scalar → T → T)
      where

      record Linear (f : A.WeightTwo → T) : Set where
        field
          sumLaw : (x y : A.WeightTwo) →
            f (A.weightTwoAdd griess x y) ≡ add (f x) (f y)
          scaleLaw : (s : A.Scalar) (x : A.WeightTwo) →
            f (A.weightTwoScale griess s x) ≡ scale s (f x)
      open Linear

      linearTermAgreement :
        (f g : A.WeightTwo → T) →
        Linear f → Linear g →
        ((i : Fin 196884) → f (L.basisState span i) ≡ g (L.basisState span i)) →
        (t : L.LinearTerm) →
        f (L.evaluate span t) ≡ g (L.evaluate span t)
      linearTermAgreement f g lf lg eq (L.basis i) =
        trans (cong f (L.evaluateBasis span i))
          (trans (eq i) (sym (cong g (L.evaluateBasis span i))))
      linearTermAgreement f g lf lg eq (L.sumTerm x y) =
        trans (cong f (L.evaluateSum span x y))
          (trans (sumLaw lf (L.evaluate span x) (L.evaluate span y))
            (trans (cong₂ add
              (linearTermAgreement f g lf lg eq x)
              (linearTermAgreement f g lf lg eq y))
              (trans (sym (sumLaw lg (L.evaluate span x) (L.evaluate span y)))
                (sym (cong g (L.evaluateSum span x y))))))
      linearTermAgreement f g lf lg eq (L.scaleTerm s x) =
        trans (cong f (L.evaluateScale span s x))
          (trans (scaleLaw lf s (L.evaluate span x))
            (trans (cong (scale s) (linearTermAgreement f g lf lg eq x))
              (trans (sym (scaleLaw lg s (L.evaluate span x)))
                (sym (cong g (L.evaluateScale span s x))))))

      linearAgreement :
        (f g : A.WeightTwo → T) →
        Linear f → Linear g →
        ((i : Fin 196884) → f (L.basisState span i) ≡ g (L.basisState span i)) →
        (x : A.WeightTwo) → f x ≡ g x
      linearAgreement f g lf lg eq x =
        trans (sym (cong f (L.expressionEvaluates span x)))
          (trans (linearTermAgreement f g lf lg eq (L.expressionFor span x))
            (cong g (L.expressionEvaluates span x)))

      record Bilinear (f : A.WeightTwo → A.WeightTwo → T) : Set where
        field
          linearLeft : (y : A.WeightTwo) → Linear (λ x → f x y)
          linearRight : (x : A.WeightTwo) → Linear (f x)
      open Bilinear

      -- Use f = toGriess (sourceModeOne x y), g = canonicalModeOne
      -- (toGriess x) (toGriess y). These are independently interpreted
      -- source operations, not the same function named twice.
      basisPairAgreementIsWholeProduct :
        (f g : A.WeightTwo → A.WeightTwo → T) →
        Bilinear f → Bilinear g →
        ((i j : Fin 196884) →
          f (L.basisState span i) (L.basisState span j) ≡
          g (L.basisState span i) (L.basisState span j)) →
        (x y : A.WeightTwo) → f x y ≡ g x y
      basisPairAgreementIsWholeProduct f g bf bg eq x y =
        linearAgreement (λ t → f t y) (λ t → g t y)
          (linearLeft bf y) (linearLeft bg y)
          (λ i → linearAgreement
            (f (L.basisState span i)) (g (L.basisState span i))
            (linearRight bf (L.basisState span i))
            (linearRight bg (L.basisState span i)) (eq i) y) x
