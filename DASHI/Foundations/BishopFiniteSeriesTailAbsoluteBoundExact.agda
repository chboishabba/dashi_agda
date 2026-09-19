module DASHI.Foundations.BishopFiniteSeriesTailAbsoluteBoundExact where

------------------------------------------------------------------------
-- FINITE BISHOP SERIES TAIL TRIANGLE INEQUALITY
--
-- DASHI CONTRIBUTION
--
-- For every finite prefix difference,
--
--   | S_(start+count) - S_start |
--       <=
--   S^abs_(start+count) - S^abs_start.
--
-- This is a purely finite theorem.  It is the row-local estimate needed for
-- Cauchy-product wing bounds and introduces no convergence assumption.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
import Data.Nat.Properties as NatP
open import Relation.Binary.PropositionalEquality using (cong)

import Real as BishopReal
import RealProperties as BishopP
import Sequence as BishopSequence

absoluteTerms :
  (Nat → BishopReal.ℝ) →
  Nat → BishopReal.ℝ
absoluteTerms terms index = BishopReal.∣ terms index ∣

finiteTailAbsoluteBound :
  (terms : Nat → BishopReal.ℝ) →
  ∀ start count →
  BishopReal._≤_
    (BishopReal.∣
      BishopReal._-_
        (BishopSequence.SeriesOf terms (start + count))
        (BishopSequence.SeriesOf terms start)
    ∣)
    (BishopReal._-_
      (BishopSequence.SeriesOf
        (absoluteTerms terms)
        (start + count))
      (BishopSequence.SeriesOf
        (absoluteTerms terms)
        start))
finiteTailAbsoluteBound terms start zero =
  BishopP.≤-respʳ-≃
    (BishopP.≃-symm
      (BishopP.nonNegx⇒∣x∣≃x BishopP.nonNeg0))
    (BishopP.≤-respˡ-≃
      (BishopP.∣-∣-cong
        (BishopP.≃-trans
          (BishopP.-‿cong
            (BishopP.≃-refl₂
              (cong
                (BishopSequence.SeriesOf terms)
                (NatP.+-identityʳ start))))
          (BishopP.+-inverseʳ
            (BishopSequence.SeriesOf terms start))))
      (BishopP.≤-respʳ-≃
        (BishopP.≃-trans
          (BishopP.-‿cong
            (BishopP.≃-refl₂
              (cong
                (BishopSequence.SeriesOf (absoluteTerms terms))
                (NatP.+-identityʳ start))))
          (BishopP.+-inverseʳ
            (BishopSequence.SeriesOf (absoluteTerms terms) start)))
        BishopP.≤-refl))
finiteTailAbsoluteBound terms start (suc count) =
  let
    end = start + count
    signedPrefix = BishopSequence.SeriesOf terms end
    signedStart = BishopSequence.SeriesOf terms start
    absolutePrefix =
      BishopSequence.SeriesOf (absoluteTerms terms) end
    absoluteStart =
      BishopSequence.SeriesOf (absoluteTerms terms) start

    signedStep :
      BishopReal._≃_
        (BishopReal._-_
          (BishopSequence.SeriesOf terms (start + suc count))
          signedStart)
        (BishopReal._+_
          (BishopReal._-_ signedPrefix signedStart)
          (terms end))
    signedStep =
      BishopP.≃-trans
        (BishopP.-‿cong
          (BishopP.≃-refl₂
            (cong
              (BishopSequence.SeriesOf terms)
              (NatP.+-suc start count))))
        (let open BishopP.ℝ-Solver in
         solve 3
           (λ prefix term startValue →
             ((prefix ⊕ term) ⊖ startValue)
             ⊜ ((prefix ⊖ startValue) ⊕ term))
           BishopP.≃-refl
           signedPrefix
           (terms end)
           signedStart)

    absoluteStep :
      BishopReal._≃_
        (BishopReal._-_
          (BishopSequence.SeriesOf
            (absoluteTerms terms)
            (start + suc count))
          absoluteStart)
        (BishopReal._+_
          (BishopReal._-_ absolutePrefix absoluteStart)
          (BishopReal.∣ terms end ∣))
    absoluteStep =
      BishopP.≃-trans
        (BishopP.-‿cong
          (BishopP.≃-refl₂
            (cong
              (BishopSequence.SeriesOf (absoluteTerms terms))
              (NatP.+-suc start count))))
        (let open BishopP.ℝ-Solver in
         solve 3
           (λ prefix termAbs startValue →
             ((prefix ⊕ termAbs) ⊖ startValue)
             ⊜ ((prefix ⊖ startValue) ⊕ termAbs))
           BishopP.≃-refl
           absolutePrefix
           (BishopReal.∣ terms end ∣)
           absoluteStart)
  in
  BishopP.≤-respʳ-≃
    (BishopP.≃-symm absoluteStep)
    (BishopP.≤-respˡ-≃
      (BishopP.∣-∣-cong signedStep)
      (BishopP.≤-trans
        (BishopP.∣x+y∣≤∣x∣+∣y∣
          (BishopReal._-_ signedPrefix signedStart)
          (terms end))
        (BishopP.+-mono-≤
          (finiteTailAbsoluteBound terms start count)
          BishopP.≤-refl)))
