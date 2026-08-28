module DASHI.Foundations.BishopBaselReciprocalSquareConvergenceExact where

------------------------------------------------------------------------
-- CONSTRUCTIVE CONVERGENCE OF THE BASEL SERIES
--
-- This module proves convergence only; it does not identify the limit.
--
--   a_n = 1/(n+1)^2
--
-- is eventually dominated by the telescoping positive majorant
--
--   b_0 = 1,
--   b_n = 1/n - 1/(n+1)  (n>=1).
--
-- Hence sum a_n converges by the pinned Bishop comparison theorem.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc; _*_)
open import Data.Integer.Base as ℤ using (+_)
open import Data.Integer.Solver renaming (module +-*-Solver to ℤSolver)
open ℤSolver using (solve; _:+_; _:*_; con; _:=_)
import Data.Nat.Properties as NatP
open import Data.Rational.Unnormalised as ℚ using
  (ℚᵘ; 0ℚᵘ; 1ℚᵘ; _/_; _-_; _≤_)
import Data.Rational.Unnormalised.Properties as ℚP

import ExtraProperties as Extra
import Real as BishopReal
import RealProperties as BishopP
import Sequence as BishopSequence

import DASHI.Foundations.BishopExponentialSeriesConvergenceExact as Exp
open import DASHI.Physics.YangMills.CompactLieProofLevel

embed : ℚᵘ → BishopReal.ℝ
embed = BishopReal._⋆

reciprocalPositiveNat : Nat → ℚᵘ
reciprocalPositiveNat n = + 1 / suc n

baselRationalTerm : Nat → ℚᵘ
baselRationalTerm n =
  + 1 / (suc n * suc n)

baselTerm : Nat → BishopReal.ℝ
baselTerm n = embed (baselRationalTerm n)

telescopingRationalTerm : Nat → ℚᵘ
telescopingRationalTerm zero = 1ℚᵘ
telescopingRationalTerm (suc n) =
  (+ 1 / suc n) ℚ.- (+ 1 / suc (suc n))

telescopingTerm : Nat → BishopReal.ℝ
telescopingTerm n = embed (telescopingRationalTerm n)

------------------------------------------------------------------------
-- Rational finite algebra.

telescopingSuccessorAsProductReciprocal :
  ∀ n →
  telescopingRationalTerm (suc n)
  ℚ.≃
  (+ 1 / (suc n * suc (suc n)))
telescopingSuccessorAsProductReciprocal n =
  ℚ.*≡*
    (solve 1
      (λ m →
        (((m :* (con (+ 1) :+ m))
           :- (m :* m))
          :* (m :* (con (+ 1) :+ m)))
        :=
        ((con (+ 1) :* (m :* (con (+ 1) :+ m)))
          :* ((m :* (con (+ 1) :+ m)))))
      refl
      (+ suc n))
  where
    infixl 6 _:-_
    _:-_ = λ a b → a :+ (con (-[1+ 0]) :* b)

successorSquareDenominatorAboveProduct :
  ∀ n →
  suc n * suc (suc n)
  NatP.≤ suc (suc n) * suc (suc n)
successorSquareDenominatorAboveProduct n =
  NatP.*-monoˡ-≤ (suc (suc n)) (NatP.n≤1+n (suc n))

baselBelowTelescopingRational :
  ∀ n →
  baselRationalTerm (suc n)
  ℚ.≤ telescopingRationalTerm (suc n)
baselBelowTelescopingRational n =
  ℚP.≤-respʳ-≃
    (ℚP.≃-sym (telescopingSuccessorAsProductReciprocal n))
    (Extra.q≤r⇒+p/r≤+p/q
      1
      (suc n * suc (suc n))
      (suc (suc n) * suc (suc n))
      (successorSquareDenominatorAboveProduct n))

baselTermNonnegative : ∀ n → BishopReal.NonNegative (baselTerm n)
baselTermNonnegative n =
  BishopP.0≤x⇒nonNegx
    (BishopP.p≤q⇒p⋆≤q⋆
      0ℚᵘ (baselRationalTerm n)
      (ℚP.nonNegative⁻¹ (baselRationalTerm n)))

absoluteBaselTerm : ∀ n →
  BishopReal._≃_ (BishopReal.∣ baselTerm n ∣) (baselTerm n)
absoluteBaselTerm n =
  BishopP.nonNegx⇒∣x∣≃x (baselTermNonnegative n)

baselBelowTelescoping :
  ∀ n →
  BishopReal._≤_ (baselTerm (suc n)) (telescopingTerm (suc n))
baselBelowTelescoping n =
  BishopP.p≤q⇒p⋆≤q⋆
    (baselRationalTerm (suc n))
    (telescopingRationalTerm (suc n))
    (baselBelowTelescopingRational n)

------------------------------------------------------------------------
-- The reciprocal sequence 1/(n+1) tends to zero.

reciprocalSequence : Nat → BishopReal.ℝ
reciprocalSequence n = embed (reciprocalPositiveNat n)

reciprocalSequenceConvergesZero :
  BishopSequence._ConvergesTo_
    reciprocalSequence BishopReal.0ℝ
reciprocalSequenceConvergesZero =
  BishopSequence.con* λ {(suc k-1) →
    k-1 , λ {(suc n-1) n≥k →
      let
        k = suc k-1
        n = suc n-1
        reciprocalOrder :
          reciprocalPositiveNat n ℚ.≤ (+ 1 / k)
        reciprocalOrder =
          Extra.q≤r⇒+p/r≤+p/q
            1 k (suc n)
            (NatP.≤-trans n≥k (NatP.n≤1+n n))

        embeddedOrder :
          BishopReal._≤_
            (reciprocalSequence n)
            (embed (+ 1 / k))
        embeddedOrder =
          BishopP.p≤q⇒p⋆≤q⋆
            (reciprocalPositiveNat n) (+ 1 / k) reciprocalOrder
      in
      BishopP.≤-respˡ-≃
        (BishopP.≃-trans
          (BishopP.∣-∣-cong
            (BishopP.+-identityʳ (reciprocalSequence n)))
          (absoluteReciprocal n))
        embeddedOrder }}
  where
    reciprocalNonnegative : ∀ n →
      BishopReal.NonNegative (reciprocalSequence n)
    reciprocalNonnegative n =
      BishopP.0≤x⇒nonNegx
        (BishopP.p≤q⇒p⋆≤q⋆
          0ℚᵘ (reciprocalPositiveNat n)
          (ℚP.nonNegative⁻¹ (reciprocalPositiveNat n)))

    absoluteReciprocal : ∀ n →
      BishopReal._≃_
        (BishopReal.∣ reciprocalSequence n ∣)
        (reciprocalSequence n)
    absoluteReciprocal n =
      BishopP.nonNegx⇒∣x∣≃x (reciprocalNonnegative n)

------------------------------------------------------------------------
-- Telescoping partial sums equal 2 - 1/N after the first term.

partialTelescopingClosedForm :
  ∀ n →
  BishopReal._≃_
    (BishopSequence.SeriesOf telescopingTerm (suc n))
    (BishopReal._-_
      (embed (+ 2 / 1))
      (reciprocalSequence n))
partialTelescopingClosedForm zero =
  let open BishopP.ℝ-Solver
  in solve 0
    ((Κ 0ℚᵘ ⊕ Κ 1ℚᵘ)
      ⊜ Κ (+ 2 / 1) ⊖ Κ (+ 1 / 1))
    BishopP.≃-refl
partialTelescopingClosedForm (suc n) =
  let open BishopP.ℝ-Solver
  in
  BishopP.≃-trans
    (BishopP.+-cong
      (partialTelescopingClosedForm n)
      (BishopP.⋆-cong
        (telescopingSuccessorAsProductReciprocal n)))
    (solve 2
      (λ old next →
        (Κ (+ 2 / 1) ⊖ old)
          ⊕ (old ⊖ next)
        ⊜ Κ (+ 2 / 1) ⊖ next)
      BishopP.≃-refl
      (reciprocalSequence n)
      (reciprocalSequence (suc n)))

telescopingSeriesConvergent :
  BishopSequence._isConvergent
    (BishopSequence.SeriesOf telescopingTerm)
telescopingSeriesConvergent =
  let
    two = embed (+ 2 / 1)
    closedForm : Nat → BishopReal.ℝ
    closedForm n = BishopReal._-_ two (reciprocalSequence n)

    closedConverges : BishopSequence._isConvergent closedForm
    closedConverges =
      two ,
      BishopSequence.xₙ→x∧x≃y⇒xₙ→y
        (BishopSequence.xₙ+yₙ→x₀+y₀
          (two , BishopSequence.xₙ≃c⇒xₙ→c
            (λ {(suc n) → BishopP.≃-refl}))
          (BishopReal.- BishopReal.0ℝ ,
            BishopSequence.-xₙ→-x₀
              (BishopReal.0ℝ , reciprocalSequenceConvergesZero)))
        (let open BishopP.ℝ-Solver
         in solve 0
           (Κ (+ 2 / 1) ⊕ (⊝ Κ 0ℚᵘ) ⊜ Κ (+ 2 / 1))
           BishopP.≃-refl)

    shiftedPartials : Nat → BishopReal.ℝ
    shiftedPartials n =
      BishopSequence.SeriesOf telescopingTerm (suc n)

    shiftedConverges : BishopSequence._ConvergesTo_ shiftedPartials two
    shiftedConverges =
      BishopSequence.xₙ≃yₙ∧xₙ→x₀⇒yₙ→x₀
        (λ {(suc n) →
          BishopP.≃-symm (partialTelescopingClosedForm (suc n))})
        closedConverges
  in
  two ,
  BishopSequence.fast-xₙ⊆yₙ∧yₙ→y⇒xₙ→y
    (BishopSequence.shift-is-subsequence
      (BishopSequence.SeriesOf telescopingTerm) 1)
    (two , shiftedConverges)

------------------------------------------------------------------------
-- Bishop comparison theorem gives convergence of the Basel series.

baselSeriesConvergent :
  BishopSequence._isConvergent
    (BishopSequence.SeriesOf baselTerm)
baselSeriesConvergent =
  BishopSequence.proposition-3-5
    telescopingSeriesConvergent
    (0 , λ {(suc n) n≥1 →
      BishopP.≤-respˡ-≃
        (absoluteBaselTerm (suc n))
        (baselBelowTelescoping n)})

baselLimit : BishopReal.ℝ
baselLimit = BishopSequence.lim baselSeriesConvergent

bishopBaselReciprocalSquareConvergenceLevel : ProofLevel
bishopBaselReciprocalSquareConvergenceLevel = machineChecked
