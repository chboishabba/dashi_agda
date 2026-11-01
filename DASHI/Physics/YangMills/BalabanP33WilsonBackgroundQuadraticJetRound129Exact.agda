{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanP33WilsonBackgroundQuadraticJetRound129Exact where

------------------------------------------------------------------------
-- ROUND129 A1: EXACT NONCOMMUTATIVE d_s d_t^2 WILSON PRODUCT JET
--
-- Primary sources:
-- Kenneth G. Wilson, Phys. Rev. D 10 (1974), 2445--2459.
-- Tadeusz Bałaban, CMP 99 (1985), 389--434. DOI 10.1007/BF01240355.
--
-- The Wilson part of A1.1 is D_background of the physical Wilson Hessian.
-- Rather than leave that derivative abstract, this module extends the existing
-- rational quaternion t^2 product jet by one background derivative s.  The
-- recursion is the exact noncommutative Leibniz rule for d_s d_t^2.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.List.Base using (map; _++_; length)
open import Data.Rational.Base as ℚ using (ℚ; -_)
open import Relation.Binary.PropositionalEquality using (cong; trans; sym)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionWilsonJetExact as Jet

record MixedFactorJet : Set where
  constructor mixedFactorJet
  field
    value background fluctuation fluctuationSecond : Jet.RationalQuaternion
    backgroundFluctuation backgroundFluctuationSecond : Jet.RationalQuaternion
open MixedFactorJet public

valueProduct : List MixedFactorJet → Jet.RationalQuaternion
valueProduct [] = Jet.oneQ
valueProduct (f ∷ fs) = value f Jet.*q valueProduct fs

backgroundProduct : List MixedFactorJet → Jet.RationalQuaternion
backgroundProduct [] = Jet.zeroQ
backgroundProduct (f ∷ fs) =
  (background f Jet.*q valueProduct fs)
  Jet.+q (value f Jet.*q backgroundProduct fs)

fluctuationProduct : List MixedFactorJet → Jet.RationalQuaternion
fluctuationProduct [] = Jet.zeroQ
fluctuationProduct (f ∷ fs) =
  (fluctuation f Jet.*q valueProduct fs)
  Jet.+q (value f Jet.*q fluctuationProduct fs)

fluctuationSecondProduct : List MixedFactorJet → Jet.RationalQuaternion
fluctuationSecondProduct [] = Jet.zeroQ
fluctuationSecondProduct (f ∷ fs) =
  (fluctuationSecond f Jet.*q valueProduct fs)
  Jet.+q
    ((fluctuation f Jet.*q fluctuationProduct fs)
    Jet.+q ((fluctuation f Jet.*q fluctuationProduct fs)
    Jet.+q (value f Jet.*q fluctuationSecondProduct fs)))

backgroundFluctuationProduct : List MixedFactorJet → Jet.RationalQuaternion
backgroundFluctuationProduct [] = Jet.zeroQ
backgroundFluctuationProduct (f ∷ fs) =
  (backgroundFluctuation f Jet.*q valueProduct fs)
  Jet.+q
    ((background f Jet.*q fluctuationProduct fs)
    Jet.+q ((fluctuation f Jet.*q backgroundProduct fs)
    Jet.+q (value f Jet.*q backgroundFluctuationProduct fs)))

backgroundFluctuationSecondProduct : List MixedFactorJet → Jet.RationalQuaternion
backgroundFluctuationSecondProduct [] = Jet.zeroQ
backgroundFluctuationSecondProduct (f ∷ fs) =
  (backgroundFluctuationSecond f Jet.*q valueProduct fs)
  Jet.+q
    ((fluctuationSecond f Jet.*q backgroundProduct fs)
    Jet.+q
    ((backgroundFluctuation f Jet.*q fluctuationProduct fs)
    Jet.+q
    ((backgroundFluctuation f Jet.*q fluctuationProduct fs)
    Jet.+q
    ((fluctuation f Jet.*q backgroundFluctuationProduct fs)
    Jet.+q
    ((fluctuation f Jet.*q backgroundFluctuationProduct fs)
    Jet.+q
    ((background f Jet.*q fluctuationSecondProduct fs)
    Jet.+q (value f Jet.*q backgroundFluctuationSecondProduct fs)))))))

-- Explicit atom list, useful for executable finite coefficient evaluation.
backgroundFluctuationSecondTerms : List MixedFactorJet → List Jet.RationalQuaternion
backgroundFluctuationSecondTerms [] = []
backgroundFluctuationSecondTerms (f ∷ fs) =
  (backgroundFluctuationSecond f Jet.*q valueProduct fs)
  ∷ (map (fluctuationSecond f Jet.*q_) (backgroundTerms fs)
    ++ (map (backgroundFluctuation f Jet.*q_) (fluctuationTerms fs)
    ++ (map (backgroundFluctuation f Jet.*q_) (fluctuationTerms fs)
    ++ (map (fluctuation f Jet.*q_) (backgroundFluctuationTerms fs)
    ++ (map (fluctuation f Jet.*q_) (backgroundFluctuationTerms fs)
    ++ (map (background f Jet.*q_) (fluctuationSecondTerms fs)
    ++ map (value f Jet.*q_) (backgroundFluctuationSecondTerms fs))))))
  where
    backgroundTerms : List MixedFactorJet → List Jet.RationalQuaternion
    backgroundTerms [] = []
    backgroundTerms (g ∷ gs) =
      (background g Jet.*q valueProduct gs) ∷ map (value g Jet.*q_) (backgroundTerms gs)

    fluctuationTerms : List MixedFactorJet → List Jet.RationalQuaternion
    fluctuationTerms [] = []
    fluctuationTerms (g ∷ gs) =
      (fluctuation g Jet.*q valueProduct gs) ∷ map (value g Jet.*q_) (fluctuationTerms gs)

    fluctuationSecondTerms : List MixedFactorJet → List Jet.RationalQuaternion
    fluctuationSecondTerms [] = []
    fluctuationSecondTerms (g ∷ gs) =
      (fluctuationSecond g Jet.*q valueProduct gs)
      ∷ (map (fluctuation g Jet.*q_) (fluctuationTerms gs)
        ++ (map (fluctuation g Jet.*q_) (fluctuationTerms gs)
        ++ map (value g Jet.*q_) (fluctuationSecondTerms gs)))

    backgroundFluctuationTerms : List MixedFactorJet → List Jet.RationalQuaternion
    backgroundFluctuationTerms [] = []
    backgroundFluctuationTerms (g ∷ gs) =
      (backgroundFluctuation g Jet.*q valueProduct gs)
      ∷ (map (background g Jet.*q_) (fluctuationTerms gs)
        ++ (map (fluctuation g Jet.*q_) (backgroundTerms gs)
        ++ map (value g Jet.*q_) (backgroundFluctuationTerms gs)))

fourFactors : MixedFactorJet → MixedFactorJet → MixedFactorJet → MixedFactorJet → List MixedFactorJet
fourFactors a b c d = a ∷ b ∷ c ∷ d ∷ []

-- Three labelled derivatives distributed over four ordered factors give 4^3=64
-- Leibniz atoms, with repeated placements retaining their multiplicity.
fourFactorMixedAtomCount : ∀ a b c d →
  length (backgroundFluctuationSecondTerms (fourFactors a b c d)) ≡ 64
fourFactorMixedAtomCount a b c d = refl

wilsonMixedNumerator : List MixedFactorJet → ℚ
wilsonMixedNumerator factors = - Jet.q0 (backgroundFluctuationSecondProduct factors)

wilsonMixedProductJetRound129Level : ProofLevel
wilsonMixedProductJetRound129Level = machineChecked

wilsonMixedFourFactorAtomCountRound129Level : ProofLevel
wilsonMixedFourFactorAtomCountRound129Level = machineChecked

-- Remaining Wilson source seam: instantiate the six factor-jet values from the
-- literal exponential link/background coordinates and identify this recursive
-- coefficient with D_background of the existing physical Wilson Hessian.
literalWilsonMixedFactorInstantiationRound129Level : ProofLevel
literalWilsonMixedFactorInstantiationRound129Level = conditional
