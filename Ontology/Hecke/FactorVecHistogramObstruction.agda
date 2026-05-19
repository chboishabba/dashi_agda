module Ontology.Hecke.FactorVecHistogramObstruction where

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (cong)

open import MonsterOntos using
  (SSP; p2; p3; p5; p7; p11; p13; p17; p19; p23; p29; p31; p41; p47; p59; p71)
open import Ontology.GodelLattice using (FactorVec)
open import Ontology.GodelLattice renaming (v15 to mkVec15)
open import Ontology.Hecke.FactorVecMultiLaneTransport using
  (PairMode; pairMode; pairLegal)
open import Ontology.Hecke.FactorVecDefectHistograms using (DefectHistogram; defectHistogramOf)
open import Ontology.Hecke.SignedTransportObstruction using (suc-injective; nat-not-suc-self)

------------------------------------------------------------------------
-- Stronger boundary: exact chamber agreement does not force the full defect
-- histogram. The first invariant histogram component is the illegal /
-- forced-stable count only.

samePairLegalEverywhere : FactorVec → FactorVec → Set
samePairLegalEverywhere x y = ∀ m → pairLegal m x ≡ pairLegal m y

counterexample-x : FactorVec
counterexample-x =
  mkVec15 zero zero zero (suc (suc zero))
          zero zero zero zero zero zero zero zero zero zero zero

counterexample-y : FactorVec
counterexample-y =
  mkVec15 zero zero zero (suc (suc (suc zero)))
          zero zero zero zero zero zero zero zero zero zero zero

counterexample-samePairLegalEverywhere :
  samePairLegalEverywhere counterexample-x counterexample-y
counterexample-samePairLegalEverywhere (pairMode p2  second) = refl
counterexample-samePairLegalEverywhere (pairMode p3  second) = refl
counterexample-samePairLegalEverywhere (pairMode p5  second) = refl
counterexample-samePairLegalEverywhere (pairMode p7 p7) = refl
counterexample-samePairLegalEverywhere (pairMode p7 p11) = refl
counterexample-samePairLegalEverywhere (pairMode p7 p2) = refl
counterexample-samePairLegalEverywhere (pairMode p7 p3) = refl
counterexample-samePairLegalEverywhere (pairMode p7 p5) = refl
counterexample-samePairLegalEverywhere (pairMode p7 p13) = refl
counterexample-samePairLegalEverywhere (pairMode p7 p17) = refl
counterexample-samePairLegalEverywhere (pairMode p7 p19) = refl
counterexample-samePairLegalEverywhere (pairMode p7 p23) = refl
counterexample-samePairLegalEverywhere (pairMode p7 p29) = refl
counterexample-samePairLegalEverywhere (pairMode p7 p31) = refl
counterexample-samePairLegalEverywhere (pairMode p7 p41) = refl
counterexample-samePairLegalEverywhere (pairMode p7 p47) = refl
counterexample-samePairLegalEverywhere (pairMode p7 p59) = refl
counterexample-samePairLegalEverywhere (pairMode p7 p71) = refl
counterexample-samePairLegalEverywhere (pairMode p11 second) = refl
counterexample-samePairLegalEverywhere (pairMode p13 second) = refl
counterexample-samePairLegalEverywhere (pairMode p17 second) = refl
counterexample-samePairLegalEverywhere (pairMode p19 second) = refl
counterexample-samePairLegalEverywhere (pairMode p23 second) = refl
counterexample-samePairLegalEverywhere (pairMode p29 second) = refl
counterexample-samePairLegalEverywhere (pairMode p31 second) = refl
counterexample-samePairLegalEverywhere (pairMode p41 second) = refl
counterexample-samePairLegalEverywhere (pairMode p47 second) = refl
counterexample-samePairLegalEverywhere (pairMode p59 second) = refl
counterexample-samePairLegalEverywhere (pairMode p71 second) = refl

counterexample-histogram-x :
  defectHistogramOf p7 counterexample-x
    ≡
  Ontology.Hecke.FactorVecDefectHistograms.defectHistogram
    (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))))))
    (suc zero)
    zero
    zero
counterexample-histogram-x = refl

counterexample-histogram-y :
  defectHistogramOf p7 counterexample-y
    ≡
  Ontology.Hecke.FactorVecDefectHistograms.defectHistogram
    (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))))))
    zero
    zero
    (suc zero)
counterexample-histogram-y = refl

counterexample-histograms-not-equal :
  defectHistogramOf p7 counterexample-x
    ≡
  defectHistogramOf p7 counterexample-y
    →
  ⊥
counterexample-histograms-not-equal eq
  rewrite counterexample-histogram-x
        | counterexample-histogram-y with eq
... | ()
