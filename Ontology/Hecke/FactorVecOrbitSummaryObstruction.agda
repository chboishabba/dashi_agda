module Ontology.Hecke.FactorVecOrbitSummaryObstruction where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (cong)

open import MonsterOntos using (p7)
open import Ontology.Hecke.FactorVecHistogramObstruction using
  (counterexample-x; counterexample-y; counterexample-samePairLegalEverywhere)
open import Ontology.Hecke.FactorVecDefectOrbitSummaries using
  (DefectOrbitSummary; profileSummaryAt)

------------------------------------------------------------------------
-- Stronger boundary: even the first orbit-style summary is not determined by
-- the full pointwise legality signature alone.

counterexample-orbitSummary-x :
  profileSummaryAt p7 counterexample-x
    ≡
  Ontology.Hecke.FactorVecDefectOrbitSummaries.defectOrbitSummary 14 0 2 1 0 0
counterexample-orbitSummary-x = refl

counterexample-orbitSummary-y :
  profileSummaryAt p7 counterexample-y
    ≡
  Ontology.Hecke.FactorVecDefectOrbitSummaries.defectOrbitSummary 14 0 1 0 0 1
counterexample-orbitSummary-y = refl

counterexample-orbitSummaries-not-equal :
  profileSummaryAt p7 counterexample-x
    ≡
  profileSummaryAt p7 counterexample-y
    →
  ⊥
counterexample-orbitSummaries-not-equal eq
  rewrite counterexample-orbitSummary-x
        | counterexample-orbitSummary-y with eq
... | ()
