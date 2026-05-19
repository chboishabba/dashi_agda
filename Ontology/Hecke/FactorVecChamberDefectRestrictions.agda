module Ontology.Hecke.FactorVecChamberDefectRestrictions where

open import Agda.Builtin.Bool     using (false)
open import Agda.Builtin.Equality using (_≡_)
open import Relation.Binary.PropositionalEquality using (sym; trans)

open import Ontology.GodelLattice using (FactorVec)
open import Ontology.Hecke.FactorVecMultiLaneTransport using (PairMode; pairLegal)
open import Ontology.Hecke.FactorVecTransportChambers using
  (samePairChamber; samePairChamber-respects-legal)
open import Ontology.Hecke.FactorVecMultiLaneDefects using
  (PairDefectClass; Stable; pairDefectClass; pairDefectClass-illegal)

------------------------------------------------------------------------
-- Exact chamber agreement does not determine every defect outcome, but it
-- does force stability on modes that are illegal throughout the chamber.

samePairChamber-illegal-right :
  ∀ m x y →
  samePairChamber x y →
  pairLegal m x ≡ false →
  pairLegal m y ≡ false
samePairChamber-illegal-right m x y chamberEq illegalLeft =
  trans (sym (samePairChamber-respects-legal m x y chamberEq)) illegalLeft

samePairChamber-forces-stable-defect :
  ∀ m x y →
  samePairChamber x y →
  pairLegal m x ≡ false →
  pairDefectClass m y ≡ Stable
samePairChamber-forces-stable-defect m x y chamberEq illegalLeft =
  pairDefectClass-illegal m y
    (samePairChamber-illegal-right m x y chamberEq illegalLeft)
