module Ontology.Hecke.FactorVecChamberDefectCorrespondence where

open import Agda.Builtin.Bool     using (false)
open import Agda.Builtin.Equality using (_≡_)

open import MonsterOntos using (SSP)
open import Ontology.GodelLattice using (FactorVec)
open import Ontology.Hecke.FactorVecMultiLaneTransport using (pairMode; pairLegal)
open import Ontology.Hecke.FactorVecTransportChambers using (samePairChamber)
open import Ontology.Hecke.FactorVecChamberDefectRestrictions using
  (samePairChamber-forces-stable-defect)
open import Ontology.Hecke.FactorVecDefectCorrespondence using
  (defectAt)
open import Ontology.Hecke.FactorVecMultiLaneDefects using (Stable)

------------------------------------------------------------------------
-- First chamber-side restriction stated directly on the defect-derived
-- correspondence entries.

samePairChamber-forces-stable-defectAt :
  ∀ q p x y →
  samePairChamber x y →
  pairLegal (pairMode q p) x ≡ false →
  defectAt q p y ≡ Stable
samePairChamber-forces-stable-defectAt q p x y chamberEq illegalLeft =
  samePairChamber-forces-stable-defect (pairMode q p) x y chamberEq illegalLeft
