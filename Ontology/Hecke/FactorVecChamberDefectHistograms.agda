module Ontology.Hecke.FactorVecChamberDefectHistograms where

open import Agda.Builtin.Equality using (_≡_; refl)

open import MonsterOntos using
  (SSP; p2; p3; p5; p7; p11; p13; p17; p19; p23; p29; p31; p41; p47; p59; p71)
open import Ontology.GodelLattice using (FactorVec)
open import Ontology.Hecke.FactorVecMultiLaneTransport using (pairMode; pairLegal)
open import Ontology.Hecke.FactorVecTransportChambers using
  (samePairChamber; samePairChamber-respects-legal)
open import Ontology.Hecke.FactorVecDefectHistograms using
  (countFalse; illegalCount; forcedStableCount)

------------------------------------------------------------------------
-- First histogram-level chamber law: exact chamber agreement fixes the
-- legality mask for every `(q , p)` entry, so the illegal / forced-stable
-- count is chamber-invariant.

countFalse-respects :
  ∀ {b₁ b₂} →
  b₁ ≡ b₂ →
  countFalse b₁ ≡ countFalse b₂
countFalse-respects refl = refl

samePairChamber-preserves-illegalCount :
  ∀ p x y →
  samePairChamber x y →
  illegalCount p x ≡ illegalCount p y
samePairChamber-preserves-illegalCount p x y chamberEq
  rewrite countFalse-respects (samePairChamber-respects-legal (pairMode p2  p) x y chamberEq)
        | countFalse-respects (samePairChamber-respects-legal (pairMode p3  p) x y chamberEq)
        | countFalse-respects (samePairChamber-respects-legal (pairMode p5  p) x y chamberEq)
        | countFalse-respects (samePairChamber-respects-legal (pairMode p7  p) x y chamberEq)
        | countFalse-respects (samePairChamber-respects-legal (pairMode p11 p) x y chamberEq)
        | countFalse-respects (samePairChamber-respects-legal (pairMode p13 p) x y chamberEq)
        | countFalse-respects (samePairChamber-respects-legal (pairMode p17 p) x y chamberEq)
        | countFalse-respects (samePairChamber-respects-legal (pairMode p19 p) x y chamberEq)
        | countFalse-respects (samePairChamber-respects-legal (pairMode p23 p) x y chamberEq)
        | countFalse-respects (samePairChamber-respects-legal (pairMode p29 p) x y chamberEq)
        | countFalse-respects (samePairChamber-respects-legal (pairMode p31 p) x y chamberEq)
        | countFalse-respects (samePairChamber-respects-legal (pairMode p41 p) x y chamberEq)
        | countFalse-respects (samePairChamber-respects-legal (pairMode p47 p) x y chamberEq)
        | countFalse-respects (samePairChamber-respects-legal (pairMode p59 p) x y chamberEq)
        | countFalse-respects (samePairChamber-respects-legal (pairMode p71 p) x y chamberEq) = refl

samePairChamber-preserves-forcedStableCount :
  ∀ p x y →
  samePairChamber x y →
  forcedStableCount p x ≡ forcedStableCount p y
samePairChamber-preserves-forcedStableCount p x y chamberEq =
  samePairChamber-preserves-illegalCount p x y chamberEq

