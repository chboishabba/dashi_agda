module Ontology.Hecke.FactorVecDefectHistograms where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)

open import MonsterOntos using
  (SSP; p2; p3; p5; p7; p11; p13; p17; p19; p23; p29; p31; p41; p47; p59; p71)
open import Ontology.GodelLattice using (FactorVec)
open import Ontology.GodelLattice renaming (Vec15 to Vec15' ; v15 to mkVec15)
open import Ontology.Hecke.FactorVecMultiLaneTransport using (pairMode; pairLegal)
open import Ontology.Hecke.FactorVecDefectCorrespondence using (defectCorrespondence)
open import Ontology.Hecke.FactorVecMultiLaneDefects using
  (PairDefectClass; Stable; Repatterning; Contractive; Expansive)
import Ontology.Hecke.DefectCorrespondenceRepresentation as HD

------------------------------------------------------------------------
-- Histogram views of the 15-entry defect correspondence fiber. This keeps the
-- current target modest: extract the data first, then prove chamber-stability
-- only for the forced-stable / illegal component.

countDefect : PairDefectClass → PairDefectClass → Nat
countDefect Stable       Stable       = suc zero
countDefect Stable       _            = zero
countDefect Repatterning Repatterning = suc zero
countDefect Repatterning _            = zero
countDefect Contractive  Contractive  = suc zero
countDefect Contractive  _            = zero
countDefect Expansive    Expansive    = suc zero
countDefect Expansive    _            = zero

record DefectHistogram : Set where
  constructor defectHistogram
  field
    stableCount       : Nat
    repatterningCount : Nat
    contractiveCount  : Nat
    expansiveCount    : Nat

defectHistogramOf : SSP → FactorVec → DefectHistogram
defectHistogramOf p v = defectHistogram
  (HD.PrimeDefectHeckeOn.operator
    (record { correspondence = defectCorrespondence })
    (countDefect Stable) p v)
  (HD.PrimeDefectHeckeOn.operator
    (record { correspondence = defectCorrespondence })
    (countDefect Repatterning) p v)
  (HD.PrimeDefectHeckeOn.operator
    (record { correspondence = defectCorrespondence })
    (countDefect Contractive) p v)
  (HD.PrimeDefectHeckeOn.operator
    (record { correspondence = defectCorrespondence })
    (countDefect Expansive) p v)

countFalse : Bool → Nat
countFalse true  = zero
countFalse false = suc zero

illegalMask : SSP → FactorVec → Vec15' Bool
illegalMask p v =
  mkVec15
    (pairLegal (pairMode p2  p) v)
    (pairLegal (pairMode p3  p) v)
    (pairLegal (pairMode p5  p) v)
    (pairLegal (pairMode p7  p) v)
    (pairLegal (pairMode p11 p) v)
    (pairLegal (pairMode p13 p) v)
    (pairLegal (pairMode p17 p) v)
    (pairLegal (pairMode p19 p) v)
    (pairLegal (pairMode p23 p) v)
    (pairLegal (pairMode p29 p) v)
    (pairLegal (pairMode p31 p) v)
    (pairLegal (pairMode p41 p) v)
    (pairLegal (pairMode p47 p) v)
    (pairLegal (pairMode p59 p) v)
    (pairLegal (pairMode p71 p) v)

illegalCount : SSP → FactorVec → Nat
illegalCount p v = HD.sum15 (HD.map15 countFalse (illegalMask p v))

forcedStableCount : SSP → FactorVec → Nat
forcedStableCount = illegalCount

