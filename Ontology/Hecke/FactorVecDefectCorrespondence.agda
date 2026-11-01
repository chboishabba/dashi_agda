module Ontology.Hecke.FactorVecDefectCorrespondence where

open import Agda.Builtin.Nat using (Nat; zero; suc)

open import MonsterOntos using
  (SSP; p2; p3; p5; p7; p11; p13; p17; p19; p23; p29; p31; p41; p47; p59; p71)
open import Ontology.GodelLattice using (FactorVec)
open import Ontology.GodelLattice renaming (v15 to mkVec15)
open import Ontology.Hecke.FactorVecMultiLaneTransport using (PairMode; pairMode)
open import Ontology.Hecke.FactorVecMultiLaneDefects using
  (PairDefectClass; Stable; Repatterning; Contractive; Expansive; pairDefectClass)
import Ontology.Hecke.DefectCorrespondenceRepresentation as HD

------------------------------------------------------------------------
-- For a fixed first prime p and a state v, vary the second prime through the
-- Monster basis and record the resulting defect class. This yields a genuine
-- scan/defect-derived finite correspondence.

defectAt : SSP → SSP → FactorVec → PairDefectClass
defectAt q p v = pairDefectClass (pairMode q p) v

defectCorrespondence : SSP → FactorVec → Ontology.GodelLattice.Vec15 PairDefectClass
defectCorrespondence p v =
  mkVec15
    (defectAt p2  p v)
    (defectAt p3  p v)
    (defectAt p5  p v)
    (defectAt p7  p v)
    (defectAt p11 p v)
    (defectAt p13 p v)
    (defectAt p17 p v)
    (defectAt p19 p v)
    (defectAt p23 p v)
    (defectAt p29 p v)
    (defectAt p31 p v)
    (defectAt p41 p v)
    (defectAt p47 p v)
    (defectAt p59 p v)
    (defectAt p71 p v)

factorVecDefectHecke : HD.PrimeDefectHeckeOn FactorVec PairDefectClass
factorVecDefectHecke = record
  { correspondence = defectCorrespondence
  }

defectWeight : PairDefectClass → Nat
defectWeight Stable       = zero
defectWeight Repatterning = suc zero
defectWeight Contractive  = suc (suc zero)
defectWeight Expansive    = suc (suc (suc zero))

factorVecDefectAverage : SSP → FactorVec → Nat
factorVecDefectAverage =
  HD.PrimeDefectHeckeOn.operator factorVecDefectHecke defectWeight
