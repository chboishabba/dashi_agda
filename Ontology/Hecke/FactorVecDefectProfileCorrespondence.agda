module Ontology.Hecke.FactorVecDefectProfileCorrespondence where

open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)

open import MonsterOntos using
  (SSP; p2; p3; p5; p7; p11; p13; p17; p19; p23; p29; p31; p41; p47; p59; p71)
open import Ontology.GodelLattice using (FactorVec)
open import Ontology.GodelLattice renaming (v15 to mkVec15)
open import Ontology.Hecke.FactorVecMultiLaneTransport using (pairMode)
open import Ontology.Hecke.FactorVecMultiLaneDefects using
  (PairDefectClass; Stable; Repatterning; Contractive; Expansive;
   PairDefectProfile; pairDefectProfileOf)
import Ontology.Hecke.DefectCorrespondenceRepresentation as HD

------------------------------------------------------------------------
-- Lift the defect-derived correspondence from coarse defect classes to the
-- full finite defect profile already present on the representation layer.

defectProfileAt : SSP → SSP → FactorVec → PairDefectProfile
defectProfileAt q p v = pairDefectProfileOf (pairMode q p) v

defectProfileCorrespondence : SSP → FactorVec → Ontology.GodelLattice.Vec15 PairDefectProfile
defectProfileCorrespondence p v =
  mkVec15
    (defectProfileAt p2  p v)
    (defectProfileAt p3  p v)
    (defectProfileAt p5  p v)
    (defectProfileAt p7  p v)
    (defectProfileAt p11 p v)
    (defectProfileAt p13 p v)
    (defectProfileAt p17 p v)
    (defectProfileAt p19 p v)
    (defectProfileAt p23 p v)
    (defectProfileAt p29 p v)
    (defectProfileAt p31 p v)
    (defectProfileAt p41 p v)
    (defectProfileAt p47 p v)
    (defectProfileAt p59 p v)
    (defectProfileAt p71 p v)

factorVecDefectProfileHecke : HD.PrimeDefectHeckeOn FactorVec PairDefectProfile
factorVecDefectProfileHecke = record
  { correspondence = defectProfileCorrespondence
  }

defectClassWeight : PairDefectClass → Nat
defectClassWeight Stable       = zero
defectClassWeight Repatterning = suc zero
defectClassWeight Contractive  = suc (suc zero)
defectClassWeight Expansive    = suc (suc (suc zero))

profileWeight : PairDefectProfile → Nat
profileWeight prof =
  PairDefectProfile.drift prof + defectClassWeight (PairDefectProfile.defect prof)

factorVecDefectProfileAverage : SSP → FactorVec → Nat
factorVecDefectProfileAverage =
  HD.PrimeDefectHeckeOn.operator factorVecDefectProfileHecke profileWeight
