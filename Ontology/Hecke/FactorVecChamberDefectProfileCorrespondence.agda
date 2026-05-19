module Ontology.Hecke.FactorVecChamberDefectProfileCorrespondence where

open import Agda.Builtin.Bool using (false)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (zero)

open import MonsterOntos using (SSP)
open import Ontology.GodelLattice using (FactorVec)
open import Ontology.Hecke.FactorVecMultiLaneTransport using (pairMode; pairLegal)
open import Ontology.Hecke.FactorVecTransportChambers using (samePairChamber)
open import Ontology.Hecke.FactorVecChamberDefectRestrictions using
  (samePairChamber-illegal-right)
open import Ontology.Hecke.FactorVecDefectProfileCorrespondence using
  (defectProfileAt)
open import Ontology.Hecke.FactorVecMultiLaneDefects using
  (PairDefectClass; Stable; PairDefectProfile;
   pairPrePostSignature-illegal; pairSignatureDrift-illegal;
   pairPrePostMotif-illegal; pairDefectClass-illegal)

------------------------------------------------------------------------
-- Chamber-side restriction lifted from coarse defect classes to the full
-- defect-profile correspondence. Illegal entries stay fully rigid: no
-- signature drift, no motif change, and the coarse defect class is Stable.

samePairChamber-forces-profileSignatureFixedAt :
  ∀ q p x y →
  samePairChamber x y →
  pairLegal (pairMode q p) x ≡ false →
  PairDefectProfile.preSignature (defectProfileAt q p y)
    ≡
  PairDefectProfile.postSignature (defectProfileAt q p y)
samePairChamber-forces-profileSignatureFixedAt q p x y chamberEq illegalLeft =
  pairPrePostSignature-illegal
    (pairMode q p)
    y
    (samePairChamber-illegal-right
      (pairMode q p) x y chamberEq illegalLeft)

samePairChamber-forces-profileDriftZeroAt :
  ∀ q p x y →
  samePairChamber x y →
  pairLegal (pairMode q p) x ≡ false →
  PairDefectProfile.drift (defectProfileAt q p y) ≡ zero
samePairChamber-forces-profileDriftZeroAt q p x y chamberEq illegalLeft =
  pairSignatureDrift-illegal
    (pairMode q p)
    y
    (samePairChamber-illegal-right
      (pairMode q p) x y chamberEq illegalLeft)

samePairChamber-forces-profileMotifFixedAt :
  ∀ q p x y →
  samePairChamber x y →
  pairLegal (pairMode q p) x ≡ false →
  PairDefectProfile.preMotif (defectProfileAt q p y)
    ≡
  PairDefectProfile.postMotif (defectProfileAt q p y)
samePairChamber-forces-profileMotifFixedAt q p x y chamberEq illegalLeft =
  pairPrePostMotif-illegal
    (pairMode q p)
    y
    (samePairChamber-illegal-right
      (pairMode q p) x y chamberEq illegalLeft)

samePairChamber-forces-profileStableAt :
  ∀ q p x y →
  samePairChamber x y →
  pairLegal (pairMode q p) x ≡ false →
  PairDefectProfile.defect (defectProfileAt q p y) ≡ Stable
samePairChamber-forces-profileStableAt q p x y chamberEq illegalLeft =
  pairDefectClass-illegal
    (pairMode q p)
    y
    (samePairChamber-illegal-right
      (pairMode q p) x y chamberEq illegalLeft)
