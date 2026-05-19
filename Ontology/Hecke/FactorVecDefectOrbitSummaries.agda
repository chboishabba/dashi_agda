module Ontology.Hecke.FactorVecDefectOrbitSummaries where

open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Agda.Builtin.Equality using (_≡_)

open import MonsterOntos using
  (SSP; p2; p3; p5; p7; p11; p13; p17; p19; p23; p29; p31; p41; p47; p59; p71)
open import Ontology.GodelLattice using (FactorVec)
open import Ontology.GodelLattice renaming (Vec15 to Vec15' ; v15 to mkVec15)
open import Ontology.Hecke.FactorVecMultiLaneDefects using
  (PairDefectClass; Stable; Repatterning; Contractive; Expansive;
   PairDefectProfile)
open import Ontology.Hecke.FactorVecSignedScan using (SignedMotif; Rigid; Mixed; Flowing)
open import Ontology.Hecke.FactorVecDefectProfileCorrespondence using
  (defectProfileCorrespondence)
import Ontology.Hecke.DefectCorrespondenceRepresentation as HD

------------------------------------------------------------------------
-- Orbit-style summaries built from the full defect-profile correspondence.
-- This does not claim any new invariance law yet; it supplies a richer target
-- for orbit-style clustering than the raw full profile fiber.

countProfileClass : PairDefectClass → PairDefectProfile → Nat
countProfileClass c prof with PairDefectProfile.defect prof
... | d = countClass c d
  where
  countClass : PairDefectClass → PairDefectClass → Nat
  countClass Stable       Stable       = suc zero
  countClass Stable       _            = zero
  countClass Repatterning Repatterning = suc zero
  countClass Repatterning _            = zero
  countClass Contractive  Contractive  = suc zero
  countClass Contractive  _            = zero
  countClass Expansive    Expansive    = suc zero
  countClass Expansive    _            = zero

motifChanged : PairDefectProfile → Nat
motifChanged prof with PairDefectProfile.preMotif prof | PairDefectProfile.postMotif prof
... | pre | post = motifDiff pre post
  where
  motifDiff : SignedMotif → SignedMotif → Nat
  motifDiff Rigid   Rigid   = zero
  motifDiff Mixed   Mixed   = zero
  motifDiff Flowing Flowing = zero
  motifDiff _       _       = suc zero

profileDrift : PairDefectProfile → Nat
profileDrift = PairDefectProfile.drift

record DefectOrbitSummary : Set where
  constructor defectOrbitSummary
  field
    forcedStableCount : Nat
    motifChangeCount  : Nat
    totalDrift        : Nat
    repatterningCount : Nat
    contractiveCount  : Nat
    expansiveCount    : Nat

profileSummaryAt : SSP → FactorVec → DefectOrbitSummary
profileSummaryAt p v = defectOrbitSummary
  (HD.PrimeDefectHeckeOn.operator
    (record { correspondence = defectProfileCorrespondence })
    (countProfileClass Stable) p v)
  (HD.PrimeDefectHeckeOn.operator
    (record { correspondence = defectProfileCorrespondence })
    motifChanged p v)
  (HD.PrimeDefectHeckeOn.operator
    (record { correspondence = defectProfileCorrespondence })
    profileDrift p v)
  (HD.PrimeDefectHeckeOn.operator
    (record { correspondence = defectProfileCorrespondence })
    (countProfileClass Repatterning) p v)
  (HD.PrimeDefectHeckeOn.operator
    (record { correspondence = defectProfileCorrespondence })
    (countProfileClass Contractive) p v)
  (HD.PrimeDefectHeckeOn.operator
    (record { correspondence = defectProfileCorrespondence })
    (countProfileClass Expansive) p v)

profileSummaryFamily : FactorVec → Vec15' DefectOrbitSummary
profileSummaryFamily v =
  mkVec15
    (profileSummaryAt p2  v)
    (profileSummaryAt p3  v)
    (profileSummaryAt p5  v)
    (profileSummaryAt p7  v)
    (profileSummaryAt p11 v)
    (profileSummaryAt p13 v)
    (profileSummaryAt p17 v)
    (profileSummaryAt p19 v)
    (profileSummaryAt p23 v)
    (profileSummaryAt p29 v)
    (profileSummaryAt p31 v)
    (profileSummaryAt p41 v)
    (profileSummaryAt p47 v)
    (profileSummaryAt p59 v)
    (profileSummaryAt p71 v)

sameOrbitSummary : FactorVec → FactorVec → Set
sameOrbitSummary x y = profileSummaryFamily x ≡ profileSummaryFamily y
