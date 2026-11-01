module Ontology.Hecke.FactorVecOrbitForcedStableLowerBound where

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Nat using (_≤_; z≤n; s≤s)
open import Data.Nat.Properties as NatP using (+-mono-≤)

open import MonsterOntos using
  (SSP; p2; p3; p5; p7; p11; p13; p17; p19; p23; p29; p31; p41; p47; p59; p71)
open import Ontology.GodelLattice using (FactorVec)
open import Ontology.Hecke.FactorVecMultiLaneTransport using (pairMode; pairLegal)
open import Ontology.Hecke.FactorVecDefectHistograms as FDH using
  (countFalse; forcedStableCount)
open import Ontology.Hecke.FactorVecDefectOrbitSummaries using
  (DefectOrbitSummary; profileSummaryAt; countProfileClass)
open import Ontology.Hecke.FactorVecDefectProfileCorrespondence using (defectProfileAt)
open import Ontology.Hecke.FactorVecMultiLaneDefects using
  (Stable; pairDefectClass-illegal)

------------------------------------------------------------------------
-- The orbit-summary `forcedStableCount` field counts all Stable profile
-- entries, while the histogram-layer `forcedStableCount` only counts illegal
-- entries. Illegal entries are always Stable, so the histogram count is a
-- lower bound for the orbit-summary field.

illegalEntry≤StableProfile :
  ∀ q p v →
  FDH.countFalse (pairLegal (pairMode q p) v)
    ≤
  countProfileClass Stable (defectProfileAt q p v)
illegalEntry≤StableProfile q p v with pairLegal (pairMode q p) v in legalEq
... | true = z≤n
... | false rewrite pairDefectClass-illegal (pairMode q p) v legalEq = s≤s z≤n

forcedStableCount≤orbitForcedStable :
  ∀ p v →
  forcedStableCount p v
    ≤
  DefectOrbitSummary.forcedStableCount (profileSummaryAt p v)
forcedStableCount≤orbitForcedStable p v =
  NatP.+-mono-≤
    (NatP.+-mono-≤
      (NatP.+-mono-≤
        (NatP.+-mono-≤
          (NatP.+-mono-≤
            (NatP.+-mono-≤
              (NatP.+-mono-≤
                (NatP.+-mono-≤
                  (NatP.+-mono-≤
                    (NatP.+-mono-≤
                      (NatP.+-mono-≤
                        (NatP.+-mono-≤
                          (NatP.+-mono-≤
                            (NatP.+-mono-≤
                              (illegalEntry≤StableProfile p2 p v)
                              (illegalEntry≤StableProfile p3 p v))
                            (illegalEntry≤StableProfile p5 p v))
                          (illegalEntry≤StableProfile p7 p v))
                        (illegalEntry≤StableProfile p11 p v))
                      (illegalEntry≤StableProfile p13 p v))
                    (illegalEntry≤StableProfile p17 p v))
                  (illegalEntry≤StableProfile p19 p v))
                (illegalEntry≤StableProfile p23 p v))
              (illegalEntry≤StableProfile p29 p v))
            (illegalEntry≤StableProfile p31 p v))
          (illegalEntry≤StableProfile p41 p v))
        (illegalEntry≤StableProfile p47 p v))
      (illegalEntry≤StableProfile p59 p v))
    (illegalEntry≤StableProfile p71 p v)
