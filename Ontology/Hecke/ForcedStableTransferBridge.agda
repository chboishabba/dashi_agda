module Ontology.Hecke.ForcedStableTransferBridge where

open import Agda.Primitive using (Level; lsuc)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Equality using (_≡_)
open import Data.Nat using (_≤_)
open import Data.Nat.Properties as NatP using (≤-trans)

open import MonsterOntos using (SSP)
open import Ontology.GodelLattice using (FactorVec)
open import Ontology.Hecke.FactorVecTransportChambers using (samePairChamber)
open import Ontology.Hecke.FactorVecDefectHistograms using
  (illegalCount; forcedStableCount)
open import Ontology.Hecke.FactorVecDefectOrbitSummaries using
  (DefectOrbitSummary; profileSummaryAt)
open import Ontology.Hecke.FactorVecChamberDefectHistograms using
  (samePairChamber-preserves-illegalCount)
open import Ontology.Hecke.FactorVecOrbitForcedStableLowerBound using
  (forcedStableCount≤orbitForcedStable)

------------------------------------------------------------------------
-- Bridge ladder packaging:
-- 1. exact chamber agreement preserves the chamber-side illegal count;
-- 2. a closure-to-shift bridge may witness a lower bound from that chamber
--    count into the histogram-layer forced-stable count on the transported
--    shift image;
-- 3. the already-proved Hecke-side lower bound then lifts that result to the
--    orbit-summary forced-stable field.

illegalCount-chamber-invariant :
  ∀ p x y →
  samePairChamber x y →
  illegalCount p x ≡ illegalCount p y
illegalCount-chamber-invariant = samePairChamber-preserves-illegalCount

record ForcedStableTransferBridge {ℓ : Level}
                                 (ClosureState : Set ℓ)
                                 : Set (lsuc ℓ) where
  field
    shiftImage : ClosureState → FactorVec
    illegalCountChamber : SSP → ClosureState → Nat

    illegalCount≤forcedStableCountHist :
      ∀ p x →
      illegalCountChamber p x ≤ forcedStableCount p (shiftImage x)

  illegalCount≤forcedStableCountOrbit :
    ∀ p x →
    illegalCountChamber p x
      ≤
    DefectOrbitSummary.forcedStableCount (profileSummaryAt p (shiftImage x))
  illegalCount≤forcedStableCountOrbit p x =
    NatP.≤-trans
      (illegalCount≤forcedStableCountHist p x)
      (forcedStableCount≤orbitForcedStable p (shiftImage x))

  illegalCount≡forcedStableCountHist⇒illegalCount≤forcedStableCountOrbit :
    ∀ p x →
    illegalCountChamber p x ≡ forcedStableCount p (shiftImage x) →
    illegalCountChamber p x
      ≤
    DefectOrbitSummary.forcedStableCount (profileSummaryAt p (shiftImage x))
  illegalCount≡forcedStableCountHist⇒illegalCount≤forcedStableCountOrbit p x eq
    rewrite eq = forcedStableCount≤orbitForcedStable p (shiftImage x)
