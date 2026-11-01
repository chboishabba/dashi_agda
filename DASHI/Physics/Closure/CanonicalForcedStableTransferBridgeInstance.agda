module DASHI.Physics.Closure.CanonicalForcedStableTransferBridgeInstance where

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Nat using (_≤_)
open import Data.Nat.Properties as NatP using (≤-refl)
open import Data.Vec using (_∷_; [])

open import DASHI.Algebra.Trit using (pos; zer)
open import DASHI.Execution.Contract as EC
open import DASHI.Geometry.ShiftLorentzEmergenceInstance as SLEI
open import MonsterOntos using (SSP)
open import Ontology.GodelLattice using (FactorVec)
open import Ontology.Hecke.FactorVecDefectHistograms as FDH using
  (forcedStableCount)
open import Ontology.Hecke.FactorVecDefectOrbitSummaries as FDOS using
  (DefectOrbitSummary; profileSummaryAt)
open import Ontology.Hecke.ForcedStableTransferBridge as FSTB

open import DASHI.Physics.Closure.CanonicalConstraintGaugePackage as CCGP
open import DASHI.Physics.Closure.ParametricGaugeConstraintTheorem as PGCT
open import DASHI.Physics.Closure.ShiftRGObservableInstance as SRGOI using
  (canonicalShiftHeckeState; shiftPrimeEmbedding)
open import DASHI.Physics.Constraints.ConcreteInstance as CI

------------------------------------------------------------------------
-- First concrete inhabitant of the forced-stable transfer ladder.
-- This uses the existing canonical closure-to-shift transport already exported
-- by the canonical abstract gauge/matter instance, then reads out the
-- shift-side prime address through the existing shift RG embedding.
--
-- The current closure-side count is still transported from that image, so
-- this is an honest first inhabitant of the bridge surface, not yet a
-- genuinely independent closure-native chamber count.

CanonicalClosureCarrier : Set
CanonicalClosureCarrier =
  CCGP.Carrier PGCT.canonicalConstraintGaugePackage

CanonicalShiftCarrier : Set
CanonicalShiftCarrier =
  EC.Contract.State (SLEI.shiftContract {suc zero} {suc (suc (suc zero))})

canonicalShiftRep0 : CanonicalShiftCarrier
canonicalShiftRep0 = pos ∷ zer ∷ zer ∷ zer ∷ []

canonicalShiftRep1 : CanonicalShiftCarrier
canonicalShiftRep1 = zer ∷ pos ∷ zer ∷ zer ∷ []

canonicalShiftRep2 : CanonicalShiftCarrier
canonicalShiftRep2 = zer ∷ zer ∷ pos ∷ zer ∷ []

canonicalTransportState : CanonicalClosureCarrier → CanonicalShiftCarrier
canonicalTransportState CI.CR = canonicalShiftRep0
canonicalTransportState CI.CP = canonicalShiftRep1
canonicalTransportState CI.CC = canonicalShiftRep2

canonicalShiftPrimeImage : CanonicalClosureCarrier → FactorVec
canonicalShiftPrimeImage x =
  shiftPrimeEmbedding
    (canonicalShiftHeckeState (canonicalTransportState x))

canonicalIllegalCountChamber : SSP → CanonicalClosureCarrier → Nat
canonicalIllegalCountChamber p x =
  forcedStableCount p (canonicalShiftPrimeImage x)

canonicalForcedStableTransferBridge :
  FSTB.ForcedStableTransferBridge CanonicalClosureCarrier
canonicalForcedStableTransferBridge =
  record
    { shiftImage = canonicalShiftPrimeImage
    ; illegalCountChamber = canonicalIllegalCountChamber
    ; illegalCount≤forcedStableCountHist = λ _ _ → NatP.≤-refl
    }

canonicalIllegalCount≡forcedStableCountHist :
  ∀ p x →
  canonicalIllegalCountChamber p x
    ≡
  forcedStableCount p (canonicalShiftPrimeImage x)
canonicalIllegalCount≡forcedStableCountHist _ _ = refl

canonicalIllegalCount≤forcedStableCountOrbit :
  ∀ p x →
  canonicalIllegalCountChamber p x
    ≤
  DefectOrbitSummary.forcedStableCount (profileSummaryAt p (canonicalShiftPrimeImage x))
canonicalIllegalCount≤forcedStableCountOrbit =
  FSTB.ForcedStableTransferBridge.illegalCount≤forcedStableCountOrbit
    canonicalForcedStableTransferBridge
