module DASHI.Physics.Closure.CanonicalChamberToShiftWitnessBridgeInstance where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Nat using (_≤_)
open import Data.Vec using (_∷_; [])

open import MonsterOntos using
  (SSP; p2; p3; p5; p7; p11; p13; p17; p19; p23; p29; p31; p41; p47; p59; p71)
open import Ontology.GodelLattice using (FactorVec)
open import Ontology.Hecke.ChamberToShiftWitnessBridge as CTSW

open import DASHI.Algebra.Trit using (pos; zer)
open import DASHI.Execution.Contract as EC
open import DASHI.Geometry.ShiftLorentzEmergenceInstance as SLEI
open import DASHI.Physics.Closure.PrimeCompatibilityProfile as PCP
open import DASHI.Physics.Closure.CanonicalConstraintGaugePackage as CCGP
open import DASHI.Physics.Closure.ParametricGaugeConstraintTheorem as PGCT
open import DASHI.Physics.Closure.ShiftRGObservableInstance as SRGOI using
  (canonicalShiftHeckeState; shiftPrimeEmbedding)
open import DASHI.Physics.Constraints.ConcreteInstance as CI

------------------------------------------------------------------------
-- First concrete inhabitant of the minimal witness-level bridge. This still
-- computes the witness from the transported canonical shift image, but it
-- lands the smaller fixed-prime illegal-mask/forced-stable-mask surface as a
-- real instance on the canonical closure carrier.

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

closureCompat : CanonicalClosureCarrier → SSP → Bool
closureCompat CI.CR p = closureCompatCR p
  where
  closureCompatCR : SSP → Bool
  closureCompatCR p2  = false
  closureCompatCR p3  = true
  closureCompatCR p5  = true
  closureCompatCR p7  = true
  closureCompatCR p11 = true
  closureCompatCR p13 = true
  closureCompatCR p17 = true
  closureCompatCR p19 = true
  closureCompatCR p23 = false
  closureCompatCR p29 = true
  closureCompatCR p31 = false
  closureCompatCR p41 = true
  closureCompatCR p47 = true
  closureCompatCR p59 = true
  closureCompatCR p71 = false
closureCompat CI.CP p = closureCompatCP p
  where
  closureCompatCP : SSP → Bool
  closureCompatCP p2  = true
  closureCompatCP p3  = false
  closureCompatCP p5  = true
  closureCompatCP p7  = true
  closureCompatCP p11 = true
  closureCompatCP p13 = true
  closureCompatCP p17 = true
  closureCompatCP p19 = true
  closureCompatCP p23 = true
  closureCompatCP p29 = false
  closureCompatCP p31 = true
  closureCompatCP p41 = true
  closureCompatCP p47 = true
  closureCompatCP p59 = true
  closureCompatCP p71 = true
closureCompat CI.CC p = closureCompatCC p
  where
  closureCompatCC : SSP → Bool
  closureCompatCC p2  = true
  closureCompatCC p3  = true
  closureCompatCC p5  = false
  closureCompatCC p7  = true
  closureCompatCC p11 = true
  closureCompatCC p13 = true
  closureCompatCC p17 = true
  closureCompatCC p19 = true
  closureCompatCC p23 = true
  closureCompatCC p29 = true
  closureCompatCC p31 = true
  closureCompatCC p41 = true
  closureCompatCC p47 = true
  closureCompatCC p59 = true
  closureCompatCC p71 = true

canonicalPrimeCompatibilityProfile :
  PCP.PrimeCompatibilityProfile CanonicalClosureCarrier
canonicalPrimeCompatibilityProfile =
  record
    { compat = closureCompat
    }

closurePrimeEmbedding : CanonicalClosureCarrier → FactorVec
closurePrimeEmbedding =
  PCP.PrimeCompatibilityProfile.primeEmbedding canonicalPrimeCompatibilityProfile

closurePrimeEmbedding≡transported : ∀ x → closurePrimeEmbedding x ≡ canonicalShiftPrimeImage x
closurePrimeEmbedding≡transported CI.CR = refl
closurePrimeEmbedding≡transported CI.CP = refl
closurePrimeEmbedding≡transported CI.CC = refl

canonicalIllegalMask : CanonicalClosureCarrier → SSP → SSP → Bool
canonicalIllegalMask =
  PCP.PrimeCompatibilityProfile.illegalMask canonicalPrimeCompatibilityProfile

canonicalShiftWitness : CanonicalClosureCarrier → SSP → CTSW.ShiftWitness
canonicalShiftWitness =
  PCP.PrimeCompatibilityProfile.witness canonicalPrimeCompatibilityProfile

canonicalChamberToShiftWitnessBridge :
  CTSW.ChamberToShiftWitnessBridge CanonicalClosureCarrier
canonicalChamberToShiftWitnessBridge =
  PCP.PrimeCompatibilityProfile.witnessBridge canonicalPrimeCompatibilityProfile

canonicalIllegalCount≤forcedStableCountHist :
  ∀ x p →
  CTSW.illegalCount-chamber canonicalChamberToShiftWitnessBridge x p
    ≤
  CTSW.forcedStableCount-hist canonicalChamberToShiftWitnessBridge x p
canonicalIllegalCount≤forcedStableCountHist =
  CTSW.forcedStableTransfer canonicalChamberToShiftWitnessBridge
