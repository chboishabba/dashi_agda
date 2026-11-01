module DASHI.Physics.Closure.NSCanonicalLiteralABCDInstanceExact where

------------------------------------------------------------------------
-- ONE HARDENED LITERAL A/B/C/D INSTANCE
--
-- A/C/D now use the fixed constructive R^3 field semantics from
-- NSCanonicalEuclideanPeriodicSemanticCarriersExact.  B deliberately reuses
-- the pre-existing literal periodic Clay carrier.
--
-- This is the capstone instance on which the four programmes may converge.
-- It prevents A/C/D from being discharged by changing the meanings of fields,
-- forcing or the PDE while preserving B's older canonical theorem surface.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Closure.NSClayLiteralABCDExact as Clay
import DASHI.Physics.Closure.NSCanonicalEuclideanPeriodicSemanticCarriersExact as Canonical

canonicalLiteralABCDInstance :
  Canonical.CanonicalNSSemantics →
  Clay.FeffermanPeriodicClayCarrier →
  Clay.LiteralClayABCDInstance
canonicalLiteralABCDInstance S periodicB = record
  { Clay.carrierA = Canonical.canonicalEuclideanA S
  ; Clay.carrierB = periodicB
  ; Clay.carrierC = Canonical.canonicalEuclideanC S
  ; Clay.carrierD = Canonical.canonicalPeriodicD S
  }

canonicalAResolution :
  ∀ {S periodicB} →
  Clay.FeffermanEuclideanClayStatementA
    (Canonical.canonicalEuclideanA S) →
  Clay.AnyOneClayResolution
    (canonicalLiteralABCDInstance S periodicB)
canonicalAResolution proof = Clay.resolvedA proof

canonicalBResolution :
  ∀ {S periodicB} →
  Clay.FeffermanPeriodicClayStatementB periodicB →
  Clay.AnyOneClayResolution
    (canonicalLiteralABCDInstance S periodicB)
canonicalBResolution proof = Clay.resolvedB proof

canonicalCResolution :
  ∀ {S periodicB} →
  Clay.FeffermanEuclideanClayStatementC
    (Canonical.canonicalEuclideanC S) →
  Clay.AnyOneClayResolution
    (canonicalLiteralABCDInstance S periodicB)
canonicalCResolution proof = Clay.resolvedC proof

canonicalDResolution :
  ∀ {S periodicB} →
  Clay.FeffermanPeriodicClayStatementD
    (Canonical.canonicalPeriodicD S) →
  Clay.AnyOneClayResolution
    (canonicalLiteralABCDInstance S periodicB)
canonicalDResolution proof = Clay.resolvedD proof

canonicalABCDInstanceConstructed : Bool
canonicalABCDInstanceConstructed = true

aUsesCanonicalEuclideanCarrier : Bool
aUsesCanonicalEuclideanCarrier = true

bUsesExistingLiteralPeriodicCarrier : Bool
bUsesExistingLiteralPeriodicCarrier = true

cUsesCanonicalEuclideanForcedCarrier : Bool
cUsesCanonicalEuclideanForcedCarrier = true

dUsesCanonicalPeriodicForcedCarrier : Bool
dUsesCanonicalPeriodicForcedCarrier = true

anyAlternativeInhabitedHere : Bool
anyAlternativeInhabitedHere = false

canonicalABCDInstanceConstructedIsTrue :
  canonicalABCDInstanceConstructed ≡ true
canonicalABCDInstanceConstructedIsTrue = refl

anyAlternativeInhabitedHereIsFalse :
  anyAlternativeInhabitedHere ≡ false
anyAlternativeInhabitedHereIsFalse = refl
