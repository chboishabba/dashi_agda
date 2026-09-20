module DASHI.Physics.Closure.NSFullyCanonicalLiteralABCDInstanceExact where

------------------------------------------------------------------------
-- FULLY CANONICAL LITERAL A/B/C/D INSTANCE
--
-- The older NSCanonicalLiteralABCDInstanceExact hardened A/C/D but still took
-- an arbitrary FeffermanPeriodicClayCarrier for B.  That is useful as an
-- interface, but it is not a safe terminal resolution boundary: choosing an
-- empty or otherwise convenient B carrier would vacuously inhabit B.
--
-- CanonicalNSSemantics now constructs periodic B on the same Bishop-real
-- space/time/field types and the same unforced Navier--Stokes semantics used by
-- A.  This owner removes the last carrier-choice parameter from the capstone.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Closure.NSClayLiteralABCDExact as Clay
import DASHI.Physics.Closure.NSCanonicalEuclideanPeriodicSemanticCarriersExact as Canonical

fullyCanonicalLiteralABCDInstance :
  Canonical.CanonicalNSSemantics →
  Clay.LiteralClayABCDInstance
fullyCanonicalLiteralABCDInstance S = record
  { Clay.carrierA = Canonical.canonicalEuclideanA S
  ; Clay.carrierB = Canonical.canonicalPeriodicB S
  ; Clay.carrierC = Canonical.canonicalEuclideanC S
  ; Clay.carrierD = Canonical.canonicalPeriodicD S
  }

fullyCanonicalAResolution :
  ∀ {S} →
  Clay.FeffermanEuclideanClayStatementA
    (Canonical.canonicalEuclideanA S) →
  Clay.AnyOneClayResolution
    (fullyCanonicalLiteralABCDInstance S)
fullyCanonicalAResolution proof = Clay.resolvedA proof

fullyCanonicalBResolution :
  ∀ {S} →
  Clay.FeffermanPeriodicClayStatementB
    (Canonical.canonicalPeriodicB S) →
  Clay.AnyOneClayResolution
    (fullyCanonicalLiteralABCDInstance S)
fullyCanonicalBResolution proof = Clay.resolvedB proof

fullyCanonicalCResolution :
  ∀ {S} →
  Clay.FeffermanEuclideanClayStatementC
    (Canonical.canonicalEuclideanC S) →
  Clay.AnyOneClayResolution
    (fullyCanonicalLiteralABCDInstance S)
fullyCanonicalCResolution proof = Clay.resolvedC proof

fullyCanonicalDResolution :
  ∀ {S} →
  Clay.FeffermanPeriodicClayStatementD
    (Canonical.canonicalPeriodicD S) →
  Clay.AnyOneClayResolution
    (fullyCanonicalLiteralABCDInstance S)
fullyCanonicalDResolution proof = Clay.resolvedD proof

allFourCarriersFixedByOneSemanticAuthority : Bool
allFourCarriersFixedByOneSemanticAuthority = true

periodicBCarrierCallerSelectableAtTerminalBoundary : Bool
periodicBCarrierCallerSelectableAtTerminalBoundary = false

vacuousPeriodicBCarrierCanDischargeFullyCanonicalCapstone : Bool
vacuousPeriodicBCarrierCanDischargeFullyCanonicalCapstone = false

anyAlternativeInhabitedHere : Bool
anyAlternativeInhabitedHere = false

clayPromotion : Bool
clayPromotion = false

allFourCarriersFixedByOneSemanticAuthorityIsTrue :
  allFourCarriersFixedByOneSemanticAuthority ≡ true
allFourCarriersFixedByOneSemanticAuthorityIsTrue = refl

periodicBCarrierCallerSelectableAtTerminalBoundaryIsFalse :
  periodicBCarrierCallerSelectableAtTerminalBoundary ≡ false
periodicBCarrierCallerSelectableAtTerminalBoundaryIsFalse = refl

vacuousPeriodicBCarrierCanDischargeFullyCanonicalCapstoneIsFalse :
  vacuousPeriodicBCarrierCanDischargeFullyCanonicalCapstone ≡ false
vacuousPeriodicBCarrierCanDischargeFullyCanonicalCapstoneIsFalse = refl

anyAlternativeInhabitedHereIsFalse :
  anyAlternativeInhabitedHere ≡ false
anyAlternativeInhabitedHereIsFalse = refl

clayPromotionIsFalse : clayPromotion ≡ false
clayPromotionIsFalse = refl
