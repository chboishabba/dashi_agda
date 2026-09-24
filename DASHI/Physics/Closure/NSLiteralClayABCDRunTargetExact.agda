module DASHI.Physics.Closure.NSLiteralClayABCDRunTargetExact where

------------------------------------------------------------------------
-- LITERAL NAVIER--STOKES A/B/C/D RUN TARGET
--
-- This file is the terminal theorem surface for actual proof checking.
-- It contains no Boolean proxy, no provenance-as-proof coercion, no postulate,
-- and no "external theorem automatically becomes Agda proof" shortcut.
--
-- A/B/C/D below are exactly the canonical literal propositions already fixed
-- by NSClayLiteralABCDExact + NSCanonicalLiteralABCDInstanceExact.
--
-- The Lean 4.34 terminal project now has actual checked-source terms for the
-- independent literal C/D specification.  Agda deliberately does not pretend
-- those foreign kernel terms are native Agda terms.  A cross-kernel importer
-- must eventually provide the *actual* C/D terms requested by
-- CanonicalLiteralCDKernelBridge below.
------------------------------------------------------------------------

import DASHI.Physics.Closure.NSClayLiteralABCDExact as Clay
import DASHI.Physics.Closure.NSCanonicalEuclideanPeriodicSemanticCarriersExact as Canonical
import DASHI.Physics.Closure.NSCanonicalLiteralABCDInstanceExact as Instance

LiteralA :
  Canonical.CanonicalNSSemantics → Set₁
LiteralA S =
  Clay.FeffermanEuclideanClayStatementA
    (Canonical.canonicalEuclideanA S)

LiteralB :
  Clay.FeffermanPeriodicClayCarrier → Set₁
LiteralB periodicB =
  Clay.FeffermanPeriodicClayStatementB periodicB

LiteralC :
  Canonical.CanonicalNSSemantics → Set₁
LiteralC S =
  Clay.FeffermanEuclideanClayStatementC
    (Canonical.canonicalEuclideanC S)

LiteralD :
  Canonical.CanonicalNSSemantics → Set₁
LiteralD S =
  Clay.FeffermanPeriodicClayStatementD
    (Canonical.canonicalPeriodicD S)

record LiteralABCDNativeProofs
    (S : Canonical.CanonicalNSSemantics)
    (periodicB : Clay.FeffermanPeriodicClayCarrier) : Set₂ where
  field
    proofA : LiteralA S
    proofB : LiteralB periodicB
    proofC : LiteralC S
    proofD : LiteralD S

open LiteralABCDNativeProofs public

nativeProofsToLiteralFourAlternativeCompletion :
  ∀ {S periodicB} →
  LiteralABCDNativeProofs S periodicB →
  Clay.LiteralFourAlternativeCompletion
    (Instance.canonicalLiteralABCDInstance S periodicB)
nativeProofsToLiteralFourAlternativeCompletion proofs = record
  { Clay.proofA = proofA proofs
  ; Clay.proofB = proofB proofs
  ; Clay.proofC = proofC proofs
  ; Clay.proofD = proofD proofs
  }

record CanonicalLiteralNSRunTarget
    (S : Canonical.CanonicalNSSemantics)
    (periodicB : Clay.FeffermanPeriodicClayCarrier) : Set₂ where
  field
    resolution :
      Clay.AnyOneClayResolution
        (Instance.canonicalLiteralABCDInstance S periodicB)

open CanonicalLiteralNSRunTarget public

runTargetFromA :
  ∀ {S periodicB} →
  LiteralA S →
  CanonicalLiteralNSRunTarget S periodicB
runTargetFromA proof = record
  { resolution = Instance.canonicalAResolution proof }

runTargetFromB :
  ∀ {S periodicB} →
  LiteralB periodicB →
  CanonicalLiteralNSRunTarget S periodicB
runTargetFromB proof = record
  { resolution = Instance.canonicalBResolution proof }

runTargetFromC :
  ∀ {S periodicB} →
  LiteralC S →
  CanonicalLiteralNSRunTarget S periodicB
runTargetFromC proof = record
  { resolution = Instance.canonicalCResolution proof }

runTargetFromD :
  ∀ {S periodicB} →
  LiteralD S →
  CanonicalLiteralNSRunTarget S periodicB
runTargetFromD proof = record
  { resolution = Instance.canonicalDResolution proof }

------------------------------------------------------------------------
-- Exact foreign-kernel import boundary.
--
-- A successful Lean check is strong evidence and, in the nested Lean terminal
-- project, gives literal C/D terms in Lean's kernel.  To claim an Agda-kernel
-- Clay resolution, however, the bridge must materialize native Agda terms of
-- LiteralC / LiteralD.  This record is intentionally proof-bearing: metadata,
-- commit hashes, Booleans, or source-alignment receipts cannot inhabit it.
------------------------------------------------------------------------

record CanonicalLiteralCDKernelBridge
    (S : Canonical.CanonicalNSSemantics) : Set₂ where
  field
    proofC : LiteralC S
    proofD : LiteralD S

open CanonicalLiteralCDKernelBridge public

runTargetFromCDKernelBridgeC :
  ∀ {S periodicB} →
  CanonicalLiteralCDKernelBridge S →
  CanonicalLiteralNSRunTarget S periodicB
runTargetFromCDKernelBridgeC bridge =
  runTargetFromC (CanonicalLiteralCDKernelBridge.proofC bridge)

runTargetFromCDKernelBridgeD :
  ∀ {S periodicB} →
  CanonicalLiteralCDKernelBridge S →
  CanonicalLiteralNSRunTarget S periodicB
runTargetFromCDKernelBridgeD bridge =
  runTargetFromD (CanonicalLiteralCDKernelBridge.proofD bridge)

------------------------------------------------------------------------
-- Native target equivalence: all-four is stronger than required.
------------------------------------------------------------------------

nativeAllFourToRunTarget :
  ∀ {S periodicB} →
  LiteralABCDNativeProofs S periodicB →
  CanonicalLiteralNSRunTarget S periodicB
nativeAllFourToRunTarget proofs =
  record
    { resolution =
        Clay.literalAllFourImpliesAnyOne
          (nativeProofsToLiteralFourAlternativeCompletion proofs)
    }
