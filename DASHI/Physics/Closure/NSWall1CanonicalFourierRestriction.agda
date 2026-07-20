module DASHI.Physics.Closure.NSWall1CanonicalFourierRestriction where

open import Agda.Primitive using (Level; lsuc)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List)
open import Data.Rational.Base using (ℚ)

open import DASHI.Analysis.FiniteWeightedKernelSums
open import DASHI.Analysis.FiniteWeightedKernelTransport
open import DASHI.Physics.Closure.NSIntegerFourierLattice using (FourierMode)
open import DASHI.Physics.Closure.NSWall1CanonicalModePacket
open import DASHI.Physics.Closure.NSWall1CanonicalFiniteSchur
open import DASHI.Physics.Closure.NSWall1FourierShellInstance

------------------------------------------------------------------------
-- Canonical six-mode restriction of an actual Fourier kernel.
--
-- The exact 3 x 3 rational Schur certificates may be transferred to a physical
-- Fourier kernel only after the physical entries agree on the six declared
-- modes.  This module performs that transport and keeps support/list identity
-- explicit.  It does not claim that the full shell operator is exhausted by the
-- six-mode restriction.
------------------------------------------------------------------------

embedLowMode : LowMode → FourierMode
embedLowMode low100 = p100
embedLowMode low010 = p010
embedLowMode low001 = p001

embedHighMode : HighMode → FourierMode
embedHighMode high110 = p110
embedHighMode high101 = p101
embedHighMode high011 = p011

restrictedK01 :
  (FourierMode → FourierMode → ℚ) →
  HighMode → LowMode → ℚ
restrictedK01 actual high low =
  actual (embedHighMode high) (embedLowMode low)

restrictedK10 :
  (FourierMode → FourierMode → ℚ) →
  LowMode → HighMode → ℚ
restrictedK10 actual low high =
  actual (embedLowMode low) (embedHighMode high)

record CanonicalFourierRestrictionMatch
    (actualK01 actualK10 : FourierMode → FourierMode → ℚ) : Set where
  field
    k01EntryMatch :
      (high : HighMode) →
      (low : LowMode) →
      restrictedK01 actualK01 high low ≡ canonicalK01 high low

    k10EntryMatch :
      (low : LowMode) →
      (high : HighMode) →
      restrictedK10 actualK10 low high ≡ canonicalK10 low high

open CanonicalFourierRestrictionMatch public

restrictedK01Finite :
  (FourierMode → FourierMode → ℚ) →
  FiniteWeightedKernel HighMode LowMode ℚ
restrictedK01Finite actual =
  replaceKernel canonicalK01Finite (restrictedK01 actual)

restrictedK10Finite :
  (FourierMode → FourierMode → ℚ) →
  FiniteWeightedKernel LowMode HighMode ℚ
restrictedK10Finite actual =
  replaceKernel canonicalK10Finite (restrictedK10 actual)

canonicalCertificateControlsRestrictedK01 :
  (actualK01 actualK10 : FourierMode → FourierMode → ℚ) →
  (M : CanonicalFourierRestrictionMatch actualK01 actualK10) →
  FiniteWeightedSchurCertificate (restrictedK01Finite actualK01)
canonicalCertificateControlsRestrictedK01 actualK01 actualK10 M =
  transportFiniteWeightedSchurCertificate
    canonicalK01Finite
    (restrictedK01 actualK01)
    (k01EntryMatch M)
    canonicalK01Certificate

canonicalCertificateControlsRestrictedK10 :
  (actualK01 actualK10 : FourierMode → FourierMode → ℚ) →
  (M : CanonicalFourierRestrictionMatch actualK01 actualK10) →
  FiniteWeightedSchurCertificate (restrictedK10Finite actualK10)
canonicalCertificateControlsRestrictedK10 actualK01 actualK10 M =
  transportFiniteWeightedSchurCertificate
    canonicalK10Finite
    (restrictedK10 actualK10)
    (k10EntryMatch M)
    canonicalK10Certificate

------------------------------------------------------------------------
-- Wall-1 specialization.  Active-list equalities prevent the restricted
-- certificate from being silently promoted to an operator with additional
-- source or target modes.
------------------------------------------------------------------------

record Wall1CanonicalFourierRestriction
    {v : Level}
    (Vector : Set v)
    (W01 W10 : Wall1FourierShellData Vector ℚ) : Set (lsuc v) where
  field
    targetModes01AreCanonical :
      targetModes W01 ≡
      DASHI.Analysis.FiniteWeightedKernelSums.map embedHighMode highModes

    sourceModes01AreCanonical :
      sourceModes W01 ≡
      DASHI.Analysis.FiniteWeightedKernelSums.map embedLowMode lowModes

    targetModes10AreCanonical :
      targetModes W10 ≡
      DASHI.Analysis.FiniteWeightedKernelSums.map embedLowMode lowModes

    sourceModes10AreCanonical :
      sourceModes W10 ≡
      DASHI.Analysis.FiniteWeightedKernelSums.map embedHighMode highModes

    restrictionMatch :
      CanonicalFourierRestrictionMatch
        (wall1BiotSavartKernel W01)
        (wall1BiotSavartKernel W10)

open Wall1CanonicalFourierRestriction public

wall1CanonicalRestrictedK01Certificate :
  ∀ {v}
    {Vector : Set v}
    {W01 W10 : Wall1FourierShellData Vector ℚ} →
  Wall1CanonicalFourierRestriction Vector W01 W10 →
  FiniteWeightedSchurCertificate
    (restrictedK01Finite (wall1BiotSavartKernel W01))
wall1CanonicalRestrictedK01Certificate {W01 = W01} {W10 = W10} R =
  canonicalCertificateControlsRestrictedK01
    (wall1BiotSavartKernel W01)
    (wall1BiotSavartKernel W10)
    (restrictionMatch R)

wall1CanonicalRestrictedK10Certificate :
  ∀ {v}
    {Vector : Set v}
    {W01 W10 : Wall1FourierShellData Vector ℚ} →
  Wall1CanonicalFourierRestriction Vector W01 W10 →
  FiniteWeightedSchurCertificate
    (restrictedK10Finite (wall1BiotSavartKernel W10))
wall1CanonicalRestrictedK10Certificate {W01 = W01} {W10 = W10} R =
  canonicalCertificateControlsRestrictedK10
    (wall1BiotSavartKernel W01)
    (wall1BiotSavartKernel W10)
    (restrictionMatch R)
