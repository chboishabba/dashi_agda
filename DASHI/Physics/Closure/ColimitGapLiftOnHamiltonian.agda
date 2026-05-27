module DASHI.Physics.Closure.ColimitGapLiftOnHamiltonian where

-- Gate 2 colimit-gap lift on the actual Nat tower.
--
-- This file reuses the canonical Gate 2 finite-to-limit witness chain:
-- the finite spectral-gap toolkit, the actual Nat witness slice, the
-- Nat-to-real transition receipt, and the existing colimit lift packaged in
-- Gate2SpectralGapMath.  It does not fabricate a real-carrier theorem.

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

open import DASHI.Geometry.LCP.FiniteSpectralGap using
  (FiniteSpectralGapToolkit; diagram; limitWitness)
open import DASHI.Geometry.LCP.InductiveLimit using (NatColimitWitness)

import DASHI.Physics.Closure.Gate2SpectralGapMath as Gate2
import DASHI.Physics.Closure.PressureBelow15SpectralNatWitnessSlice as Pressure

------------------------------------------------------------------------
-- Gate 2 colimit lift receipt.

canonicalActualNatTransitionReceipt :
  Pressure.S8NatToRealPhysicalCarrierTransitionReceipt
canonicalActualNatTransitionReceipt =
  Pressure.canonicalS8NatToRealPhysicalCarrierTransitionReceipt

canonicalNatColimitWitness :
  NatColimitWitness (diagram Gate2.gate2CanonicalToolkit)
canonicalNatColimitWitness =
  limitWitness Gate2.gate2CanonicalToolkit

canonicalColimitGapProof :
  Gate2.GapProof∞ Gate2.gate2CanonicalGap
canonicalColimitGapProof =
  Gate2.ColimitGapLift Gate2.canonicalUniformLowerBound

record ColimitGapLiftOnHamiltonianReceipt : Setω where
  field
    finiteSpectralGapToolkit :
      FiniteSpectralGapToolkit

    gapLiftConstructed :
      Bool

    gapLiftConstructedIsFalse :
      gapLiftConstructed ≡ false

    receiptBoundary :
      List String

open ColimitGapLiftOnHamiltonianReceipt public

canonicalColimitGapLiftOnHamiltonianReceipt :
  ColimitGapLiftOnHamiltonianReceipt
canonicalColimitGapLiftOnHamiltonianReceipt =
  record
    { finiteSpectralGapToolkit =
        Gate2.gate2CanonicalToolkit
    ; gapLiftConstructed =
        false
    ; gapLiftConstructedIsFalse =
        refl
    ; receiptBoundary =
        "The colimit gap lift consumes the canonical Gate 2 finite witness chain"
        ∷ "The actual Nat transition receipt is recorded as a canonical top-level witness"
        ∷ "The Nat colimit witness is reused as the finite-to-limit compatibility anchor"
        ∷ "No real-carrier analytic theorem is promoted by this wrapper"
        ∷ []
    }
