module DASHI.Moonshine.JInvariant369NormalizedRendererReadoutFactorizationExact where

------------------------------------------------------------------------
-- NORMALIZED-j RENDERER READOUT FACTORIZATION
--
-- Existing StandardJRendererReadout mixes two conceptually distinct layers:
--
--   (A) analytic readout:
--       real/imaginary parts and continuous phase extraction;
--
--   (B) presentation / finite observers:
--       tone, colour, and C3/C6/C9/C27 quantizers.
--
-- The Lean route-B target now owns a concrete continuous readout using
-- Mathlib Complex.arg with phase carrier Real.Angle, together with exact
-- conjugation/reflection equivariance.
--
-- This module factors the Agda interface accordingly.  It does not pretend
-- that the finite sector quantizers or colour/tone calibration are canonical.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

import Base369 as Base
import DASHI.Biology.TriadicKernelLiftQuotientExact as Triadic
import DASHI.Foundations.Base369Ternary27HypervoxelFabricGeometryExact as Fabric

import DASHI.Physics.Closure.TriadicEisensteinTransformationTheorem as Eisenstein
import DASHI.Moonshine.JInvariant369NormalizedAnalyticRendererExact as Normalized

------------------------------------------------------------------------
-- 1. Continuous analytic phase readout.
------------------------------------------------------------------------

record StandardJContinuousReadout
    (M : Eisenstein.EisensteinAnalyticModel) : Set₁ where
  field
    Scalar : Set
    Phase : Set

    realPart :
      Eisenstein.Scalar M → Scalar

    imagPart :
      Eisenstein.Scalar M → Scalar

    atan2 :
      Scalar → Scalar → Phase

open StandardJContinuousReadout public

------------------------------------------------------------------------
-- 2. Presentation and finite observer layer.
------------------------------------------------------------------------

record StandardJPresentationReadout
    (M : Eisenstein.EisensteinAnalyticModel)
    (C : StandardJContinuousReadout M) : Set₁ where
  field
    Tone : Set
    Colour : Set

    toneOfValue :
      Eisenstein.Scalar M → Tone

    phaseColour :
      Phase C → Colour

    composeTone :
      Tone → Colour → Colour

    phase3 :
      Phase C → Triadic.KernelTrit

    phase6 :
      Phase C → Base.HexTruth

    phase9 :
      Phase C → Triadic.NineSheet

    phase27 :
      Phase C → Fabric.Ternary27Point

open StandardJPresentationReadout public

------------------------------------------------------------------------
-- 3. Reassemble the old renderer-facing interface exactly.
------------------------------------------------------------------------

assembleStandardJRendererReadout :
  ∀ {M} →
  (C : StandardJContinuousReadout M) →
  StandardJPresentationReadout M C →
  Normalized.StandardJRendererReadout M
assembleStandardJRendererReadout C P =
  record
    { Normalized.Scalar = Scalar C
    ; Normalized.Phase = Phase C
    ; Normalized.Tone = Tone P
    ; Normalized.Colour = Colour P

    ; Normalized.realPart = realPart C
    ; Normalized.imagPart = imagPart C
    ; Normalized.atan2 = atan2 C
    ; Normalized.toneOfValue = toneOfValue P

    ; Normalized.phaseColour = phaseColour P
    ; Normalized.composeTone = composeTone P

    ; Normalized.phase3 = phase3 P
    ; Normalized.phase6 = phase6 P
    ; Normalized.phase9 = phase9 P
    ; Normalized.phase27 = phase27 P
    }

------------------------------------------------------------------------
-- 4. The factorization is lossless at the interface level.
------------------------------------------------------------------------

assembledScalar :
  ∀ {M}
    (C : StandardJContinuousReadout M)
    (P : StandardJPresentationReadout M C) →
  Normalized.Scalar
    (assembleStandardJRendererReadout C P)
  ≡
  Scalar C
assembledScalar C P = refl

assembledPhase :
  ∀ {M}
    (C : StandardJContinuousReadout M)
    (P : StandardJPresentationReadout M C) →
  Normalized.Phase
    (assembleStandardJRendererReadout C P)
  ≡
  Phase C
assembledPhase C P = refl

------------------------------------------------------------------------
-- 5. Cross-prover theorem-parity receipt.
--
-- Lean module:
--   Integration.MoonshineNormalizedJPhaseReadout
--
-- It owns on ordinary Mathlib complex numbers:
--
--   jValue       = normalized route-B standard j,
--   jRealPart    = re(j),
--   jImagPart    = im(j),
--   jMagnitude   = |j|,
--   jPhase       = Complex.arg(j) : Real.Angle,
--
-- and proves
--
--   jPhase(reflect tau) = -jPhase(tau)
--
-- exactly in Real.Angle.
--
-- This is theorem parity, not an automatic Agda carrier inhabitant.
------------------------------------------------------------------------

record LeanContinuousJReadoutParity : Set where
  constructor lean-continuous-j-readout-parity
  field
    leanRepository : String
    leanBranch : String
    leanModule : String

    normalizedJValueConcreteInLean : Bool
    realPartConcreteInLean : Bool
    imagPartConcreteInLean : Bool
    magnitudeConcreteInLean : Bool
    continuousArgConcreteInLean : Bool
    phaseCarrierIsFullTurnAngleQuotient : Bool
    reflectionActsByAngleNegation : Bool
    fixedLocusPhaseSelfNegationOwned : Bool

    agdaContinuousReadoutInhabitedByThisReceipt : Bool
    finiteQuantizersConstructedByThisReceipt : Bool
    colourCalibrationConstructedByThisReceipt : Bool

canonicalLeanContinuousJReadoutParity :
  LeanContinuousJReadoutParity
canonicalLeanContinuousJReadoutParity =
  lean-continuous-j-readout-parity
    "chboishabba/dashi_lean4"
    "agent/moonshine-eisenstein-analytic-20260922"
    "Integration.MoonshineNormalizedJPhaseReadout"
    true true true true true true true true
    false false false

------------------------------------------------------------------------
-- 6. Boundary.
------------------------------------------------------------------------

record NormalizedReadoutFactorizationBoundary : Set where
  constructor normalized-readout-factorization-boundary
  field
    continuousPresentationSplitOwned : Bool
    oldReadoutReassemblesExactly : Bool
    leanConcreteContinuousReadoutParityRecorded : Bool
    leanPhaseReflectionOwned : Bool

    continuousAgdaReadoutInhabitedHere : Bool
    finiteC3QuantizerInhabitedHere : Bool
    finiteC6QuantizerInhabitedHere : Bool
    finiteC9QuantizerInhabitedHere : Bool
    finiteC27QuantizerInhabitedHere : Bool
    toneColourCalibrationInhabitedHere : Bool

canonicalNormalizedReadoutFactorizationBoundary :
  NormalizedReadoutFactorizationBoundary
canonicalNormalizedReadoutFactorizationBoundary =
  normalized-readout-factorization-boundary
    true true true true
    false false false false false false
