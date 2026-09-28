{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119AntigravityPreferredCanonicalSU2S4NoGoExact where

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ)

import DASHI.Physics.Foundations.CMP119AntigravityLiteralPlaquetteSourceTrajectoryExact as Source
import DASHI.Physics.Foundations.CMP119AntigravityCanonicalSU2LiteralHistoryExact as SU2History
import DASHI.Physics.Foundations.CMP119AntigravityCanonicalLiteralPlaquetteHistoryExact as CanonicalHistory
import DASHI.Physics.Foundations.CMP119AntigravityCanonicalRowAInverseThresholdExact as Threshold
import DASHI.Physics.Foundations.CMP119AntigravityCanonicalRowALiteralTerminalHistoryExact as Terminal
import DASHI.Physics.Foundations.CMP119AntigravityLiteralPlaquetteBetaDrivenDensityExact as Density
import DASHI.Physics.Foundations.CMP119AntigravityCanonicalBishopSU2ConventionExact as Convention
import DASHI.Physics.Foundations.CMP119AntigravityPreferredLiteralS4NoGoExact as Preferred
import DASHI.Physics.YangMills.BalabanClayT4LocalizedPlaquetteCoefficientProducerExact as Plaquette
import DASHI.Physics.YangMills.BalabanYM4QuarticResponseCanonicalChoiceExact as RowA
open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- SHORTEST CURRENT S4 SOURCE INTERFACE
--
-- Compile all currently-constructible administrative coordinates:
--
--   source trajectory              from literal plaquette + UV coherence
--   Gaussian history bounds        from one common SU(2) log window
--   history zLower                 from (11/12) * logFloor
--   history zUpper                 from (11/12) * logCeiling
--   threshold coupling gamma       from canonical Row-A choice
--   inverse threshold u_*          from exact reciprocal of gamma^2
--
-- The surviving inputs are physical/provenance data rather than duplicate
-- scalar choices.
------------------------------------------------------------------------

record PreferredCanonicalSU2S4NoGo
    (plaquette : Plaquette.PhysicalRunningCouplingData Nat)
    (coherence : Source.LiteralPlaquetteUVChainCoherence plaquette)
    (source : SU2History.CanonicalSU2LiteralHistory plaquette coherence)
    (rowA : RowA.FiniteQuarticResponseConstants)
    (geometry :
      Threshold.CanonicalRowATerminalGeometry
        plaquette coherence
        (SU2History.asCanonicalLiteralPlaquetteHistory source)
        rowA) : Set₂ where
  field
    density :
      Density.LiteralPlaquetteBetaDrivenDensity
        plaquette
        (CanonicalHistory.trajectory coherence)
        (CanonicalHistory.asLiteralPlaquetteCMP109FiniteHistory
          (SU2History.asCanonicalLiteralPlaquetteHistory source))
        (Terminal.asLiteralPlaquetteTerminalHistory
          (Threshold.asCanonicalRowALiteralTerminalHistory geometry))

    traceBoundary :
      Convention.CanonicalBishopSU2TraceBoundary

open PreferredCanonicalSU2S4NoGo public

asPreferredLiteralS4NoGo :
  ∀ {plaquette coherence source rowA geometry} →
  PreferredCanonicalSU2S4NoGo
    plaquette coherence source rowA geometry →
  Preferred.PreferredLiteralS4NoGo
    plaquette
    coherence
    (SU2History.asCanonicalLiteralPlaquetteHistory source)
    rowA
    (Threshold.asCanonicalRowALiteralTerminalHistory geometry)
asPreferredLiteralS4NoGo package = record
  { Preferred.PreferredLiteralS4NoGo.density =
      density package
  ; Preferred.PreferredLiteralS4NoGo.traceBoundary =
      traceBoundary package
  }

freeUniformGaussianBoundsRequired : Bool
freeUniformGaussianBoundsRequired = false

freeHistoryZLowerEqualityRequired : Bool
freeHistoryZLowerEqualityRequired = false

freeInverseThresholdRequired : Bool
freeInverseThresholdRequired = false

freeInverseThresholdLawRequired : Bool
freeInverseThresholdLawRequired = false

freeUniformGaussianBoundsRequiredIsFalse :
  freeUniformGaussianBoundsRequired ≡ false
freeUniformGaussianBoundsRequiredIsFalse = refl

freeHistoryZLowerEqualityRequiredIsFalse :
  freeHistoryZLowerEqualityRequired ≡ false
freeHistoryZLowerEqualityRequiredIsFalse = refl

freeInverseThresholdRequiredIsFalse :
  freeInverseThresholdRequired ≡ false
freeInverseThresholdRequiredIsFalse = refl

freeInverseThresholdLawRequiredIsFalse :
  freeInverseThresholdLawRequired ≡ false
freeInverseThresholdLawRequiredIsFalse = refl

preferredCanonicalSU2S4CompilerLevel : ProofLevel
preferredCanonicalSU2S4CompilerLevel = machineChecked

------------------------------------------------------------------------
-- Remaining source frontier on this route:
--
--   1. literal UV-chain coherence;
--   2. one finite SU(2) log window;
--   3. per-step absolute quartic interaction enclosure;
--   4. terminal-scale reachability + literal inverse-square coupling identity;
--   5. CMP122 density/Section-2 attachment;
--   6. selected Lorentzian trace/F^2 boundary.
------------------------------------------------------------------------
