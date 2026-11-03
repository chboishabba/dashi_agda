{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119AntigravityVacuumConstantBetaOrthogonalityExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat; suc)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _-_)
open import Data.Rational.Tactic.RingSolver using (solve-∀)

import DASHI.Physics.Foundations.CMP119AntigravityCanonicalSourceSectorActionExact as Canonical
import DASHI.Physics.YangMills.BalabanClayT4LocalizedPlaquetteCoefficientProducerExact as T4
import DASHI.Physics.YangMills.BalabanYM4SourceNormalizedCouplingRecurrenceExact as Flow

------------------------------------------------------------------------
-- VACUUM CONSTANT IS ORTHOGONAL TO THE PLAQUETTE / BETA PROJECTION
--
-- A true additive vacuum/normalization coordinate is represented as
--
--   irrelevantAction V = localizedAction 0 V.
--
-- The canonical beta/source projection reads ONLY plaquetteCoefficientField.
-- Therefore a pure vacuum constant contributes exactly zero to that projection
-- and exactly zero to its scale-to-scale plaquette drift.
--
-- This turns the earlier non-identifiability into a structural theorem:
-- beta/plaquette data cannot recover V because that observation quotient has
-- deliberately discarded the constant coordinate.
------------------------------------------------------------------------

module _
  {Density Background Fluctuation : Set}
  (trajectory : Flow.SourceNormalizedCouplingTrajectory)
  (source : Canonical.CMP119NormalizedSectorSource
    Density Background Fluctuation)
  where

  record VacuumConstantEncoding : Set where
    field
      vacuumConstantAt : Nat → ℚ
      vacuumSectorIsConstantAction :
        ∀ scale →
        Canonical.vacuumAt source scale
        ≡ T4.irrelevantAction (vacuumConstantAt scale)

  open VacuumConstantEncoding public

  vacuumPlaquetteProjectionZero :
    (encoding : VacuumConstantEncoding) →
    ∀ scale →
    T4.plaquetteCoefficientProjector
      (Canonical.vacuumAt source scale)
    ≡ 0ℚ
  vacuumPlaquetteProjectionZero encoding scale
    rewrite vacuumSectorIsConstantAction encoding scale = refl

  vacuumPlaquetteDriftZero :
    (encoding : VacuumConstantEncoding) →
    ∀ scale →
    T4.plaquetteCoefficientProjector
      (Canonical.vacuumAt source scale)
    - T4.plaquetteCoefficientProjector
      (Canonical.vacuumAt source (suc scale))
    ≡ 0ℚ
  vacuumPlaquetteDriftZero encoding scale
    rewrite vacuumPlaquetteProjectionZero encoding scale
          | vacuumPlaquetteProjectionZero encoding (suc scale) =
    solve-∀

  nonVacuumSectorProjection : Nat → ℚ
  nonVacuumSectorProjection scale =
    T4.plaquetteCoefficientProjector (Canonical.eAt source scale)
    + (T4.plaquetteCoefficientProjector (Canonical.rAt source scale)
    + T4.plaquetteCoefficientProjector (Canonical.bAt source scale))

  sectorProjectionDropsVacuumConstant :
    (encoding : VacuumConstantEncoding) →
    ∀ scale →
    Canonical.sectorProjection trajectory source scale
    ≡ nonVacuumSectorProjection scale
  sectorProjectionDropsVacuumConstant encoding scale
    rewrite vacuumPlaquetteProjectionZero encoding scale =
    solve-∀
      (T4.plaquetteCoefficientProjector (Canonical.eAt source scale))
      (T4.plaquetteCoefficientProjector (Canonical.rAt source scale))
      (T4.plaquetteCoefficientProjector (Canonical.bAt source scale))

  betaProjectedSectorDriftIsIndependentOfVacuumConstant :
    (encoding : VacuumConstantEncoding) →
    ∀ scale →
    Canonical.sectorProjection trajectory source scale
      - Canonical.sectorProjection trajectory source (suc scale)
    ≡
    nonVacuumSectorProjection scale
      - nonVacuumSectorProjection (suc scale)
  betaProjectedSectorDriftIsIndependentOfVacuumConstant encoding scale
    rewrite sectorProjectionDropsVacuumConstant encoding scale
          | sectorProjectionDropsVacuumConstant encoding (suc scale) = refl

record VacuumConstantBetaOrthogonalityBoundary : Set where
  constructor vacuum-constant-beta-orthogonality-boundary
  field
    pureVacuumConstantHasZeroPlaquetteProjection : Bool
    pureVacuumConstantHasZeroPlaquetteDrift : Bool
    betaProjectionCannotRecoverVacuumConstant : Bool
    vacuumConstantNeedsIndependentNormalizationCoordinate : Bool
    plaquetteCouplingFlowDeterminesAbsoluteVacuumConstant : Bool

canonicalVacuumConstantBetaOrthogonalityBoundary :
  VacuumConstantBetaOrthogonalityBoundary
canonicalVacuumConstantBetaOrthogonalityBoundary =
  vacuum-constant-beta-orthogonality-boundary
    true true true true false

betaProjectionCannotRecoverVacuumConstant : Bool
betaProjectionCannotRecoverVacuumConstant = true

vacuumConstantNeedsIndependentNormalizationCoordinate : Bool
vacuumConstantNeedsIndependentNormalizationCoordinate = true
