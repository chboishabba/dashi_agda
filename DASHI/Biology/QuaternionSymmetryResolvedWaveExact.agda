module DASHI.Biology.QuaternionSymmetryResolvedWaveExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Julien Flamant, Nicolas Le Bihan, Pierre Chainais,
-- "Time-frequency analysis of bivariate signals",
-- Applied and Computational Harmonic Analysis 46 (2019), 351--383.
-- DOI: 10.1016/j.acha.2017.05.007.
--
-- Heinz Hopf,
-- "Ueber die Abbildungen der dreidimensionalen Sphaere auf die Kugelflaeche".
-- DOI: 10.1007/BF01457962.
--
-- DASHI CONTRIBUTION
--
-- Keep mode extraction and orientation as different mathematical axes.  The
-- coarse spatial frequency is the exact T^2_3 character label, the fine
-- frequency is the existing 3^9 carrier, the vector-wave geometry is a
-- divergence/curl class, and the local orientation is a proof-bearing unit
-- quaternion from QuaternionHopfUnitOrbitExact.
--
-- Unit-quaternion action changes orientation while leaving the spatial mode,
-- fine-frequency address, and geometry class exactly fixed.  These projections
-- are therefore explicit orbit invariants.  Quaternion orientation is not used
-- as a substitute for Fourier/representation decomposition.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Biology.BalancedTernaryFourierModeExact as Fourier
import DASHI.Biology.BalancedTernaryHarmonicCarrierExact as Harmonic
import DASHI.Biology.FiniteTorusVectorWaveGeometryExact as Geometry
import DASHI.Mathematics.Topology.QuaternionHopfUnitOrbitExact as Hopf

record SymmetryResolvedWaveMode : Set where
  constructor symmetryResolvedWaveMode
  field
    spatialMode : Fourier.Mode3x3
    fineFrequency : Harmonic.FineFrequency
    geometryClass : Geometry.FiniteGeometryClass
    orientation : Hopf.UnitQuaternion

open SymmetryResolvedWaveMode public

rotateOrientation :
  Hopf.UnitQuaternion → SymmetryResolvedWaveMode → SymmetryResolvedWaveMode
rotateOrientation unit mode =
  symmetryResolvedWaveMode
    (spatialMode mode)
    (fineFrequency mode)
    (geometryClass mode)
    (Hopf.unitQuaternionCompose (orientation mode) unit)

spatialModeOrbitInvariant : ∀ unit mode →
  spatialMode (rotateOrientation unit mode) ≡ spatialMode mode
spatialModeOrbitInvariant unit mode = refl

fineFrequencyOrbitInvariant : ∀ unit mode →
  fineFrequency (rotateOrientation unit mode) ≡ fineFrequency mode
fineFrequencyOrbitInvariant unit mode = refl

geometryClassOrbitInvariant : ∀ unit mode →
  geometryClass (rotateOrientation unit mode) ≡ geometryClass mode
geometryClassOrbitInvariant unit mode = refl

record OrbitInvariantObservable
  (Observable : Set)
  (observe : SymmetryResolvedWaveMode → Observable) : Set₁ where
  constructor orbitInvariantObservable
  field
    invariant : ∀ unit mode →
      observe (rotateOrientation unit mode) ≡ observe mode

spatialModeInvariantObservable :
  OrbitInvariantObservable Fourier.Mode3x3 spatialMode
spatialModeInvariantObservable =
  orbitInvariantObservable spatialModeOrbitInvariant

fineFrequencyInvariantObservable :
  OrbitInvariantObservable Harmonic.FineFrequency fineFrequency
fineFrequencyInvariantObservable =
  orbitInvariantObservable fineFrequencyOrbitInvariant

geometryInvariantObservable :
  OrbitInvariantObservable Geometry.FiniteGeometryClass geometryClass
geometryInvariantObservable =
  orbitInvariantObservable geometryClassOrbitInvariant

record SymmetryResolvedObservable : Set where
  constructor symmetryResolvedObservable
  field
    modeProjection : Fourier.Mode3x3
    fineProjection : Harmonic.FineFrequency
    geometryProjection : Geometry.FiniteGeometryClass

observeModuloOrientation :
  SymmetryResolvedWaveMode → SymmetryResolvedObservable
observeModuloOrientation mode =
  symmetryResolvedObservable
    (spatialMode mode)
    (fineFrequency mode)
    (geometryClass mode)

symmetryResolvedObservableExt : ∀ {left right} →
  SymmetryResolvedObservable.modeProjection left
    ≡ SymmetryResolvedObservable.modeProjection right →
  SymmetryResolvedObservable.fineProjection left
    ≡ SymmetryResolvedObservable.fineProjection right →
  SymmetryResolvedObservable.geometryProjection left
    ≡ SymmetryResolvedObservable.geometryProjection right →
  left ≡ right
symmetryResolvedObservableExt
    {symmetryResolvedObservable _ _ _}
    {symmetryResolvedObservable _ _ _}
    refl refl refl = refl

observeModuloOrientationInvariant : ∀ unit mode →
  observeModuloOrientation (rotateOrientation unit mode)
  ≡ observeModuloOrientation mode
observeModuloOrientationInvariant unit mode = refl

record QuaternionModeBoundary : Set where
  constructor quaternionModeBoundary
  field
    quaternionOrientationReplacesFourierMode : Set
    quaternionOrientationDoesNotReplaceFourierMode :
      quaternionOrientationReplacesFourierMode → Set

    orientationOrbitErasesSpatialMode : Set
    orientationOrbitDoesNotEraseSpatialMode :
      orientationOrbitErasesSpatialMode → Set

    unitQuaternionActionIsMonsterAction : Set
    unitQuaternionActionIsNotMonsterAction :
      unitQuaternionActionIsMonsterAction → Set

canonicalQuaternionModeBoundary : QuaternionModeBoundary
canonicalQuaternionModeBoundary =
  quaternionModeBoundary
    ⊥ (λ impossible → ⊥)
    ⊥ (λ impossible → ⊥)
    ⊥ (λ impossible → ⊥)
  where
  open import Data.Empty using (⊥)
