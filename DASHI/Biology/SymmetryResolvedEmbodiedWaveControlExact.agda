module DASHI.Biology.SymmetryResolvedEmbodiedWaveControlExact where

open import DASHI.Core.Prelude

import DASHI.Physics.Common.FiniteThreeCycleTorusExact as Torus
import DASHI.Biology.BalancedTernaryHarmonicCarrierExact as Harmonic
import DASHI.Biology.ObserverRelativeReachableSubfabricExact as Reach

------------------------------------------------------------------------
-- SYMMETRY-RESOLVED EMBODIED WAVE CONTROL
--
-- Cross-pollination seam between the finite T^2_3 / 3^9 harmonic carrier and
-- the embodied reachable-subfabric layer.  Spatial mode, fine harmonic
-- address, geometric class, and body context remain separate coordinates.
--
-- Source context for finite harmonic analysis:
-- Audrey Terras, "Fourier Analysis on Finite Groups and Applications".
-- DOI: 10.1017/CBO9780511626265.
--
-- Empirical geometry calibration:
-- Anup Das, Erfan Zabeh, Bard Ermentrout, Joshua Jacobs,
-- "Planar, spiral, and concentric traveling waves distinguish behavioral
-- states in human memory", Nature Communications 17 (2026), 5143.
-- DOI: 10.1038/s41467-026-71386-z.
--
-- The finite theorem below does not identify T^2_3 with cortex, nor does it
-- claim that body state breaks a literal physical symmetry of a measured field.
-- It proves that raw wave symmetry need not be a symmetry of an embodied
-- consumer's effective reachability map.
------------------------------------------------------------------------

data GeometryClass : Set where
  planarGeometry sourceSinkGeometry rotationalGeometry spiralGeometry : GeometryClass

record SymmetryResolvedMode : Set where
  constructor symmetryResolvedMode
  field
    coarseMode : Torus.Torus3x3
    fineFrequency : Harmonic.FineFrequency
    geometry : GeometryClass

open SymmetryResolvedMode public

translateFirstMode : SymmetryResolvedMode → SymmetryResolvedMode
translateFirstMode mode =
  symmetryResolvedMode
    (Torus.translateFirst (coarseMode mode))
    (fineFrequency mode)
    (geometry mode)

fineFrequencyPreservedByTranslation : (mode : SymmetryResolvedMode) →
  fineFrequency (translateFirstMode mode) ≡ fineFrequency mode
fineFrequencyPreservedByTranslation mode = refl

geometryPreservedByTranslation : (mode : SymmetryResolvedMode) →
  geometry (translateFirstMode mode) ≡ geometry mode
geometryPreservedByTranslation mode = refl

record FirstTranslationOrbitWitness
    (left right : SymmetryResolvedMode) : Set where
  constructor firstTranslationOrbitWitness
  field
    translatedCoarse : coarseMode right ≡ Torus.translateFirst (coarseMode left)
    sameFine : fineFrequency right ≡ fineFrequency left
    sameGeometry : geometry right ≡ geometry left

translatedModeIsRawSymmetryRelated : (mode : SymmetryResolvedMode) →
  FirstTranslationOrbitWitness mode (translateFirstMode mode)
translatedModeIsRawSymmetryRelated mode =
  firstTranslationOrbitWitness refl refl refl

-- A finite consumer gate.  The geometric coordinate and body coordinate are
-- independently visible to the consumer; the same structural carrier and fine
-- harmonic content therefore need not induce the same effective incidence.
effectiveIncidence : Reach.BodyContext → GeometryClass → Bool
effectiveIncidence Reach.regulatedContext planarGeometry = true
effectiveIncidence Reach.regulatedContext sourceSinkGeometry = true
effectiveIncidence Reach.regulatedContext rotationalGeometry = true
effectiveIncidence Reach.regulatedContext spiralGeometry = true
effectiveIncidence Reach.mobilisedContext planarGeometry = true
effectiveIncidence Reach.mobilisedContext sourceSinkGeometry = false
effectiveIncidence Reach.mobilisedContext rotationalGeometry = false
effectiveIncidence Reach.mobilisedContext spiralGeometry = false

modeIncidence : Reach.BodyContext → SymmetryResolvedMode → Bool
modeIncidence body mode = effectiveIncidence body (geometry mode)

sameRawSymmetryCanSplitEmbodiedReach : (mode : SymmetryResolvedMode) →
  geometry mode ≡ sourceSinkGeometry →
  modeIncidence Reach.regulatedContext mode
  ≡ modeIncidence Reach.mobilisedContext (translateFirstMode mode) → ⊥
sameRawSymmetryCanSplitEmbodiedReach
  (symmetryResolvedMode coarse fine sourceSinkGeometry) refl ()

sameRawSymmetryCanSplitRotationalReach : (mode : SymmetryResolvedMode) →
  geometry mode ≡ rotationalGeometry →
  modeIncidence Reach.regulatedContext mode
  ≡ modeIncidence Reach.mobilisedContext (translateFirstMode mode) → ⊥
sameRawSymmetryCanSplitRotationalReach
  (symmetryResolvedMode coarse fine rotationalGeometry) refl ()

record SymmetryResolvedEmbodimentBoundary : Set where
  constructor symmetryResolvedEmbodimentBoundary
  field
    rawWaveSymmetryDeterminesEmbodiedReachability : Bool
    bodyContextCanRefineFunctionalEquivalence : Bool
    finiteModeIsMeasuredCorticalMode : Bool
    functionalAsymmetryIsLiteralGaugeSymmetryBreaking : Bool

canonicalSymmetryResolvedEmbodimentBoundary : SymmetryResolvedEmbodimentBoundary
canonicalSymmetryResolvedEmbodimentBoundary =
  symmetryResolvedEmbodimentBoundary false true false false
