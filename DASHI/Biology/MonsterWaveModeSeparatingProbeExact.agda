module DASHI.Biology.MonsterWaveModeSeparatingProbeExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Robert A. Wilson,
-- "The Odd-Local Subgroups of the Monster",
-- Journal of the Australian Mathematical Society 44 (1988), 1--16.
-- DOI: 10.1017/S1446788700031323.
--
-- Thomas Breuer, Kay Magaard, Robert A. Wilson,
-- "Verification of the Conjugacy Classes and Ordinary Character Table of the
-- Monster" (2024).
-- arXiv DOI: 10.48550/arXiv.2412.12182.
--
-- DASHI CONTRIBUTION
--
-- Make the proposed Monster/wave cross-pollination fail closed.  A candidate
-- mode carries two independent coordinates: a genuine order-three Monster lane
-- (3A, 3B, or 3C, observed here through its already-recorded normalizer kind)
-- and a proposed finite physical wave geometry.  A two-probe family separates
-- the candidate exactly.
--
-- Consequently an order-three lane by itself cannot determine planar, radial,
-- rotational/transverse, or spiral geometry.  Any later Monster-derived mode
-- claim must supply an actual action plus representation/character evidence and
-- a physical geometry probe; period-three arithmetic is not enough.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl; cong)
open import Data.Empty using (⊥)

import DASHI.Biology.MonsterSubgroupBranchingBenchmarksExact as Monster
import DASHI.Biology.FiniteTorusVectorWaveGeometryExact as Geometry
import DASHI.Physics.Common.SeparatingProbeFamilyExact as Probe

record MonsterWaveModeCandidate : Set where
  constructor monsterWaveModeCandidate
  field
    orderThreeClass : Monster.OrderThreeClass
    proposedGeometry : Geometry.FiniteGeometryClass

open MonsterWaveModeCandidate public

candidateExt : ∀ {left right} →
  orderThreeClass left ≡ orderThreeClass right →
  proposedGeometry left ≡ proposedGeometry right →
  left ≡ right
candidateExt
  {monsterWaveModeCandidate _ _}
  {monsterWaveModeCandidate _ _}
  refl refl = refl

normalizerInjective : ∀ {left right} →
  Monster.normalizerKind left ≡ Monster.normalizerKind right → left ≡ right
normalizerInjective {Monster.class3A} {Monster.class3A} equality = refl
normalizerInjective {Monster.class3A} {Monster.class3B} ()
normalizerInjective {Monster.class3A} {Monster.class3C} ()
normalizerInjective {Monster.class3B} {Monster.class3A} ()
normalizerInjective {Monster.class3B} {Monster.class3B} equality = refl
normalizerInjective {Monster.class3B} {Monster.class3C} ()
normalizerInjective {Monster.class3C} {Monster.class3A} ()
normalizerInjective {Monster.class3C} {Monster.class3B} ()
normalizerInjective {Monster.class3C} {Monster.class3C} equality = refl

data ModeProbe : Set where
  normalizerProbe : ModeProbe
  geometryProbe : ModeProbe

data ModeObservation : Set where
  normalizerObservation : Monster.ThreeLocalNormalizerKind → ModeObservation
  geometryObservation : Geometry.FiniteGeometryClass → ModeObservation

observeMode : ModeProbe → MonsterWaveModeCandidate → ModeObservation
observeMode normalizerProbe candidate =
  normalizerObservation (Monster.normalizerKind (orderThreeClass candidate))
observeMode geometryProbe candidate =
  geometryObservation (proposedGeometry candidate)

normalizerObservationInjective : ∀ {left right} →
  normalizerObservation left ≡ normalizerObservation right → left ≡ right
normalizerObservationInjective refl = refl

geometryObservationInjective : ∀ {left right} →
  geometryObservation left ≡ geometryObservation right → left ≡ right
geometryObservationInjective refl = refl

modeProbesSeparate : ∀ left right →
  ((probe : ModeProbe) → observeMode probe left ≡ observeMode probe right) →
  left ≡ right
modeProbesSeparate left right agreement =
  candidateExt
    (normalizerInjective
      (normalizerObservationInjective (agreement normalizerProbe)))
    (geometryObservationInjective (agreement geometryProbe))

monsterWaveModeSeparatingSystem :
  Probe.SeparatingProbeSystem MonsterWaveModeCandidate ModeObservation
monsterWaveModeSeparatingSystem =
  Probe.separatingProbeSystem ModeProbe observeMode modeProbesSeparate

class3APlanarCandidate : MonsterWaveModeCandidate
class3APlanarCandidate =
  monsterWaveModeCandidate Monster.class3A Geometry.planarClass

class3ARotationalCandidate : MonsterWaveModeCandidate
class3ARotationalCandidate =
  monsterWaveModeCandidate Monster.class3A Geometry.rotationalTransverseClass

sameMonsterLaneDifferentGeometryClass :
  orderThreeClass class3APlanarCandidate
  ≡ orderThreeClass class3ARotationalCandidate
sameMonsterLaneDifferentGeometryClass = refl

planarNotRotational :
  Geometry.planarClass ≡ Geometry.rotationalTransverseClass → ⊥
planarNotRotational ()

sameMonsterLaneDoesNotDetermineGeometry :
  proposedGeometry class3APlanarCandidate
  ≡ proposedGeometry class3ARotationalCandidate → ⊥
sameMonsterLaneDoesNotDetermineGeometry = planarNotRotational

record MonsterWaveExtractionBoundary : Set where
  constructor monsterWaveExtractionBoundary
  field
    orderThreePeriodDeterminesPhysicalGeometry : Set
    orderThreePeriodDoesNotDeterminePhysicalGeometry :
      orderThreePeriodDeterminesPhysicalGeometry → ⊥

    currentTernaryCarrierConstructsMonsterAction : Set
    currentTernaryCarrierDoesNotConstructMonsterAction :
      currentTernaryCarrierConstructsMonsterAction → ⊥

    dimensionMatchIsModeIdentification : Set
    dimensionMatchIsNotModeIdentification :
      dimensionMatchIsModeIdentification → ⊥

canonicalMonsterWaveExtractionBoundary : MonsterWaveExtractionBoundary
canonicalMonsterWaveExtractionBoundary =
  monsterWaveExtractionBoundary
    ⊥ (λ impossible → impossible)
    ⊥ (λ impossible → impossible)
    ⊥ (λ impossible → impossible)
