{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP116TwoSourceTrajectoryRound280Exact where

------------------------------------------------------------------------
-- ROUND280 / R279 TWO-SOURCE SHELL -> R273 CANONICAL TRAJECTORY
--
-- R279 ends in
--
--   |Cov(F,G)| <= C_H * (1/4 * (1/2)^d).
--
-- R273's least-privilege trajectory expects
--
--   |Cov(F,G)| <= A * q^d.
--
-- This file proves the representation-only conversion with
--   A = C_H/4, q = 1/2.
-- No new Yang--Mills estimate is introduced.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; 1ℚ; _*_; _≤_; _<_; NonNegative; nonNegative)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open ℚP using (_<?_)
open import Relation.Binary.PropositionalEquality using (cong; subst; trans)
open import Relation.Nullary.Decidable.Core using (toWitness)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanCMP116TwoSourceSpatialShellRound279Exact as R279
import DASHI.Physics.YangMills.BalabanSharedMarkedAnalyticShellExact as Shared
import DASHI.Physics.YangMills.BalabanClayP2LargeFieldStepVExact as StepV
import DASHI.Physics.YangMills.BalabanTraceKoteckyPreissGeometricExact as Geo
import DASHI.Physics.YangMills.BalabanFiniteInfluenceRowMassPowerExact as Power
import DASHI.Physics.YangMills.BalabanUnifiedPolymerSchwingerNormExact as Unified

halfPowerIsRationalPower : ∀ depth →
  Geo.halfPower depth ≡ Power.rationalPower Geo.half depth
halfPowerIsRationalPower zero = refl
halfPowerIsRationalPower (suc depth)
  rewrite halfPowerIsRationalPower depth =
  ℚP.*-comm Geo.half (Power.rationalPower Geo.half depth)

quarterNonnegative : 0ℚ ≤ StepV.quarter
quarterNonnegative =
  let
    instance
      quarterNN : NonNegative StepV.quarter
      quarterNN = ℚP.normalize-nonNeg 1 4
  in
  ℚP.nonNegative⁻¹ StepV.quarter

halfStrictlyBelowOne : Geo.half < 1ℚ
halfStrictlyBelowOne = toWitness {a? = Geo.half <? 1ℚ} _

record SelectedTwoSourceSpatialTrajectory
    (Volume Root Observable : Set) : Set₁ where
  field
    spatial : R279.CMP116TwoSourceSpatialShell Nat Volume Root Observable
    volumeAtScale : Nat → Volume

open SelectedTwoSourceSpatialTrajectory public

twoSourceAmplitude :
  ∀ {Volume Root Observable} →
  SelectedTwoSourceSpatialTrajectory Volume Root Observable → ℚ
twoSourceAmplitude selected =
  Shared.hessianAnalyticConstant (R279.shared (spatial selected)) * StepV.quarter

twoSourceAmplitudeNonnegative :
  ∀ {Volume Root Observable}
    (selected : SelectedTwoSourceSpatialTrajectory Volume Root Observable) →
  0ℚ ≤ twoSourceAmplitude selected
twoSourceAmplitudeNonnegative selected =
  let
    constant = Shared.hessianAnalyticConstant (R279.shared (spatial selected))
    constantNonnegative =
      Shared.markedConstantNonnegative
        (R279.shared (spatial selected)) Shared.hessianMark

    instance
      constantNN : NonNegative constant
      constantNN = nonNegative constantNonnegative

      quarterNN : NonNegative StepV.quarter
      quarterNN = nonNegative quarterNonnegative

      productNN : NonNegative (constant * StepV.quarter)
      productNN = ℚP.nonNeg*nonNeg⇒nonNeg constant StepV.quarter
  in
  ℚP.nonNegative⁻¹ (constant * StepV.quarter)

twoSourceGeometricBoundCanonical :
  ∀ {Volume Root Observable}
    (selected : SelectedTwoSourceSpatialTrajectory Volume Root Observable)
    scale left right →
  R279.connectedCovarianceMagnitude (spatial selected)
    scale (volumeAtScale selected scale) left right
  ≤ twoSourceAmplitude selected
      * Power.rationalPower Geo.half
          (R279.physicalDistance (spatial selected) left right)
twoSourceGeometricBoundCanonical selected scale left right =
  let
    dataSet = spatial selected
    volume = volumeAtScale selected scale
    depth = R279.physicalDistance dataSet left right
    constant = Shared.hessianAnalyticConstant (R279.shared dataSet)

    sourceBound = R279.connectedCovarianceGeometricBound
      dataSet scale volume left right

    exposePower :
      constant * (StepV.quarter * Geo.halfPower depth)
      ≡ constant *
          (StepV.quarter * Power.rationalPower Geo.half depth)
    exposePower = cong
      (λ power → constant * (StepV.quarter * power))
      (halfPowerIsRationalPower depth)

    reassociate :
      constant * (StepV.quarter * Power.rationalPower Geo.half depth)
      ≡ (constant * StepV.quarter)
          * Power.rationalPower Geo.half depth
    reassociate = ℚRing.solve []
  in
  subst
    (λ upper →
      R279.connectedCovarianceMagnitude dataSet scale volume left right
      ≤ upper)
    (trans exposePower reassociate)
    sourceBound

asQuantitativeCorrelationDecayTrajectory :
  ∀ {Volume Root Observable} →
  SelectedTwoSourceSpatialTrajectory Volume Root Observable →
  Unified.QuantitativeCorrelationDecayTrajectory
asQuantitativeCorrelationDecayTrajectory selected = record
  { Unified.QuantitativeCorrelationDecayTrajectory.State = Nat
  ; Unified.QuantitativeCorrelationDecayTrajectory.Observable = _
  ; Unified.QuantitativeCorrelationDecayTrajectory.Correlation = Nat
  ; Unified.QuantitativeCorrelationDecayTrajectory.correlationProjection = λ scale → scale
  ; Unified.QuantitativeCorrelationDecayTrajectory.stateAtScale = λ scale → scale
  ; Unified.QuantitativeCorrelationDecayTrajectory.physicalDistance =
      R279.physicalDistance (spatial selected)
  ; Unified.QuantitativeCorrelationDecayTrajectory.connectedCorrelationMagnitude =
      λ scale left right →
        R279.connectedCovarianceMagnitude (spatial selected)
          scale (volumeAtScale selected scale) left right
  ; Unified.QuantitativeCorrelationDecayTrajectory.amplitude =
      twoSourceAmplitude selected
  ; Unified.QuantitativeCorrelationDecayTrajectory.ratio = Geo.half
  ; Unified.QuantitativeCorrelationDecayTrajectory.amplitudeNonnegative =
      twoSourceAmplitudeNonnegative selected
  ; Unified.QuantitativeCorrelationDecayTrajectory.ratioNonnegative =
      Geo.halfNonnegative
  ; Unified.QuantitativeCorrelationDecayTrajectory.ratioStrictlyBelowOne =
      halfStrictlyBelowOne
  ; Unified.QuantitativeCorrelationDecayTrajectory.geometricDecayAtEveryScale =
      twoSourceGeometricBoundCanonical selected
  }

round280DyadicRepresentationCompilerLevel : ProofLevel
round280DyadicRepresentationCompilerLevel = machineChecked

round280TwoSourceShellToCanonicalTrajectoryLevel : ProofLevel
round280TwoSourceShellToCanonicalTrajectoryLevel = machineChecked

-- The only physical theorem inherited from this route is R279's literal
-- two-J-direction instantiation of CMP116 differentiated localization.
round280LiteralTwoJDirectionsToSpatialShellLevel : ProofLevel
round280LiteralTwoJDirectionsToSpatialShellLevel =
  R279.round279LiteralTwoJDirectionsToSpatialShellLevel
