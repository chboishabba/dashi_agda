{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119AntigravityRealCurvatureF2PointBridgeExact where

open import Agda.Builtin.Equality using (_≡_)
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import Data.Rational.Base as ℚ using (ℚ; 0ℚ)
open import DASHI.Foundations.RealAnalysisAxioms using
  (ℝ; 0ℝ; _<ℝ_)

import DASHI.Physics.Foundations.CMP119AntigravityCurvatureF2PositivityExact as RationalF2
import DASHI.Physics.Foundations.CMP119ClassicalCurvatureTenMetricVariationExact as Curvature
import DASHI.Physics.YangMills.BalabanRationalBetaCertificateToRealSlopeRound102Exact as Embed

------------------------------------------------------------------------
-- RATIONAL CURVATURE CERTIFICATE -> REAL POSITIVE F^2 POINT
--
-- The existing six-curvature theorem already proves strict positivity of the
-- normalized rational F^2 value from one positive curvature component.  The
-- physical real source lane only needs a same-object value weld at that
-- configuration; ordered embedding then transports strict positivity.
------------------------------------------------------------------------

record RealCurvatureF2PointBridge
    (Configuration : Set)
    (embedding : Embed.OrderedRationalRealEmbedding) : Set₁ where
  field
    rationalFamily :
      RationalF2.FiniteCurvatureF2Family Configuration

    witnessConfiguration : Configuration

    rationalPositiveCurvature :
      RationalF2.PositiveCurvatureEnergyWitness
        (Curvature.curvatureAt
          (RationalF2.curvature rationalFamily)
          witnessConfiguration)

    realFieldStrengthSquare :
      Configuration → ℝ

    realF2AtWitnessIsEmbeddedRationalF2 :
      realFieldStrengthSquare witnessConfiguration
      ≡
      Embed.embed embedding
        (RationalF2.fieldStrengthSquare
          rationalFamily witnessConfiguration)

open RealCurvatureF2PointBridge public

realF2PositiveAtWitness :
  ∀ {Configuration embedding}
    (bridge : RealCurvatureF2PointBridge Configuration embedding) →
  0ℝ <ℝ realFieldStrengthSquare bridge (witnessConfiguration bridge)
realF2PositiveAtWitness {embedding = embedding} bridge =
  let
    rationalPositive =
      RationalF2.normalizedCurvatureF2PositiveFromF01
        (rationalPositiveCurvature bridge)

    embeddedPositive :
      Embed.embed embedding (0ℚ)
      <ℝ
      Embed.embed embedding
        (RationalF2.fieldStrengthSquare
          (rationalFamily bridge)
          (witnessConfiguration bridge))
    embeddedPositive =
      Embed.strictOrderPreserving embedding rationalPositive
  in
  subst
    (λ left →
      left <ℝ realFieldStrengthSquare bridge (witnessConfiguration bridge))
    (Embed.zeroExact embedding)
    (subst
      (λ right →
        Embed.embed embedding (0ℚ) <ℝ right)
      (sym (realF2AtWitnessIsEmbeddedRationalF2 bridge))
      embeddedPositive)
