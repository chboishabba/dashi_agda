{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119CosmologyEq223VacuumTailThresholdExact where

------------------------------------------------------------------------
-- EQ.(2.23) STRICT-MARGIN MAX-CUT.
--
-- The preferred continuum sign theorem consumes
--
--   (M_ERB + c_V) + Tail_R109(k) < 0.
--
-- Once the combined E/R/B envelope M_ERB and the literal Round109 tail are
-- fixed, the only remaining scalar inequality is equivalently supplied by the
-- vacuum coefficient beating their sum:
--
--   c_V < -(M_ERB + Tail_R109(k)).
--
-- This owner packages the forward compiler actually needed downstream.  It
-- does not infer the physical vacuum coefficient: that source-native metric
-- derivative remains the genuine physics leaf.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _+_; _<_; -_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as Ring
open import Relation.Binary.PropositionalEquality using (subst₂)

vacuumBelowNegativeERBPlusTailForcesStrictMargin :
  ∀ combinedERB vacuumCoefficient tail →
  vacuumCoefficient < - (combinedERB + tail) →
  (combinedERB + vacuumCoefficient) + tail < 0ℚ
vacuumBelowNegativeERBPlusTailForcesStrictMargin
    combinedERB vacuumCoefficient tail vacuumThreshold =
  let
    shifted :
      vacuumCoefficient + (combinedERB + tail)
      <
      (- (combinedERB + tail)) + (combinedERB + tail)
    shifted =
      ℚP.+-mono-<-≤ vacuumThreshold ℚP.≤-refl
  in
  subst₂ _<_
    (Ring.solve-∀ combinedERB vacuumCoefficient tail)
    (Ring.solve-∀ combinedERB tail)
    shifted

requiredVacuumUpper : ℚ → ℚ → ℚ
requiredVacuumUpper combinedERB tail = - (combinedERB + tail)

vacuumBelowRequiredUpperForcesStrictMargin :
  ∀ combinedERB vacuumCoefficient tail →
  vacuumCoefficient < requiredVacuumUpper combinedERB tail →
  (combinedERB + vacuumCoefficient) + tail < 0ℚ
vacuumBelowRequiredUpperForcesStrictMargin =
  vacuumBelowNegativeERBPlusTailForcesStrictMargin

preferredStrictMarginReducesToOneVacuumThresholdGivenEnvelope : Bool
preferredStrictMarginReducesToOneVacuumThresholdGivenEnvelope = true

round109TailIsPartOfRequiredVacuumBudget : Bool
round109TailIsPartOfRequiredVacuumBudget = true

rawEq223SourceAloneDeterminesVacuumThreshold : Bool
rawEq223SourceAloneDeterminesVacuumThreshold = false
