module DASHI.Physics.Closure.NSTriadKNR650Rational345RealODEMaxCutRound833Exact where

------------------------------------------------------------------------
-- R833 / R830 REAL-ODE MAX-CUT AFTER ROUND71/74 CROSS-POLLINATION
--
-- Already repository-proved:
--   * fixed autonomous reality-preserving Galerkin vector field (R71);
--   * transverse subspace invariance (R71);
--   * exact degree <= 2 expression for the literal RHS (R71);
--   * corrected finite rational slot chart (R74);
--   * quantitative local-Lipschitz majorant through that finite chart (R74).
--
-- Standard complete-real C1/Picard and negative-integral transport are
-- separately source-written in dashi_lean4 Rational345LocalODE,
-- Rational345QuadraticODE and Rational345ShortTime.
--
-- Remaining NS-specific bridge:
--   O1. actual Round71 physical RHS = the finite-chart polynomial / complete
--       real quadratic field;
--   O2. selected R828 displacement/rate bounds apply to that solution and the
--       selected rate is the same R829/R815 scalar.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)

import DASHI.Physics.Closure.NSTriadKNFixedCanonicalRealityVectorFieldRound71Exact as Field
import DASHI.Physics.Closure.NSTriadKNFixedCanonicalTransverseInvariantRound71Exact as Transverse
import DASHI.Physics.Closure.NSTriadKNFixedCanonicalVectorFieldDegreeTwoRound71Exact as Degree
import DASHI.Physics.Closure.NSTriadKNFiniteRationalSlotAssignmentBridgeRound74Exact as Chart

data RealODELeaf : Set where
  physicalRHSToFiniteRealQuadraticField : RealODELeaf
  selectedR828BoundsAndRateTransport : RealODELeaf

realODELeafClosed : RealODELeaf → Bool
realODELeafClosed physicalRHSToFiniteRealQuadraticField =
  Chart.round74PhysicalRHSAgreesWithFiniteChartPolynomial
realODELeafClosed selectedR828BoundsAndRateTransport = false

realODELeafCount : Nat
realODELeafCount = suc (suc zero)

fixedAutonomousRealityFieldConstructed : Bool
fixedAutonomousRealityFieldConstructed =
  Field.round71FullSpaceRealityVectorFieldConstructed

transverseSubspaceInvariant : Bool
transverseSubspaceInvariant =
  Transverse.round71FixedCanonicalTransverseSubspaceInvariant

literalRHSExactDegreeAtMostTwo : Bool
literalRHSExactDegreeAtMostTwo =
  Degree.round71FixedCanonicalVectorFieldDegreeAtMostTwo

literalDegreeTwoExpressionEvaluatesToRHS : Bool
literalDegreeTwoExpressionEvaluatesToRHS =
  Degree.round71DegreeTwoExpressionEvaluatesToLiteralRHS

finiteAssignmentChartConstructed : Bool
finiteAssignmentChartConstructed =
  Chart.round74CorrectedFiniteRationalStateHasExecutableAssignmentChart

finiteChartLipschitzMajorantConstructed : Bool
finiteChartLipschitzMajorantConstructed =
  Chart.round74Round28LipschitzMajorantAppliesThroughFiniteChart

realODELeafCountIsTwo : realODELeafCount ≡ suc (suc zero)
realODELeafCountIsTwo = refl

fixedAutonomousRealityFieldConstructedIsTrue :
  fixedAutonomousRealityFieldConstructed ≡ true
fixedAutonomousRealityFieldConstructedIsTrue = refl

transverseSubspaceInvariantIsTrue :
  transverseSubspaceInvariant ≡ true
transverseSubspaceInvariantIsTrue = refl

literalRHSExactDegreeAtMostTwoIsTrue :
  literalRHSExactDegreeAtMostTwo ≡ true
literalRHSExactDegreeAtMostTwoIsTrue = refl

finiteChartLipschitzMajorantConstructedIsTrue :
  finiteChartLipschitzMajorantConstructed ≡ true
finiteChartLipschitzMajorantConstructedIsTrue = refl

clayPromotion : Bool
clayPromotion = false
