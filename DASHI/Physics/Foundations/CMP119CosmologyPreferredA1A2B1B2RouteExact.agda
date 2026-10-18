{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119CosmologyPreferredA1A2B1B2RouteExact where

------------------------------------------------------------------------
-- PREFERRED COSMOLOGY ROUTE: A1 / A2 / B1 / B2.
--
-- This owner freezes the shortest route after the 2026-10-03 max-cut:
--
--   A1  D1_R144(gB,gh) = D1_R144(B,h)
--   A2  selected R109 insertion pair -> an actual Wilson/OS-admissible
--       cylinder observable
--   B1  embed(Q_E^R136) <= embed(DGamma_k) + embed(Tail_109(k))
--   B2  c_V < -(M_ERB + Tail_109(k))
--
-- Everything below B1+B2 is already compiler-owned.  In particular the direct
-- R109-tail owner reflects the embedded-real inequality back to the rational
-- R136 sign, and the existing marked-OS / Local-C terminal consumer turns that
-- sign into positive matter acceleration for positive gravity factor.
--
-- IMPORTANT SOURCE BOUNDARY.
-- `SourceNativeOrdinaryCharacteristicPair` deliberately hides the raw pair
-- representation.  There is therefore no lawful definition-by-unfolding from
-- an arbitrary R109 pair to `Configuration -> R`.  A2 is exactly the source
-- receipt which supplies that presentation and proves the selected image is on
-- the published Wilson positive-time/gauge-invariant surface.  We do not invent
-- an evaluator here.
--
-- A1 is already represented exactly by
-- `CanonicalB4R144ReadoutCovariance.signedReadoutCovariant` in the imported
-- canonical R144 owner; no duplicate covariance interface is introduced.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _+_; _≤_; _<_)
import Data.Rational.Properties as ℚP

open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)

import DASHI.Physics.Foundations.CMP119CosmologyE1R144CanonicalB4ReadoutExact as A1
import DASHI.Physics.Foundations.CMP119CosmologyR109FunctionalStressCylinderPresentationExact as Functional
import DASHI.Physics.Foundations.CMP119CosmologyR109WilsonAdmissibleStressCylinderExact as WilsonPinned
import DASHI.Physics.Foundations.CMP119CosmologyEq223VacuumTailThresholdExact as B2
import DASHI.Physics.Foundations.CMP119CosmologyR144R109DirectTailAnchorExact as B1
import DASHI.Physics.Foundations.CMP119CosmologyR144R109ExpectationCompletionMaxCutExact as Tail
import DASHI.Physics.Foundations.CMP119CosmologyRealR136TraceReadoutBridgeExact as Readout
import DASHI.Physics.Foundations.CMP119CosmologySelectedR109RealTailSignCompilerExact as RealSign
import DASHI.Physics.Foundations.CMP119CosmologyEq223DirectTailThresholdToExpansionExact as Terminal

import DASHI.Physics.YangMills.BalabanA2RationalSensitivityToRealContractionRound104Exact as Additive
import DASHI.Physics.YangMills.BalabanSameFamilyStressCauchySchwingerRound109Exact as R109

------------------------------------------------------------------------
-- A2: selected R109 pair -> actual published-OS-admissible cylinder.
--
-- The functional presentation defines the selected observable as the image of
-- the literal R109 `stressInsertion`; this compiler forgets the unnecessary
-- global evaluator and exposes exactly the actual admissible selected cylinder.
------------------------------------------------------------------------

functionalPresentationGivesActualSelectedAdmissibleCylinder =
  Functional.asWilsonAdmissibleR109StressCylinderPresentation

------------------------------------------------------------------------
-- B1+B2 sign compiler.
--
-- B1 supplies the direct embedded-real completion bound.  The already-owned
-- Eq.(2.23) finite source estimate supplies
--
--   DGamma_k <= M_ERB + c_V.
--
-- B2 is literally c_V < -(M_ERB + Tail_109(k)).  First compile B2 to the
-- strict source-plus-tail margin, then monotonicity pushes the finite DGamma
-- under that margin, and finally the existing direct-tail owner reflects the
-- R136 completion back to Q.
------------------------------------------------------------------------

preferredB1B2ForcesNegativeR136 :
  (embedding : Additive.OrderedAdditiveRationalRealEmbedding) →
  (realOrder : RealSign.RealWeakStrictTransitivity) →
  (reflection :
    Readout.NegativeOrderReflectionAtZero (Additive.base embedding)) →
  ∀ {source completed finite start combinedERB vacuumCoefficient} →
  B1.DirectR144R109TailAnchor
    embedding source completed finite start →
  finite ≤ combinedERB + vacuumCoefficient →
  vacuumCoefficient <
    B2.requiredVacuumUpper combinedERB
      (Tail.r109RemainingTail source start) →
  completed < 0ℚ
preferredB1B2ForcesNegativeR136
    embedding realOrder reflection
    {source} {completed} {finite} {start}
    {combinedERB} {vacuumCoefficient}
    directAnchor finiteUpper vacuumThreshold =
  let
    tail = Tail.r109RemainingTail source start

    sourcePlusTailNegative :
      (combinedERB + vacuumCoefficient) + tail < 0ℚ
    sourcePlusTailNegative =
      B2.vacuumBelowRequiredUpperForcesStrictMargin
        combinedERB vacuumCoefficient tail vacuumThreshold

    finitePlusTailBelowSourcePlusTail :
      finite + tail ≤ (combinedERB + vacuumCoefficient) + tail
    finitePlusTailBelowSourcePlusTail =
      ℚP.+-mono-≤ finiteUpper ℚP.≤-refl

    finitePlusTailNegative : finite + tail < 0ℚ
    finitePlusTailNegative =
      ℚP.≤-<-trans
        finitePlusTailBelowSourcePlusTail
        sourcePlusTailNegative
  in
  B1.directTailMarginForcesNegativeRationalCompletion
    embedding realOrder reflection directAnchor finitePlusTailNegative

------------------------------------------------------------------------
-- Architectural receipts.
------------------------------------------------------------------------

a1ExactOwnerIsCanonicalR144B4Readout : Bool
a1ExactOwnerIsCanonicalR144B4Readout = true

a2SelectedPairHasNoInventedIndependentObservableChoice : Bool
a2SelectedPairHasNoInventedIndependentObservableChoice = true

b1IsDirectEmbeddedR136FinitePlusR109TailReceipt : Bool
b1IsDirectEmbeddedR136FinitePlusR109TailReceipt = true

b2IsExactlyVacuumBelowNegativeERBPlusTail : Bool
b2IsExactlyVacuumBelowNegativeERBPlusTail = true

b1b2CompileToNegativeRationalR136 : Bool
b1b2CompileToNegativeRationalR136 = true

terminalConsumerAlreadyCompilesNegativeR136ToMatterAcceleration : Bool
terminalConsumerAlreadyCompilesNegativeR136ToMatterAcceleration = true

preferredRouteIntroducesNoFiniteEqualsContinuumEquality : Bool
preferredRouteIntroducesNoFiniteEqualsContinuumEquality = true

preferredRouteIntroducesNoSecondLorentzianStress : Bool
preferredRouteIntroducesNoSecondLorentzianStress = true
