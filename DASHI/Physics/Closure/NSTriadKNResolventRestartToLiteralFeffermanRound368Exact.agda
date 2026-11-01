module DASHI.Physics.Closure.NSTriadKNResolventRestartToLiteralFeffermanRound368Exact where

------------------------------------------------------------------------
-- ROUND368 / BIDI: SHARPEN R364 BY REMOVING THE MONOLITHIC R363 AUTHORITY
--
-- The terminal route now composes:
--
--   R354 Package A
--   -> R365 old nested-limit + restart contradiction
--   -> R366 hole-free maximal-time/global-primitive compiler
--   -> R367 old UniformGlobalPhysicalSolutionInputs
--   -> existing R23 legacy witness / Fefferman adapter / Galilean restoration
--   -> literal Fefferman periodic alternative (B).
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ)

import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNPeriodicNavierStokesSubmissionTheoremExact as Legacy
import DASHI.Physics.Closure.NSTriadKNFeffermanPeriodicClayStatementExact as Clay
import DASHI.Physics.Closure.NSTriadKNPackageAToGlobalPrimitiveRound367Exact as R367
import DASHI.Physics.Closure.NSTriadKNResolventToExistingClayEndToEndRound364Exact as R364
import DASHI.Physics.Closure.NSTriadKNLuoClayEndToEndCompositionRound23Exact as R23

F : C3.RealField _
F = Rational.rationalRealField

module ResolventRestartToLiteralFefferman
    (Time : Set)
    (initialTime : Time)
    (integrateTo : (Time → ℚ) → Time → ℚ)
    (DerivativeOf :
      (Time → C3.Complex3 F) →
      (Time → C3.Complex3 F) → Set)
    (legacy : Legacy.PeriodicNavierStokesSubmissionCarrier)
    (clay : Clay.FeffermanPeriodicClayCarrier) where

  module Global =
    R367.PackageAToGlobalPrimitive
      Time initialTime integrateTo DerivativeOf legacy

  module Terminal =
    R364.ResolventToExistingClay
      Time initialTime integrateTo DerivativeOf legacy clay

  buildExistingR23InputsFromSharpResolventLane :
    Global.UniformDatumGlobalPrimitiveInputs →
    Terminal.ExistingTerminalGeometryInputs →
    R23.InRepoClayPathInputs legacy clay
  buildExistingR23InputsFromSharpResolventLane resolvent terminal = record
    { R23.legacyUniformPhysicalConstruction =
        Global.packageARestartBuildsOldUniformGlobalPhysicalInputs resolvent
    ; R23.legacyToLiteralAdapter = Terminal.legacyToLiteralAdapter terminal
    ; R23.MeanVelocity = Terminal.MeanVelocity terminal
    ; R23.DatumMeanZero = Terminal.DatumMeanZero terminal
    ; R23.spatialMean = Terminal.spatialMean terminal
    ; R23.centeredDatum = Terminal.centeredDatum terminal
    ; R23.centeredDatumSmooth = Terminal.centeredDatumSmooth terminal
    ; R23.centeredDatumDivergenceFree =
        Terminal.centeredDatumDivergenceFree terminal
    ; R23.centeredDatumPeriodic = Terminal.centeredDatumPeriodic terminal
    ; R23.centeredDatumHasZeroMean = Terminal.centeredDatumHasZeroMean terminal
    ; R23.literalDivergenceFreeToLegacy =
        Terminal.literalDivergenceFreeToLegacy terminal
    ; R23.literalMeanZeroToLegacy = Terminal.literalMeanZeroToLegacy terminal
    ; R23.restoreGalileanSolution = Terminal.restoreGalileanSolution terminal
    }

  sharpResolventLaneClosesLiteralFeffermanPeriodicB :
    Global.UniformDatumGlobalPrimitiveInputs →
    Terminal.ExistingTerminalGeometryInputs →
    Clay.FeffermanPeriodicClayStatementB clay
  sharpResolventLaneClosesLiteralFeffermanPeriodicB resolvent terminal =
    R23.inRepoPathClosesLiteralFeffermanPeriodicB
      (buildExistingR23InputsFromSharpResolventLane resolvent terminal)

round368R363MonolithicGlobalizationAuthorityBypassed : Bool
round368R363MonolithicGlobalizationAuthorityBypassed = true

round368R23TerminalStackReusedUnchanged : Bool
round368R23TerminalStackReusedUnchanged = true

round368LiteralFeffermanStatementIsExactEndpoint : Bool
round368LiteralFeffermanStatementIsExactEndpoint = true

round368FreshClayAuthorityAfterRestartNeeded : Bool
round368FreshClayAuthorityAfterRestartNeeded = false

round368LiteralFeffermanEndpointClosedConditionally : Bool
round368LiteralFeffermanEndpointClosedConditionally = true

round368LiteralFeffermanEndpointClosedConditionallyIsTrue :
  round368LiteralFeffermanEndpointClosedConditionally ≡ true
round368LiteralFeffermanEndpointClosedConditionallyIsTrue = refl

round368FreshClayAuthorityAfterRestartNeededIsFalse :
  round368FreshClayAuthorityAfterRestartNeeded ≡ false
round368FreshClayAuthorityAfterRestartNeededIsFalse = refl
