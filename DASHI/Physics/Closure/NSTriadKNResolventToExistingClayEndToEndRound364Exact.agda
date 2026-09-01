module DASHI.Physics.Closure.NSTriadKNResolventToExistingClayEndToEndRound364Exact where

------------------------------------------------------------------------
-- ROUND364 / BIDI: NEW RESOLVENT LANE -> EXISTING R23 TERMINAL CLAY STACK
--
-- R363 constructs the exact old `UniformGlobalPhysicalSolutionInputs` once the
-- single Package-A globalization seam is supplied.  R23 already owns every
-- terminal theorem adapter after that object.  This round therefore rebuilds
-- R23's `InRepoClayPathInputs` using the R363-produced global construction and
-- reuses `inRepoPathClosesLiteralFeffermanPeriodicB` unchanged.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ)

import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNPeriodicNavierStokesSubmissionTheoremExact as Legacy
import DASHI.Physics.Closure.NSTriadKNFeffermanPeriodicClayStatementExact as Clay
import DASHI.Physics.Closure.NSTriadKNLuoLegacySubmissionToFeffermanAdapterExact as Adapter
import DASHI.Physics.Closure.NSTriadKNPackageAToLegacyGlobalPhysicalRound363Exact as R363
import DASHI.Physics.Closure.NSTriadKNLuoClayEndToEndCompositionRound23Exact as R23

F : C3.RealField _
F = Rational.rationalRealField

module ResolventToExistingClay
    (Time : Set)
    (initialTime : Time)
    (integrateTo : (Time → ℚ) → Time → ℚ)
    (DerivativeOf :
      (Time → C3.Complex3 F) →
      (Time → C3.Complex3 F) → Set)
    (legacy : Legacy.PeriodicNavierStokesSubmissionCarrier)
    (clay : Clay.FeffermanPeriodicClayCarrier) where

  module Globalization =
    R363.PackageAToLegacyGlobalPhysical
      Time initialTime integrateTo DerivativeOf legacy

  record ExistingTerminalGeometryInputs : Set₁ where
    field
      legacyToLiteralAdapter :
        Adapter.LegacySubmissionToFeffermanAdapter legacy clay

      MeanVelocity : Set
      DatumMeanZero : Clay.SmoothPeriodicDatum clay → Set

      spatialMean : Clay.SmoothPeriodicDatum clay → MeanVelocity
      centeredDatum :
        Clay.SmoothPeriodicDatum clay → Clay.SmoothPeriodicDatum clay

      centeredDatumSmooth :
        (initial : Clay.SmoothPeriodicDatum clay) →
        Clay.DatumSmoothOnThreeTorus clay initial →
        Clay.DatumSmoothOnThreeTorus clay (centeredDatum initial)

      centeredDatumDivergenceFree :
        (initial : Clay.SmoothPeriodicDatum clay) →
        Clay.DatumDivergenceFree clay initial →
        Clay.DatumDivergenceFree clay (centeredDatum initial)

      centeredDatumPeriodic :
        (initial : Clay.SmoothPeriodicDatum clay) →
        Clay.DatumUnitPeriodicInThreeCoordinates clay initial →
        Clay.DatumUnitPeriodicInThreeCoordinates clay (centeredDatum initial)

      centeredDatumHasZeroMean :
        (initial : Clay.SmoothPeriodicDatum clay) →
        DatumMeanZero (centeredDatum initial)

      literalDivergenceFreeToLegacy :
        (initial : Clay.SmoothPeriodicDatum clay) →
        Clay.DatumDivergenceFree clay initial →
        Legacy.DivergenceFreeDatum legacy
          (Adapter.encodeDatum legacyToLiteralAdapter initial)

      literalMeanZeroToLegacy :
        (initial : Clay.SmoothPeriodicDatum clay) →
        DatumMeanZero initial →
        Legacy.MeanZeroDatum legacy
          (Adapter.encodeDatum legacyToLiteralAdapter initial)

      restoreGalileanSolution :
        (viscosity : Clay.Viscosity clay) →
        (initial : Clay.SmoothPeriodicDatum clay) →
        Clay.FeffermanPeriodicGlobalSolutionWitness clay viscosity
          (centeredDatum initial) →
        Clay.FeffermanPeriodicGlobalSolutionWitness clay viscosity initial

  open ExistingTerminalGeometryInputs public

  buildExistingR23Inputs :
    Globalization.UniformResolventGlobalizationInputs →
    ExistingTerminalGeometryInputs →
    R23.InRepoClayPathInputs legacy clay
  buildExistingR23Inputs resolvent terminal = record
    { R23.legacyUniformPhysicalConstruction =
        Globalization.resolventBuildsOldUniformGlobalPhysicalInputs resolvent
    ; R23.legacyToLiteralAdapter = legacyToLiteralAdapter terminal
    ; R23.MeanVelocity = MeanVelocity terminal
    ; R23.DatumMeanZero = DatumMeanZero terminal
    ; R23.spatialMean = spatialMean terminal
    ; R23.centeredDatum = centeredDatum terminal
    ; R23.centeredDatumSmooth = centeredDatumSmooth terminal
    ; R23.centeredDatumDivergenceFree = centeredDatumDivergenceFree terminal
    ; R23.centeredDatumPeriodic = centeredDatumPeriodic terminal
    ; R23.centeredDatumHasZeroMean = centeredDatumHasZeroMean terminal
    ; R23.literalDivergenceFreeToLegacy = literalDivergenceFreeToLegacy terminal
    ; R23.literalMeanZeroToLegacy = literalMeanZeroToLegacy terminal
    ; R23.restoreGalileanSolution = restoreGalileanSolution terminal
    }

  resolventLaneClosesLiteralFeffermanPeriodicB :
    Globalization.UniformResolventGlobalizationInputs →
    ExistingTerminalGeometryInputs →
    Clay.FeffermanPeriodicClayStatementB clay
  resolventLaneClosesLiteralFeffermanPeriodicB resolvent terminal =
    R23.inRepoPathClosesLiteralFeffermanPeriodicB
      (buildExistingR23Inputs resolvent terminal)

round364ExistingR23TerminalCompositionReused : Bool
round364ExistingR23TerminalCompositionReused = true

round364FreshClayAuthorityNeededAfterGlobalization : Bool
round364FreshClayAuthorityNeededAfterGlobalization = false

round364LegacyWitnessAdapterReproved : Bool
round364LegacyWitnessAdapterReproved = false

round364GalileanRestorationReproved : Bool
round364GalileanRestorationReproved = false

round364LiteralFeffermanEndpointClosedConditionally : Bool
round364LiteralFeffermanEndpointClosedConditionally = true

round364LiteralFeffermanEndpointClosedConditionallyIsTrue :
  round364LiteralFeffermanEndpointClosedConditionally ≡ true
round364LiteralFeffermanEndpointClosedConditionallyIsTrue = refl

round364FreshClayAuthorityNeededAfterGlobalizationIsFalse :
  round364FreshClayAuthorityNeededAfterGlobalization ≡ false
round364FreshClayAuthorityNeededAfterGlobalizationIsFalse = refl
