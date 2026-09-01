module DASHI.Physics.Closure.NSTriadKNPackageAToLegacyGlobalPhysicalRound363Exact where

------------------------------------------------------------------------
-- ROUND363 / BIDI: PACKAGE A -> OLD GLOBAL-PHYSICAL PRIMITIVE INPUTS
--
-- R361 temporarily allowed a direct same-instance Clay authority after R354.
-- Repository archaeology shows that the older R23 terminal route already owns
-- all theorem-language work after a `GlobalPhysicalSolutionPrimitiveInputs`
-- object exists: infinite maximal time -> global smooth velocity/pressure ->
-- legacy submission witness -> literal Fefferman witness -> Galilean restore.
--
-- Therefore the shortest honest reuse frontier is not a fresh
-- PackageA -> Fefferman theorem.  It is the single analytic/globalization seam
--
--   literal R240 Package A
--     -> old GlobalPhysicalSolutionPrimitiveInputs.
--
-- This module isolates exactly that seam.  It does not pretend that an
-- integrated mixed-helicity budget definitionally contains infinite maximal
-- time, pressure recovery, or smooth bootstrap data.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ)

import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNPhysicalNSGalerkinTrajectoryRound240Exact as R240
import DASHI.Physics.Closure.NSTriadKNR293ToPhysicalPackageARound354Exact as R354
import DASHI.Physics.Closure.NSTriadKNPeriodicNavierStokesSubmissionTheoremExact as Legacy
import DASHI.Physics.Closure.NSTriadKNLuoGlobalPhysicalSolutionReductionExact as Global

F : C3.RealField _
F = Rational.rationalRealField

module PackageAToLegacyGlobalPhysical
    (Time : Set)
    (initialTime : Time)
    (integrateTo : (Time → ℚ) → Time → ℚ)
    (DerivativeOf :
      (Time → C3.Complex3 F) →
      (Time → C3.Complex3 F) → Set)
    (legacy : Legacy.PeriodicNavierStokesSubmissionCarrier) where

  module Dyn = R240.PhysicalNSDynamics Time initialTime integrateTo DerivativeOf
  module Weld = R354.PhysicalPackageAWeld Time initialTime integrateTo DerivativeOf

  record LegacyDatumPhysicalRealization
      (initial : Legacy.SmoothPeriodicDatum legacy) : Set₁ where
    field
      trajectory : Dyn.PhysicalNSGalerkinTrajectory
      representsLegacyDatum :
        Dyn.PhysicalNSGalerkinTrajectory →
        Legacy.SmoothPeriodicDatum legacy → Set
      trajectoryRepresentsInitial :
        representsLegacyDatum trajectory initial
      r354Inputs : Weld.R293PhysicalPackageAInputs trajectory

  open LegacyDatumPhysicalRealization public

  record PackageAGlobalizationAuthority : Set₁ where
    field
      packageAToGlobalPrimitiveInputs :
        (initial : Legacy.SmoothPeriodicDatum legacy) →
        (R : LegacyDatumPhysicalRealization initial) →
        Dyn.PhysicalNSMixedHelicitySpacetimeBudget (trajectory R) →
        Global.GlobalPhysicalSolutionPrimitiveInputs legacy initial

  open PackageAGlobalizationAuthority public

  realizationBuildsGlobalPrimitiveInputs :
    PackageAGlobalizationAuthority →
    (initial : Legacy.SmoothPeriodicDatum legacy) →
    LegacyDatumPhysicalRealization initial →
    Global.GlobalPhysicalSolutionPrimitiveInputs legacy initial
  realizationBuildsGlobalPrimitiveInputs authority initial R =
    packageAToGlobalPrimitiveInputs authority initial R
      (Weld.r293BuildsPhysicalPackageA (trajectory R) (r354Inputs R))

  record UniformResolventGlobalizationInputs : Set₁ where
    field
      realizationForDatum :
        (initial : Legacy.SmoothPeriodicDatum legacy) →
        Legacy.DivergenceFreeDatum legacy initial →
        Legacy.MeanZeroDatum legacy initial →
        LegacyDatumPhysicalRealization initial

      globalizationAuthority : PackageAGlobalizationAuthority

  open UniformResolventGlobalizationInputs public

  resolventBuildsOldUniformGlobalPhysicalInputs :
    UniformResolventGlobalizationInputs →
    Global.UniformGlobalPhysicalSolutionInputs legacy
  resolventBuildsOldUniformGlobalPhysicalInputs I = record
    { Global.primitiveInputsForDatum =
        λ initial divergenceFree meanZero →
          realizationBuildsGlobalPrimitiveInputs
            (globalizationAuthority I)
            initial
            (realizationForDatum I initial divergenceFree meanZero)
    }

round363R354PackageAReusedLiterally : Bool
round363R354PackageAReusedLiterally = true

round363OldGlobalPhysicalPrimitiveInterfaceReused : Bool
round363OldGlobalPhysicalPrimitiveInterfaceReused = true

round363PackageAContainsInfiniteMaximalTimeDefinitionally : Bool
round363PackageAContainsInfiniteMaximalTimeDefinitionally = false

round363PackageAContainsPressureRecoveryDefinitionally : Bool
round363PackageAContainsPressureRecoveryDefinitionally = false

round363SingleGlobalizationAuthorityIsLiveSeam : Bool
round363SingleGlobalizationAuthorityIsLiveSeam = true

round363OldUniformGlobalPhysicalCompilerClosedConditionally : Bool
round363OldUniformGlobalPhysicalCompilerClosedConditionally = true

round363OldUniformGlobalPhysicalCompilerClosedConditionallyIsTrue :
  round363OldUniformGlobalPhysicalCompilerClosedConditionally ≡ true
round363OldUniformGlobalPhysicalCompilerClosedConditionallyIsTrue = refl

round363PackageAContainsInfiniteMaximalTimeDefinitionallyIsFalse :
  round363PackageAContainsInfiniteMaximalTimeDefinitionally ≡ false
round363PackageAContainsInfiniteMaximalTimeDefinitionallyIsFalse = refl

round363PackageAContainsPressureRecoveryDefinitionallyIsFalse :
  round363PackageAContainsPressureRecoveryDefinitionally ≡ false
round363PackageAContainsPressureRecoveryDefinitionallyIsFalse = refl
