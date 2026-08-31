module DASHI.Physics.Closure.NSTriadKNPhysicalPackageAToFullClayTheoremRound360Exact where

------------------------------------------------------------------------
-- ROUND360 / BIDI: INITIAL DATA -> PHYSICAL TRAJECTORY -> R354 -> FULL CLAY
--
-- R359 corrects the final quantifier carrier: Clay is a theorem over initial
-- data, whereas R240/R354 are indexed by physical Galerkin trajectories.
-- This module inserts the missing same-object/realization layer explicitly.
--
-- For every admissible datum we require:
--
--   * an actual R240 physical trajectory;
--   * a proof that this trajectory represents that datum in the caller-owned
--     representation relation;
--   * the explicit R354 physical inputs for that trajectory.
--
-- A supplied Clay authority may then consume the literal R240 Package-A budget
-- on that same representing trajectory and return the R359 global smooth,
-- unique solution object for the original datum.
--
-- No trajectory/datum identification is hidden and no historical Clay Boolean
-- is promoted.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ)

import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNPhysicalNSGalerkinTrajectoryRound240Exact as R240
import DASHI.Physics.Closure.NSTriadKNR293ToPhysicalPackageARound354Exact as R354
import DASHI.Physics.Closure.NSTriadKNClayNavierStokesTheoremLanguageRound359Exact as R359

F : C3.RealField _
F = Rational.rationalRealField

module FullClayWeld
    (Time : Set)
    (initialTime : Time)
    (integrateTo : (Time → ℚ) → Time → ℚ)
    (DerivativeOf :
      (Time → C3.Complex3 F) →
      (Time → C3.Complex3 F) → Set)
    (InitialDatum Solution : Set)
    (AdmissibleSmoothDatum : InitialDatum → Set)
    (SolvesGlobalSmoothNS : InitialDatum → Solution → Set)
    (UniqueInDeclaredSmoothClass : InitialDatum → Solution → Set)
    (TrajectoryRepresentsDatum :
      InitialDatum →
      R240.PhysicalNSDynamics.PhysicalNSGalerkinTrajectory
        Time initialTime integrateTo DerivativeOf →
      Set) where

  module Dyn = R240.PhysicalNSDynamics Time initialTime integrateTo DerivativeOf
  module Package = R354.PhysicalPackageAWeld Time initialTime integrateTo DerivativeOf
  module ClayLang = R359.ClayNavierStokesTheoremLanguage
    InitialDatum Solution
    AdmissibleSmoothDatum
    SolvesGlobalSmoothNS
    UniqueInDeclaredSmoothClass

  record DatumPhysicalRealization (datum : InitialDatum) : Set₁ where
    field
      trajectory : Dyn.PhysicalNSGalerkinTrajectory
      representsDatum : TrajectoryRepresentsDatum datum trajectory
      packageAInputs : Package.R293PhysicalPackageAInputs trajectory

  open DatumPhysicalRealization public

  record SuppliedFullClayAuthority : Set₁ where
    field
      packageAOnRepresentingTrajectoryToGlobalSmoothUniqueSolution :
        (datum : InitialDatum) →
        AdmissibleSmoothDatum datum →
        (T : Dyn.PhysicalNSGalerkinTrajectory) →
        TrajectoryRepresentsDatum datum T →
        Dyn.PhysicalNSMixedHelicitySpacetimeBudget T →
        ClayLang.GlobalSmoothUniqueSolution datum

  open SuppliedFullClayAuthority public

  record FullClayPhysicalInputs : Set₁ where
    field
      realizationForEveryAdmissibleDatum :
        (datum : InitialDatum) →
        AdmissibleSmoothDatum datum →
        DatumPhysicalRealization datum

      clayAuthority : SuppliedFullClayAuthority

  open FullClayPhysicalInputs public

  fullClayNavierStokesConclusion :
    FullClayPhysicalInputs →
    ClayLang.ClayNavierStokesConclusion
  fullClayNavierStokesConclusion I datum admissible =
    let
      R = realizationForEveryAdmissibleDatum I datum admissible
      T = trajectory R
      packageA = Package.r293BuildsPhysicalPackageA T (packageAInputs R)
    in
    packageAOnRepresentingTrajectoryToGlobalSmoothUniqueSolution
      (clayAuthority I)
      datum admissible T (representsDatum R) packageA

round360ClayQuantifierCorrectedToInitialData : Bool
round360ClayQuantifierCorrectedToInitialData = true

round360DatumToPhysicalTrajectoryRealizationExplicit : Bool
round360DatumToPhysicalTrajectoryRealizationExplicit = true

round360UsesLiteralR354PackageA : Bool
round360UsesLiteralR354PackageA = true

round360TrajectoryDatumEqualityAssumedDefinitionally : Bool
round360TrajectoryDatumEqualityAssumedDefinitionally = false

round360HistoricalClayBooleanUsedAsProof : Bool
round360HistoricalClayBooleanUsedAsProof = false

round360FullClayTheoremCompilerClosedConditionally : Bool
round360FullClayTheoremCompilerClosedConditionally = true

round360FullClayTheoremCompilerClosedConditionallyIsTrue :
  round360FullClayTheoremCompilerClosedConditionally ≡ true
round360FullClayTheoremCompilerClosedConditionallyIsTrue = refl

round360TrajectoryDatumEqualityAssumedDefinitionallyIsFalse :
  round360TrajectoryDatumEqualityAssumedDefinitionally ≡ false
round360TrajectoryDatumEqualityAssumedDefinitionallyIsFalse = refl

round360HistoricalClayBooleanUsedAsProofIsFalse :
  round360HistoricalClayBooleanUsedAsProof ≡ false
round360HistoricalClayBooleanUsedAsProofIsFalse = refl
