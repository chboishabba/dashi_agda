module DASHI.Physics.Closure.NSTriadKNGlobalClayConclusionRound357Exact where

------------------------------------------------------------------------
-- ROUND357 / BIDI: GLOBAL THEOREM SHAPE AFTER THE CLAY AUTHORITY IS SUPPLIED
--
-- R356 handles one actual physical NS Galerkin trajectory.  The global Clay
-- theorem shape therefore requires exactly the two families one would expect:
--
--   * for every physical trajectory, the explicit R354 physical inputs that
--     build the literal R240 Package-A budget;
--   * one supplied Clay authority consuming that exact budget.
--
-- The conclusion remains chosen by the authority.  This module does not invent
-- a surrogate definition of "Clay solved" and does not rewrite historical
-- governance flags.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ)

import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNPhysicalNSGalerkinTrajectoryRound240Exact as R240
import DASHI.Physics.Closure.NSTriadKNR293ToPhysicalPackageARound354Exact as R354
import DASHI.Physics.Closure.NSTriadKNPhysicalPackageAToClayAuthorityRound356Exact as R356

F : C3.RealField _
F = Rational.rationalRealField

module GlobalClayConclusion
    (Time : Set)
    (initialTime : Time)
    (integrateTo : (Time → ℚ) → Time → ℚ)
    (DerivativeOf :
      (Time → C3.Complex3 F) →
      (Time → C3.Complex3 F) → Set) where

  module Dyn = R240.PhysicalNSDynamics Time initialTime integrateTo DerivativeOf
  module Weld = R354.PhysicalPackageAWeld Time initialTime integrateTo DerivativeOf
  module Clay = R356.PhysicalPackageAToClay Time initialTime integrateTo DerivativeOf

  record GlobalResolventClayInputs
      (ClayConclusion : Dyn.PhysicalNSGalerkinTrajectory → Set) : Set₁ where
    field
      clayAuthority : Clay.SuppliedClayNavierStokesAuthority ClayConclusion
      physicalInputsForEveryTrajectory :
        (T : Dyn.PhysicalNSGalerkinTrajectory) →
        Weld.R293PhysicalPackageAInputs T

  open GlobalResolventClayInputs public

  globalClayConclusion :
    (ClayConclusion : Dyn.PhysicalNSGalerkinTrajectory → Set) →
    GlobalResolventClayInputs ClayConclusion →
    (T : Dyn.PhysicalNSGalerkinTrajectory) →
    ClayConclusion T
  globalClayConclusion ClayConclusion I T =
    Clay.r293PhysicalInputsToClay
      ClayConclusion
      (clayAuthority I)
      T
      (physicalInputsForEveryTrajectory I T)

round357GlobalTheoremNeedsNoNewCompilerAfterR356 : Bool
round357GlobalTheoremNeedsNoNewCompilerAfterR356 = true

round357GlobalPhysicalPremisesRemainExplicit : Bool
round357GlobalPhysicalPremisesRemainExplicit = true

round357ClayConclusionMeaningInventedLocally : Bool
round357ClayConclusionMeaningInventedLocally = false

round357HistoricalPromotionFlagsRewritten : Bool
round357HistoricalPromotionFlagsRewritten = false

round357GlobalClayConclusionCompilerClosedConditionally : Bool
round357GlobalClayConclusionCompilerClosedConditionally = true

round357GlobalClayConclusionCompilerClosedConditionallyIsTrue :
  round357GlobalClayConclusionCompilerClosedConditionally ≡ true
round357GlobalClayConclusionCompilerClosedConditionallyIsTrue = refl

round357ClayConclusionMeaningInventedLocallyIsFalse :
  round357ClayConclusionMeaningInventedLocally ≡ false
round357ClayConclusionMeaningInventedLocallyIsFalse = refl

round357HistoricalPromotionFlagsRewrittenIsFalse :
  round357HistoricalPromotionFlagsRewritten ≡ false
round357HistoricalPromotionFlagsRewrittenIsFalse = refl
