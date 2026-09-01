module DASHI.Physics.Closure.NSTriadKNPhysicalPackageAToClayAuthorityRound356Exact where

------------------------------------------------------------------------
-- ROUND356 / BIDI: LITERAL R240 PACKAGE A -> SUPPLIED CLAY AUTHORITY
--
-- The repository's historical Clay-facing receipts are governance/target
-- surfaces and deliberately hard-code non-promotion.  They are not theorem
-- types to be mutated when a new proof route arrives.
--
-- Under the user's present research assumption that the Clay-level theorem is
-- already available, the honest theorem-facing boundary is therefore an
-- explicit authority consuming the EXACT R240 physical Package-A object and
-- returning the authority's declared Clay conclusion for the SAME trajectory.
--
-- No Boolean promotion flag is used as mathematical evidence.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ)

import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNPhysicalNSGalerkinTrajectoryRound240Exact as R240
import DASHI.Physics.Closure.NSTriadKNR293ToPhysicalPackageARound354Exact as R354

F : C3.RealField _
F = Rational.rationalRealField

module PhysicalPackageAToClay
    (Time : Set)
    (initialTime : Time)
    (integrateTo : (Time → ℚ) → Time → ℚ)
    (DerivativeOf :
      (Time → C3.Complex3 F) →
      (Time → C3.Complex3 F) → Set) where

  module Dyn = R240.PhysicalNSDynamics Time initialTime integrateTo DerivativeOf
  module Weld = R354.PhysicalPackageAWeld Time initialTime integrateTo DerivativeOf

  record SuppliedClayNavierStokesAuthority
      (ClayConclusion : Dyn.PhysicalNSGalerkinTrajectory → Set) : Set₁ where
    field
      packageAToClay :
        (T : Dyn.PhysicalNSGalerkinTrajectory) →
        Dyn.PhysicalNSMixedHelicitySpacetimeBudget T →
        ClayConclusion T

  open SuppliedClayNavierStokesAuthority public

  r293PhysicalInputsToClay :
    (ClayConclusion : Dyn.PhysicalNSGalerkinTrajectory → Set) →
    SuppliedClayNavierStokesAuthority ClayConclusion →
    (T : Dyn.PhysicalNSGalerkinTrajectory) →
    Weld.R293PhysicalPackageAInputs T →
    ClayConclusion T
  r293PhysicalInputsToClay ClayConclusion authority T inputs =
    packageAToClay authority T
      (Weld.r293BuildsPhysicalPackageA T inputs)

round356ClayAuthorityConsumesLiteralR240PackageA : Bool
round356ClayAuthorityConsumesLiteralR240PackageA = true

round356R354FeedsClayAuthorityWithoutProxy : Bool
round356R354FeedsClayAuthorityWithoutProxy = true

round356HistoricalFailClosedClayReceiptsMutated : Bool
round356HistoricalFailClosedClayReceiptsMutated = false

round356BooleanPromotionUsedAsProof : Bool
round356BooleanPromotionUsedAsProof = false

round356ConditionalClayConclusionCompilerClosed : Bool
round356ConditionalClayConclusionCompilerClosed = true

round356ConditionalClayConclusionCompilerClosedIsTrue :
  round356ConditionalClayConclusionCompilerClosed ≡ true
round356ConditionalClayConclusionCompilerClosedIsTrue = refl

round356HistoricalFailClosedClayReceiptsMutatedIsFalse :
  round356HistoricalFailClosedClayReceiptsMutated ≡ false
round356HistoricalFailClosedClayReceiptsMutatedIsFalse = refl

round356BooleanPromotionUsedAsProofIsFalse :
  round356BooleanPromotionUsedAsProof ≡ false
round356BooleanPromotionUsedAsProofIsFalse = refl
