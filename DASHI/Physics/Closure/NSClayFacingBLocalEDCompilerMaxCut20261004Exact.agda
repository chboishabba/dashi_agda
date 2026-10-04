module DASHI.Physics.Closure.NSClayFacingBLocalEDCompilerMaxCut20261004Exact where

------------------------------------------------------------------------
-- POSITIVE B / LOCAL-ED ALLOCATION IS NOT AN INDEPENDENT ANALYTIC LEAF
--
-- Once B1, B2, B3 and the B4 ED remainder are all paid in the SAME literal
-- output-local ED currency,
--
--   B1(k) <= c1 * ED_k
--   B2(k) <= c2 * ED_k
--   B3(k) <= c3 * ED_k
--   Crit(k) <= theta * Mcore(k) + c4 * ED_k,
--
-- the uniform-family allocation is automatic with
--
--   C = c1 + c2 + c3 + c4.
--
-- No positivity of ED_k is needed for this aggregation: after summing the
-- already-proved inequalities, the right-hand side is definitionally/ring-
-- algebraically C * ED_k.  Nonnegativity of the four coefficients is used only
-- to provide the existing uniform-family `coefficientNN` field.
--
-- Therefore B_localED is compiler plumbing, not a fifth PDE estimate.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _+_; _*_; _≤_; _<_)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst; sym)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNLiteralViscousQuadraticCoefficientRound30Exact as Field30
import DASHI.Physics.Closure.NSTriadKNFixedOutputPhysicalCriticalRegionPaymentLiveExact as Pay
import DASHI.Physics.Closure.NSClayFacingBAnalyticMaxCut20261004Exact as Cut

F : C3.RealField _
F = Rational.rationalRealField

module Compile
    (physicalSystem : Field30.PhysicalFiniteComplex3GalerkinSystem F)
    (S : Helical.HelicalModeScalars F)
    (theta c1 c2 c3 c4 : ℚ)
    (select : Z3.FourierMode → Z3.FourierMode → Bool) where

  coefficient : ℚ
  coefficient = ((c1 + c2) + c3) + c4

  module D = Cut.DirectUniformAnalytic
    physicalSystem S theta coefficient select

  localED : Z3.FourierMode → ℚ
  localED = D.U.localED

  record CommonLocalEDAnalyticLeaves : Set₁ where
    constructor common-local-ed-analytic-leaves
    field
      coreCompanionMass : Z3.FourierMode → ℚ

      thetaNN : 0ℚ ≤ theta
      thetaStrictlyBelowOne : theta < 1ℚ
      c1NN : 0ℚ ≤ c1
      c2NN : 0ℚ ≤ c2
      c3NN : 0ℚ ≤ c3
      c4NN : 0ℚ ≤ c4
      viscosityNN : 0ℚ ≤ Field30.viscosity physicalSystem

      b1PaidBySameLocalED :
        (output : Z3.FourierMode) →
        let module P = Pay.LiveRegionPayment physicalSystem S output
        in P.deepFarLowFarLowSigned ≤ c1 * localED output

      b2PaidBySameLocalED :
        (output : Z3.FourierMode) →
        let module P = Pay.LiveRegionPayment physicalSystem S output
        in P.deepFarLowDeepHighHighSigned ≤ c2 * localED output

      b3PaidBySameLocalED :
        (output : Z3.FourierMode) →
        let module P = Pay.LiveRegionPayment physicalSystem S output
        in P.deepHighHighHighHighSigned ≤ c3 * localED output

      b4PaidBySameLocalED :
        (output : Z3.FourierMode) →
        let module P = Pay.LiveRegionPayment physicalSystem S output
        in P.criticalTouchingSigned
          ≤ theta * coreCompanionMass output + c4 * localED output

  open CommonLocalEDAnalyticLeaves public

  coefficientNonnegative :
    (L : CommonLocalEDAnalyticLeaves) → 0ℚ ≤ coefficient
  coefficientNonnegative L =
    ℚP.+-mono-≤
      (ℚP.+-mono-≤
        (ℚP.+-mono-≤ (c1NN L) (c2NN L))
        (c3NN L))
      (c4NN L)

  aggregateLocalEDExact :
    (output : Z3.FourierMode) →
    (((c1 * localED output + c2 * localED output)
        + c3 * localED output)
      + c4 * localED output)
    ≡ coefficient * localED output
  aggregateLocalEDExact output =
    solve
      (c1 ∷ c2 ∷ c3 ∷ c4 ∷ localED output ∷ [])

  toDirectUniformAnalyticLeaves :
    CommonLocalEDAnalyticLeaves → D.DirectUniformAnalyticLeaves
  toDirectUniformAnalyticLeaves L = record
    { D.b1Budget = λ output → c1 * localED output
    ; D.b2Budget = λ output → c2 * localED output
    ; D.b3Budget = λ output → c3 * localED output
    ; D.coreCompanionMass = coreCompanionMass L
    ; D.coreEDBudget = λ output → c4 * localED output
    ; D.thetaNN = thetaNN L
    ; D.thetaStrictlyBelowOne = thetaStrictlyBelowOne L
    ; D.coefficientNN = coefficientNonnegative L
    ; D.viscosityNN = viscosityNN L
    ; D.b1LiteralPayment = b1PaidBySameLocalED L
    ; D.b2LiteralPayment = b2PaidBySameLocalED L
    ; D.b3LiteralPayment = b3PaidBySameLocalED L
    ; D.b4LiteralStrictPayment = b4PaidBySameLocalED L
    ; D.aggregateLocalEDAllocation = λ output →
        subst
          (((c1 * localED output + c2 * localED output)
              + c3 * localED output)
            + c4 * localED output ≤_)
          (aggregateLocalEDExact output)
          ℚP.≤-refl
    }

  commonLocalEDLeavesBuildPhysicalFamily :
    CommonLocalEDAnalyticLeaves → D.U.U.UniformPhysicalCriticalRegionFamily
  commonLocalEDLeavesBuildPhysicalFamily L =
    D.directUniformLeavesBuildPhysicalFamily
      (toDirectUniformAnalyticLeaves L)

------------------------------------------------------------------------
-- Status.
------------------------------------------------------------------------

bLocalEDAllocationCompilerClosed : Bool
bLocalEDAllocationCompilerClosed = true

bLocalEDIndependentAnalyticLeaf : Bool
bLocalEDIndependentAnalyticLeaf = false

bLocalEDCompilerIntroducesEstimate : Bool
bLocalEDCompilerIntroducesEstimate = false

clayPromotion : Bool
clayPromotion = false

bLocalEDAllocationCompilerClosedIsTrue :
  bLocalEDAllocationCompilerClosed ≡ true
bLocalEDAllocationCompilerClosedIsTrue = refl

bLocalEDIndependentAnalyticLeafIsFalse :
  bLocalEDIndependentAnalyticLeaf ≡ false
bLocalEDIndependentAnalyticLeafIsFalse = refl

bLocalEDCompilerIntroducesEstimateIsFalse :
  bLocalEDCompilerIntroducesEstimate ≡ false
bLocalEDCompilerIntroducesEstimateIsFalse = refl
