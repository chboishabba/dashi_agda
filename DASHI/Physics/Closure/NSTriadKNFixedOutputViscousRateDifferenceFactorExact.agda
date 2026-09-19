module DASHI.Physics.Closure.NSTriadKNFixedOutputViscousRateDifferenceFactorExact where

------------------------------------------------------------------------
-- FIXED-OUTPUT VISCOUS RATE DEFECT FACTORS THROUGH INPUT DISPLACEMENT
--
-- The R229 coherent-covariance obstruction is driven by differences of the
-- literal cell rates
--
--   rho(p)+rho(q),   p+q=k.
--
-- Before any estimate, the integer Fourier geometry gives the exact
-- same-output identity
--
--   (|p|^2+|k-p|^2) - (|p'|^2+|k-p'|^2)
--     = 2 (p-p') . (p+p'-k).
--
-- Thus the signed rate difference is not an opaque scalar: it carries one
-- literal displacement between the two input partners.  This is the natural
-- representation seam for the existing centered/Taylor/R571 machinery.
--
-- No absolute value, positivity, shell count, covariance sign, spacetime
-- estimate, or Clay promotion is introduced here.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Integer using (ℤ; +_; _+_; _-_; _*_; -_)
import Data.Integer.Tactic.RingSolver as IntRS
import Tactic.RingSolver.NonReflective as NR
open import Relation.Binary.PropositionalEquality using (subst)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNIntegerFourierModeAddExact as Add
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadPluckerInvariantRound27Exact as Plane
import DASHI.Physics.Closure.NSTriadKNExternalHHEuclideanSquareGapFactorRound125Exact as R125

module RingZ = NR IntRS.ring

two : ℤ
two = + 2

differenceMode : Z3.FourierMode → Z3.FourierMode → Z3.FourierMode
differenceMode = R125.subtractMode

partnerFromSum :
  (p q : Z3.FourierMode) →
  q ≡ differenceMode (Z3.addMode p q) p
partnerFromSum
    (Z3.mode px py pz)
    (Z3.mode qx qy qz) =
  Add.modeExt
    (RingZ.solve 2
      (λ p q → (q , (p + q) + (- p)))
      refl px qx)
    (RingZ.solve 2
      (λ p q → (q , (p + q) + (- p)))
      refl py qy)
    (RingZ.solve 2
      (λ p q → (q , (p + q) + (- p)))
      refl pz qz)

partnerFromResonance :
  (tau : Physical.PhysicalTriadIncidence) →
  Physical.q tau
  ≡ differenceMode (Physical.k tau) (Physical.p tau)
partnerFromResonance tau =
  subst
    (λ output →
      Physical.q tau
      ≡ differenceMode output (Physical.p tau))
    (Physical.resonance tau)
    (partnerFromSum (Physical.p tau) (Physical.q tau))

sameOutputRateKernel :
  Z3.FourierMode → Z3.FourierMode → ℤ
sameOutputRateKernel p output =
  Plane.modeNormSquared p
    + Plane.modeNormSquared (differenceMode output p)

sameOutputRateKernelDifference :
  (p p' output : Z3.FourierMode) →
  sameOutputRateKernel p output - sameOutputRateKernel p' output
  ≡
  two *
    Plane.dotMode
      (differenceMode p p')
      (differenceMode (Z3.addMode p p') output)
sameOutputRateKernelDifference
    (Z3.mode px py pz)
    (Z3.mode rx ry rz)
    (Z3.mode kx ky kz) =
  RingZ.solve 9
    (λ px py pz rx ry rz kx ky kz →
      ( ( px * px + py * py + pz * pz
          + ((kx - px) * (kx - px)
            + (ky - py) * (ky - py)
            + (kz - pz) * (kz - pz))
          - ( rx * rx + ry * ry + rz * rz
            + ((kx - rx) * (kx - rx)
              + (ky - ry) * (ky - ry)
              + (kz - rz) * (kz - rz))))
      , (+ 2) *
          ( (px - rx) * (px + rx - kx)
          + (py - ry) * (py + ry - ky)
          + (pz - rz) * (pz + rz - kz))))
    refl px py pz rx ry rz kx ky kz

physicalCellSquareRate :
  Physical.PhysicalTriadIncidence → ℤ
physicalCellSquareRate tau =
  Plane.modeNormSquared (Physical.p tau)
    + Plane.modeNormSquared (Physical.q tau)

physicalSameOutputRateDifference :
  (alpha beta : Physical.PhysicalTriadIncidence) →
  Physical.k alpha ≡ Physical.k beta →
  physicalCellSquareRate alpha - physicalCellSquareRate beta
  ≡
  two *
    Plane.dotMode
      (differenceMode (Physical.p alpha) (Physical.p beta))
      (differenceMode
        (Z3.addMode (Physical.p alpha) (Physical.p beta))
        (Physical.k beta))
physicalSameOutputRateDifference alpha beta sameOutput
  rewrite partnerFromResonance alpha
        | partnerFromResonance beta
        | sameOutput =
  sameOutputRateKernelDifference
    (Physical.p alpha)
    (Physical.p beta)
    (Physical.k beta)

------------------------------------------------------------------------
-- Trust boundary.
------------------------------------------------------------------------

fixedOutputRateDifferenceFactorizationClosed : Bool
fixedOutputRateDifferenceFactorizationClosed = true

fixedOutputRateDifferenceCarriesInputDisplacement : Bool
fixedOutputRateDifferenceCarriesInputDisplacement = true

r229CovarianceQuantitativePaymentClosed : Bool
r229CovarianceQuantitativePaymentClosed = false

r290GramDebtIdentifiedWithR229Covariance : Bool
r290GramDebtIdentifiedWithR229Covariance = false

clayPromotion : Bool
clayPromotion = false

fixedOutputRateDifferenceFactorizationClosedIsTrue :
  fixedOutputRateDifferenceFactorizationClosed ≡ true
fixedOutputRateDifferenceFactorizationClosedIsTrue = refl

fixedOutputRateDifferenceCarriesInputDisplacementIsTrue :
  fixedOutputRateDifferenceCarriesInputDisplacement ≡ true
fixedOutputRateDifferenceCarriesInputDisplacementIsTrue = refl

r229CovarianceQuantitativePaymentClosedIsFalse :
  r229CovarianceQuantitativePaymentClosed ≡ false
r229CovarianceQuantitativePaymentClosedIsFalse = refl

r290GramDebtIdentifiedWithR229CovarianceIsFalse :
  r290GramDebtIdentifiedWithR229Covariance ≡ false
r290GramDebtIdentifiedWithR229CovarianceIsFalse = refl

clayPromotionIsFalse : clayPromotion ≡ false
clayPromotionIsFalse = refl
