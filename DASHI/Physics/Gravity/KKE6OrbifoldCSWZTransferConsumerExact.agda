module DASHI.Physics.Gravity.KKE6OrbifoldCSWZTransferConsumerExact where

------------------------------------------------------------------------
-- 2026-10-25 highest-value CS/Green-Schwarz BIDI in the ALREADY
-- EXISTING first-Tits E6/trinification programme:
--
-- OWNED: E6 #1106 (original 27, E32/E33, six-invariant V6);
-- physical KK #1241 (27 chiral orbifold and source anomaly);
-- earlier 2+1D CS receipts do NOT furnish a 4+1D spin CS action.
--
-- Source-executed local anomaly polynomial in its DECLARED
-- unnormalised gauge-trace basis:
-- I6=(FL-FR) X4, with
-- X4=40 FL²+64 FL FR+40 FR²+16 p1
--    +2(c2c+c2L+c2R).
--
-- A half-anomaly on each endpoint (I6/2,I6/2) can be
-- REDISTRIBUTED by a 5D CS term with opposite endpoint descent:
-- (I6/2,I6/2)+(+I6/2,-I6/2)=(I6,0).
-- Existing Chi33 phase transforms δθ=2(λL-λR), so ONE endpoint
-- WZ source -θ X4/2 cancels the remaining INFINITESIMAL anomaly.
-- Its WZ coefficients are integral in the naive source lattice,
-- whereas original TWO symmetric endpoint WZ terms -θ X4/4
-- have an apparent half-unit for any mixed c2 source coefficient.
--
-- Stronger independent INDEX FAMILY test on SPIN CP3:
-- I(m,n)=(m-n)(40m²+64mn+40n²-16)/6.
-- It is EVEN for all integral m,n; this reduces to a nine-case
-- residue mod3: (m-n)(5m²+8mn+5n²-2) ≡ 0 (mod3).
-- Additional S2xS4 SU3c/SU2 instanton and S2xK3 families have
-- indices 4(m-n) and 32(m-n) respectively, hence even.
--
-- These are source-selected FINITE MODELS, not a global APS eta,
-- spin/(SU3^3×U1)/Γ cohomology or complete anomaly-free 5D QFT.
-- Original theory: von Gersdorff/Quiros 2003, APS index theory;
-- NOT a new discovery of orbifold GS or 6D Dirac index.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Data.Nat.Base using (_+_; _*_)
import DASHI.Core.FormalClaimTransportGeometryExact as Transport
import DASHI.Core.ConsumerDescentMinimalObserverExact as Descent
import DASHI.Physics.Gravity.KKE6OrbifoldGreenSchwarzConsumerExact as PriorGS

-- Exact numerical coefficient checks, not integral normalisations.
cubicLeftFactor : 2 * 20 ≡ 40
cubicLeftFactor = refl

cubicMixedFactor : 2 * 32 ≡ 64
cubicMixedFactor = refl

cubicRightFactor : 2 * 20 ≡ 40
cubicRightFactor = refl

gravitationalFactor : 2 * 8 ≡ 16
gravitationalFactor = refl

eachNonabelianMixedFactor : 2 * 1 ≡ 2
eachNonabelianMixedFactor = refl

-- A CS field can move consistent boundary anomaly without changing
-- the total integrated anomaly, and it requires one boundary WZ
-- to cancel the remaining local anomaly. This is an ALLOCATION
-- RECEIPT, not the quantum path integral.
data LocalAnomalyAllocation : Set where
  twoSymmetricFixedPlanes
  bulkCSTransferredToFirstPlane : LocalAnomalyAllocation

representationDimension : LocalAnomalyAllocation → Nat
representationDimension _ = 27

-- Source naive integer polynomial coefficient check:
-- Symmetric WZ at both boundaries uses theta X4/4, yielding a
-- mixed SU3/SU2 coefficient 2/4 (HALF). CS-transferred single
-- boundary WZ uses theta X4/2, giving coefficient 2/2 (ONE).
data MixedNaiveWZPeriodResult : Set where
  fractionalMixedNaiveWZ
  integralMixedNaiveWZ : MixedNaiveWZPeriodResult

selectedNaiveMixedPeriod : LocalAnomalyAllocation →
  MixedNaiveWZPeriodResult
selectedNaiveMixedPeriod twoSymmetricFixedPlanes =
  fractionalMixedNaiveWZ
selectedNaiveMixedPeriod bulkCSTransferredToFirstPlane =
  integralMixedNaiveWZ

fractionalNotIntegral : fractionalMixedNaiveWZ ≡ integralMixedNaiveWZ → ⊥
fractionalNotIntegral ()

same27MatterDoesNotDetermineBoundaryWZPeriod :
  Transport.ClaimNonTransportWitness
    representationDimension selectedNaiveMixedPeriod
same27MatterDoesNotDetermineBoundaryWZPeriod =
  Descent.consumerNonDescentWitness
    twoSymmetricFixedPlanes
    bulkCSTransferredToFirstPlane
    refl fractionalNotIntegral

-- Selected naive half-period fixes source normalisation only;
-- possible global quotient-characteristic fractional classes,
-- torsion anomalies and eta regulators are still open.
globallyIntegralSpinQuotientCSTransferCertified : Bool
globallyIntegralSpinQuotientCSTransferCertified = false

data ModThree : Set where
  resZero resOne resTwo : ModThree

_modThreeTimes_ : ModThree → ModThree → ModThree
resZero modThreeTimes_ _ = resZero
resOne modThreeTimes_ x = x
resTwo modThreeTimes_ resZero = resZero
resTwo modThreeTimes_ resOne = resTwo
resTwo modThreeTimes_ resTwo = resOne

modThreeSquare : ModThree → ModThree
modThreeSquare x = x modThreeTimes_ x

-- Actual CP3 source index parity requires d*(2*d^2+1)=0 mod3.
modThreeTwiceSquarePlusOne : ModThree → ModThree
modThreeTwiceSquarePlusOne resZero = resOne
modThreeTwiceSquarePlusOne resOne = resZero
modThreeTwiceSquarePlusOne resTwo = resZero

cpThreeSpinHalfIndexModThreeCondition :
  (d : ModThree) →
  d modThreeTimes_ (modThreeTwiceSquarePlusOne d) ≡ resZero
cpThreeSpinHalfIndexModThreeCondition resZero = refl
cpThreeSpinHalfIndexModThreeCondition resOne = refl
cpThreeSpinHalfIndexModThreeCondition resTwo = refl

cpThreeGlobalSpinIndexTestIsNotFullBordism : Bool
cpThreeGlobalSpinIndexTestIsNotFullBordism = true

priorGSFactorisationOwned :
  PriorGS.localUnitAxionShifts PriorGS.finalHypercharge ≡ false
priorGSFactorisationOwned = refl
