{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNR650HHNestedRowsRouteToLHRound778Exact where

------------------------------------------------------------------------
-- ROUND778 / HH BASE TRIAD ROUTES BOTH CYCLIC NESTED ROWS INTO LH
--
-- R763:
--
--   N(beta)+N(swap beta)
--     = PairedBase(beta) + 2 Row(pLeg beta) + 2 Row(qLeg beta).
--
-- R777 proves that an R25-HH base triad has energy-orbit profile
--
--   (HH,LH,LH).
--
-- Therefore both cyclic rows appearing in the exact HH residual normal form
-- are rows whose OUTER incidence is literally R25 low-high.
--
-- This does not estimate any row and does not identify its sign.  It only
-- removes the false picture that the HH channel is class-locally self-contained.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadOrbitConstruction as Orbit
import DASHI.Physics.Closure.NSTriadKNPhysicalScaleTrichotomy as Scale
import DASHI.Physics.Closure.NSTriadKNLuoPhysicalFiveClassSupportRound25Exact as R25
import DASHI.Physics.Closure.NSTriadKNR650EnergyOrbitBonyProfileRound775Exact as R775
import DASHI.Physics.Closure.NSTriadKNR650HHOrbitProfileRound777Exact as R777

hhPRowClassIsLowHigh :
  ∀ {beta : Physical.PhysicalTriadIncidence} →
  R25.TriadicClassCertificate beta R25.HH →
  Scale.classifyScale R25.literalShellPolicy (Orbit.pEnergyLeg beta)
  ≡ Scale.lowHigh
hhPRowClassIsLowHigh =
  R777.hhPEnergyLegIsLowHigh

hhQRowClassIsLowHigh :
  ∀ {beta : Physical.PhysicalTriadIncidence} →
  R25.TriadicClassCertificate beta R25.HH →
  Scale.classifyScale R25.literalShellPolicy (Orbit.qEnergyLeg beta)
  ≡ Scale.lowHigh
hhQRowClassIsLowHigh =
  R777.hhQEnergyLegIsLowHigh

hhProfileHasOnlyOneHHCoordinate :
  ∀ {beta : Physical.PhysicalTriadIncidence} →
  R25.TriadicClassCertificate beta R25.HH →
  R775.orbitProfile beta
  ≡ R775.orbit-profile
      Scale.highHigh
      Scale.lowHigh
      Scale.lowHigh
hhProfileHasOnlyOneHHCoordinate =
  R777.hhOrbitProfileExact

------------------------------------------------------------------------
-- Status.
------------------------------------------------------------------------

round778HHBaseCyclicPRowIsLH : Bool
round778HHBaseCyclicPRowIsLH = true

round778HHBaseCyclicQRowIsLH : Bool
round778HHBaseCyclicQRowIsLH = true

round778HHChannelIsClassLocallySelfContained : Bool
round778HHChannelIsClassLocallySelfContained = false

round778IntroducesEstimate : Bool
round778IntroducesEstimate = false

round778W2Closed : Bool
round778W2Closed = false

round778ClayPromotion : Bool
round778ClayPromotion = false

round778HHBaseCyclicPRowIsLHIsTrue :
  round778HHBaseCyclicPRowIsLH ≡ true
round778HHBaseCyclicPRowIsLHIsTrue = refl

round778HHBaseCyclicQRowIsLHIsTrue :
  round778HHBaseCyclicQRowIsLH ≡ true
round778HHBaseCyclicQRowIsLHIsTrue = refl

round778HHChannelIsClassLocallySelfContainedIsFalse :
  round778HHChannelIsClassLocallySelfContained ≡ false
round778HHChannelIsClassLocallySelfContainedIsFalse = refl

round778IntroducesEstimateIsFalse :
  round778IntroducesEstimate ≡ false
round778IntroducesEstimateIsFalse = refl

round778W2ClosedIsFalse :
  round778W2Closed ≡ false
round778W2ClosedIsFalse = refl

round778ClayPromotionIsFalse :
  round778ClayPromotion ≡ false
round778ClayPromotionIsFalse = refl
