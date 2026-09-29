{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNR650FullySeparatedPOrbitInvariantRound790Exact where

------------------------------------------------------------------------
-- ROUND790 / FULLY-SEPARATED SUPPORT IS ALSO p-ENERGY INVARIANT
--
-- On the three R782 profiles the p-energy action is:
--
--   (LH,HH,HL) --pE--> (HH,LH,LH)
--   (HH,LH,LH) --pE--> (LH,HH,HL)
--   (HL,HL,HH) --pE--> (HL,HL,HH).
--
-- Thus pEnergyLeg preserves the fully-separated support.  Since pEnergyLeg is
-- genuinely involutive, the Boolean ccTouched mask is exactly p-invariant.
--
-- Together with R787 this supplies the two mask-equivariances required to
-- localize the old R772 p/q product-rule reindexing to the separated family.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadOrbitConstruction as Orbit
import DASHI.Physics.Closure.NSTriadKNPhysicalScaleTrichotomy as Scale
import DASHI.Physics.Closure.NSTriadKNLuoPhysicalFiveClassSupportRound25Exact as R25
import DASHI.Physics.Closure.NSTriadKNPhysicalGalerkinIncidencePermutationRound38Exact as R38
import DASHI.Physics.Closure.NSTriadKNR650EnergyOrbitBonyProfileRound775Exact as R775
import DASHI.Physics.Closure.NSTriadKNR650HHOrbitProfileRound777Exact as R777
import DASHI.Physics.Closure.NSTriadKNR650LHOrbitProfileSplitRound779Exact as R779
import DASHI.Physics.Closure.NSTriadKNR650HLOrbitProfileSplitRound780Exact as R780
import DASHI.Physics.Closure.NSTriadKNR650OrbitProfileTwoFamilyResidualRound781Exact as R781
import DASHI.Physics.Closure.NSTriadKNR650FullySeparatedOrbitProfileSupportRound782Exact as R782
import DASHI.Physics.Closure.NSTriadKNR650FullySeparatedQOrbitCycleRound786Exact as R786

trueNotFalse : true ≡ false → ⊥
trueNotFalse ()

pBaseFromProfile :
  (beta : Physical.PhysicalTriadIncidence) →
  Scale.classifyScale R25.literalShellPolicy (Orbit.pEnergyLeg beta)
  ≡ R775.pClass (R775.orbitProfile beta)
pBaseFromProfile beta = refl

pPClassFromBase :
  (beta : Physical.PhysicalTriadIncidence) →
  Scale.classifyScale R25.literalShellPolicy
    (Orbit.pEnergyLeg (Orbit.pEnergyLeg beta))
  ≡
  Scale.classifyScale R25.literalShellPolicy beta
pPClassFromBase beta
  rewrite R38.pEnergyLegInvolutiveExact beta =
  refl

lhShapePStep :
  ∀ {beta} →
  R775.orbitProfile beta
    ≡ R775.orbit-profile
        Scale.lowHigh Scale.highHigh Scale.highLow →
  R775.orbitProfile (Orbit.pEnergyLeg beta)
    ≡ R775.orbit-profile
        Scale.highHigh Scale.lowHigh Scale.lowHigh
lhShapePStep {beta} shape =
  R777.hhOrbitProfileExact certificate
  where
  pBaseHH :
    Scale.classifyScale R25.literalShellPolicy (Orbit.pEnergyLeg beta)
    ≡ Scale.highHigh
  pBaseHH =
    trans
      (pBaseFromProfile beta)
      (cong R775.pClass shape)

  certificate :
    R25.TriadicClassCertificate (Orbit.pEnergyLeg beta) R25.HH
  certificate = R786.regimeCertificate pBaseHH

hlShapePStep :
  ∀ {beta} →
  R775.orbitProfile beta
    ≡ R775.orbit-profile
        Scale.highLow Scale.highLow Scale.highHigh →
  R775.orbitProfile (Orbit.pEnergyLeg beta)
    ≡ R775.orbit-profile
        Scale.highLow Scale.highLow Scale.highHigh
hlShapePStep {beta} shape =
  decide (R780.hlInterior (Orbit.pEnergyLeg beta)) refl
  where
  pBaseHL :
    Scale.classifyScale R25.literalShellPolicy (Orbit.pEnergyLeg beta)
    ≡ Scale.highLow
  pBaseHL =
    trans
      (pBaseFromProfile beta)
      (cong R775.pClass shape)

  certificate :
    R25.TriadicClassCertificate (Orbit.pEnergyLeg beta) R25.HL
  certificate = R786.regimeCertificate pBaseHL

  betaBaseHL :
    Scale.classifyScale R25.literalShellPolicy beta ≡ Scale.highLow
  betaBaseHL =
    trans
      (sym (R775.orbitProfileBase beta))
      (cong R775.baseClass shape)

  pPClassHL :
    Scale.classifyScale R25.literalShellPolicy
      (Orbit.pEnergyLeg (Orbit.pEnergyLeg beta))
    ≡ Scale.highLow
  pPClassHL =
    trans
      (pPClassFromBase beta)
      betaBaseHL

  decide :
    (value : Bool) →
    R780.hlInterior (Orbit.pEnergyLeg beta) ≡ value →
    R775.orbitProfile (Orbit.pEnergyLeg beta)
      ≡ R775.orbit-profile
          Scale.highLow Scale.highLow Scale.highHigh
  decide true interior =
    R780.hlInteriorOrbitProfile certificate interior
  decide false boundary =
    ⊥-elim
      (R786.highLowNotComparable
        (trans
          (sym pPClassHL)
          (cong R775.pClass
            (R780.hlBoundaryOrbitProfile certificate boundary))))

hhShapePStep :
  ∀ {beta} →
  R775.orbitProfile beta
    ≡ R775.orbit-profile
        Scale.highHigh Scale.lowHigh Scale.lowHigh →
  R775.orbitProfile (Orbit.pEnergyLeg beta)
    ≡ R775.orbit-profile
        Scale.lowHigh Scale.highHigh Scale.highLow
hhShapePStep {beta} shape =
  decide (R779.lhInterior (Orbit.pEnergyLeg beta)) refl
  where
  pBaseLH :
    Scale.classifyScale R25.literalShellPolicy (Orbit.pEnergyLeg beta)
    ≡ Scale.lowHigh
  pBaseLH =
    trans
      (pBaseFromProfile beta)
      (cong R775.pClass shape)

  certificate :
    R25.TriadicClassCertificate (Orbit.pEnergyLeg beta) R25.LH
  certificate = R786.regimeCertificate pBaseLH

  betaBaseHH :
    Scale.classifyScale R25.literalShellPolicy beta ≡ Scale.highHigh
  betaBaseHH =
    trans
      (sym (R775.orbitProfileBase beta))
      (cong R775.baseClass shape)

  pPClassHH :
    Scale.classifyScale R25.literalShellPolicy
      (Orbit.pEnergyLeg (Orbit.pEnergyLeg beta))
    ≡ Scale.highHigh
  pPClassHH =
    trans
      (pPClassFromBase beta)
      betaBaseHH

  decide :
    (value : Bool) →
    R779.lhInterior (Orbit.pEnergyLeg beta) ≡ value →
    R775.orbitProfile (Orbit.pEnergyLeg beta)
      ≡ R775.orbit-profile
          Scale.lowHigh Scale.highHigh Scale.highLow
  decide true interior =
    R779.lhInteriorOrbitProfile certificate interior
  decide false boundary =
    ⊥-elim
      (R786.highHighNotComparable
        (trans
          (sym pPClassHH)
          (cong R775.pClass
            (R779.lhBoundaryOrbitProfile certificate boundary))))

fullySeparatedPStep :
  (beta : Physical.PhysicalTriadIncidence) →
  R781.ccTouched beta ≡ false →
  R781.ccTouched (Orbit.pEnergyLeg beta) ≡ false
fullySeparatedPStep beta separated
  with R782.fullySeparatedOrbitShape beta separated
... | R782.lhInteriorShape shape
  rewrite lhShapePStep shape =
  refl
... | R782.hlInteriorShape shape
  rewrite hlShapePStep shape =
  refl
... | R782.hhShape shape
  rewrite hhShapePStep shape =
  refl

ccTouchedPInvariant :
  (beta : Physical.PhysicalTriadIncidence) →
  R781.ccTouched (Orbit.pEnergyLeg beta)
  ≡ R781.ccTouched beta
ccTouchedPInvariant beta
  with R781.ccTouched beta in base
... | false =
  trans
    (fullySeparatedPStep beta base)
    (sym base)
... | true
  with R781.ccTouched (Orbit.pEnergyLeg beta) in next
... | true = refl
... | false =
  ⊥-elim
    (trueNotFalse
      (trans
        (sym base)
        (trans
          (sym
            (cong R781.ccTouched
              (R38.pEnergyLegInvolutiveExact beta)))
          (fullySeparatedPStep (Orbit.pEnergyLeg beta) next))))

round790FullySeparatedProfilesClosedUnderP : Bool
round790FullySeparatedProfilesClosedUnderP = true

round790CCTouchedPEnergyInvariant : Bool
round790CCTouchedPEnergyInvariant = true

round790PActionSwapsLHAndHHAndFixesHL : Bool
round790PActionSwapsLHAndHHAndFixesHL = true

round790IntroducesEstimate : Bool
round790IntroducesEstimate = false

round790W2Closed : Bool
round790W2Closed = false

round790ClayPromotion : Bool
round790ClayPromotion = false

round790FullySeparatedProfilesClosedUnderPIsTrue :
  round790FullySeparatedProfilesClosedUnderP ≡ true
round790FullySeparatedProfilesClosedUnderPIsTrue = refl

round790CCTouchedPEnergyInvariantIsTrue :
  round790CCTouchedPEnergyInvariant ≡ true
round790CCTouchedPEnergyInvariantIsTrue = refl

round790PActionSwapsLHAndHHAndFixesHLIsTrue :
  round790PActionSwapsLHAndHHAndFixesHL ≡ true
round790PActionSwapsLHAndHHAndFixesHLIsTrue = refl

round790IntroducesEstimateIsFalse :
  round790IntroducesEstimate ≡ false
round790IntroducesEstimateIsFalse = refl

round790W2ClosedIsFalse :
  round790W2Closed ≡ false
round790W2ClosedIsFalse = refl

round790ClayPromotionIsFalse :
  round790ClayPromotion ≡ false
round790ClayPromotionIsFalse = refl
