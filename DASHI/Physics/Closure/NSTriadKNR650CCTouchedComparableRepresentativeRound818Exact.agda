{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNR650CCTouchedComparableRepresentativeRound818Exact where

------------------------------------------------------------------------
-- ROUND818 / ccTouched -> ONE LITERAL COMPARABLE ENERGY-LEG REPRESENTATIVE
--
-- R781's ccTouched beta means that at least one coordinate of
--
--   ( class beta
--   , class (pEnergyLeg beta)
--   , class (qEnergyLeg beta) )
--
-- is the executable R25/R775 comparable regime.
--
-- The older R203--R214 comparable machinery consumes the stronger-looking
-- type
--
--   TriadicClassCertificate tau CC.
--
-- There is no semantic gap: both classifiers are the SAME literal R25 shell
-- classifier.  This owner constructs the certificate on the correct orbit
-- representative, rather than falsely asserting that beta itself is CC.
--
-- Therefore every ccTouched beta supplies one of:
--
--   beta              with literal CC certificate/localization,
--   pEnergyLeg beta   with literal CC certificate/localization,
--   qEnergyLeg beta   with literal CC certificate/localization.
--
-- This imports R203's cutoff-independent shell collar into the live R781/R817
-- CC family.  It does NOT pay the CC residual; R214 explicitly shows that
-- constant-band localization alone is insufficient for the Gram debt.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadOrbitConstruction as Orbit
import DASHI.Physics.Closure.NSTriadKNPhysicalScaleTrichotomy as Scale
import DASHI.Physics.Closure.NSTriadKNLuoPhysicalFiveClassSupportRound25Exact as R25
import DASHI.Physics.Closure.NSTriadKNComparableShellLocalizationRound203Exact as R203
import DASHI.Physics.Closure.NSTriadKNComparableResidualProducerBoundaryRound204Exact as R204
import DASHI.Physics.Closure.NSTriadKNR650EnergyOrbitBonyProfileRound775Exact as R775
import DASHI.Physics.Closure.NSTriadKNR650OrbitProfileTwoFamilyResidualRound781Exact as R781

orBoolTrue :
  (left right : Bool) →
  R781.orBool left right ≡ true →
  (left ≡ true) ⊎ (right ≡ true)
orBoolTrue true right proof = inj₁ refl
orBoolTrue false true proof = inj₂ refl
orBoolTrue false false ()

regimeComparableTrue :
  (regime : Scale.ScaleRegime) →
  R781.regimeComparable regime ≡ true →
  regime ≡ Scale.comparable
regimeComparableTrue Scale.lowHigh ()
regimeComparableTrue Scale.highLow ()
regimeComparableTrue Scale.highHigh ()
regimeComparableTrue Scale.comparable proof = refl

literalComparableCertificate :
  (tau : Physical.PhysicalTriadIncidence) →
  Scale.classifyScale R25.literalShellPolicy tau ≡ Scale.comparable →
  R25.TriadicClassCertificate tau R25.CC
literalComparableCertificate tau classified =
  R25.triadic-class-certificate
    (trans (cong R25.classForRegime classified) refl)
    (subst
      (Scale.ScaleCondition R25.literalShellPolicy tau)
      classified
      (Scale.scaleClassificationSound R25.literalShellPolicy tau))

data CCTouchedRepresentative
    (beta : Physical.PhysicalTriadIncidence) : Set where
  baseRepresentative :
    R25.TriadicClassCertificate beta R25.CC →
    CCTouchedRepresentative beta

  pRepresentative :
    R25.TriadicClassCertificate (Orbit.pEnergyLeg beta) R25.CC →
    CCTouchedRepresentative beta

  qRepresentative :
    R25.TriadicClassCertificate (Orbit.qEnergyLeg beta) R25.CC →
    CCTouchedRepresentative beta

representativeIncidence :
  ∀ {beta} →
  CCTouchedRepresentative beta →
  Physical.PhysicalTriadIncidence
representativeIncidence {beta} (baseRepresentative certificate) = beta
representativeIncidence {beta} (pRepresentative certificate) =
  Orbit.pEnergyLeg beta
representativeIncidence {beta} (qRepresentative certificate) =
  Orbit.qEnergyLeg beta

representativeCertificate :
  ∀ {beta} (R : CCTouchedRepresentative beta) →
  R25.TriadicClassCertificate (representativeIncidence R) R25.CC
representativeCertificate (baseRepresentative certificate) = certificate
representativeCertificate (pRepresentative certificate) = certificate
representativeCertificate (qRepresentative certificate) = certificate

representativeLocalized :
  ∀ {beta} (R : CCTouchedRepresentative beta) →
  R204.LocalizedComparableIncidence
representativeLocalized R =
  R204.localizePhysicalComparable
    (representativeIncidence R)
    (representativeCertificate R)

ccTouchedSelectsComparableRepresentative :
  (beta : Physical.PhysicalTriadIncidence) →
  R781.ccTouched beta ≡ true →
  CCTouchedRepresentative beta
ccTouchedSelectsComparableRepresentative beta touched
  with orBoolTrue
    (R781.regimeComparable
      (R775.baseClass (R775.orbitProfile beta)))
    (R781.orBool
      (R781.regimeComparable
        (R775.pClass (R775.orbitProfile beta)))
      (R781.regimeComparable
        (R775.qClass (R775.orbitProfile beta))))
    touched
... | inj₁ baseTrue =
  baseRepresentative
    (literalComparableCertificate beta
      (trans
        (sym (R775.orbitProfileBase beta))
        (regimeComparableTrue
          (R775.baseClass (R775.orbitProfile beta))
          baseTrue)))
... | inj₂ tailTrue
  with orBoolTrue
    (R781.regimeComparable
      (R775.pClass (R775.orbitProfile beta)))
    (R781.regimeComparable
      (R775.qClass (R775.orbitProfile beta)))
    tailTrue
... | inj₁ pTrue =
  pRepresentative
    (literalComparableCertificate (Orbit.pEnergyLeg beta)
      (trans
        (sym (R775.orbitProfileP beta))
        (regimeComparableTrue
          (R775.pClass (R775.orbitProfile beta))
          pTrue)))
... | inj₂ qTrue =
  qRepresentative
    (literalComparableCertificate (Orbit.qEnergyLeg beta)
      (trans
        (sym (R775.orbitProfileQ beta))
        (regimeComparableTrue
          (R775.qClass (R775.orbitProfile beta))
          qTrue)))

round818CCTouchedSelectsLiteralR25CCRepresentative : Bool
round818CCTouchedSelectsLiteralR25CCRepresentative = true

round818RepresentativeFeedsR203Localization : Bool
round818RepresentativeFeedsR203Localization = true

round818OriginalIncidenceAlwaysCC : Bool
round818OriginalIncidenceAlwaysCC = false

round818ComparableCollarPaysCCTouchedResidual : Bool
round818ComparableCollarPaysCCTouchedResidual = false

round818IntroducesEstimate : Bool
round818IntroducesEstimate = false

round818ClayPromotion : Bool
round818ClayPromotion = false

round818CCTouchedSelectsLiteralR25CCRepresentativeIsTrue :
  round818CCTouchedSelectsLiteralR25CCRepresentative ≡ true
round818CCTouchedSelectsLiteralR25CCRepresentativeIsTrue = refl

round818OriginalIncidenceAlwaysCCIsFalse :
  round818OriginalIncidenceAlwaysCC ≡ false
round818OriginalIncidenceAlwaysCCIsFalse = refl

round818ComparableCollarPaysCCTouchedResidualIsFalse :
  round818ComparableCollarPaysCCTouchedResidual ≡ false
round818ComparableCollarPaysCCTouchedResidualIsFalse = refl
