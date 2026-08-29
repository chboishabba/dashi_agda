module DASHI.Physics.Closure.NSTriadKNComparableResidualProducerBoundaryRound204Exact where

------------------------------------------------------------------------
-- ROUND204 / LOCALIZED CC RESIDUAL PRODUCER BOUNDARY
--
-- Round203 proves that every physical CC incidence carries exact shell-collar
-- localization.  This module makes the next theorem boundary explicit:
-- downstream CC covariance estimates are allowed to assume ONLY the proof-
-- bearing localization derived from the literal classifier, not an unrelated
-- stronger comparability hypothesis.
--
-- The missing analytic producer must therefore consume a physical CC
-- certificate and its derived localization, and return a cutoff-uniform
-- quartic residual payment.  No such payment is fabricated here.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNLuoPhysicalFiveClassSupportRound25Exact as Support
import DASHI.Physics.Closure.NSTriadKNComparableShellLocalizationRound203Exact as R203

record LocalizedComparableIncidence : Set where
  constructor localized-comparable-incidence
  field
    incidence : Physical.PhysicalTriadIncidence
    classCertificate : Support.TriadicClassCertificate incidence Support.CC
    shellLocalization : R203.ComparableShellLocalization incidence

open LocalizedComparableIncidence public

localizePhysicalComparable :
  (tau : Physical.PhysicalTriadIncidence) →
  Support.TriadicClassCertificate tau Support.CC →
  LocalizedComparableIncidence
localizePhysicalComparable tau certificate =
  localized-comparable-incidence
    tau
    certificate
    (R203.physicalComparableCertificateLocalizes certificate)

-- Deliberately only a theorem-boundary status.  The next owner must attach
-- actual raw-curl/block data and prove the quartic residual inequality on that
-- same localized carrier.
round204LiteralCCCertificateFeedsLocalization : Bool
round204LiteralCCCertificateFeedsLocalization = true

round204IndependentStrongerComparabilityAssumptionNeeded : Bool
round204IndependentStrongerComparabilityAssumptionNeeded = false

round204LocalizedCCQuarticResidualPaymentClosed : Bool
round204LocalizedCCQuarticResidualPaymentClosed = false

round204PackageAClosed : Bool
round204PackageAClosed = false

round204ClayPromotion : Bool
round204ClayPromotion = false

round204LiteralCCCertificateFeedsLocalizationIsTrue :
  round204LiteralCCCertificateFeedsLocalization ≡ true
round204LiteralCCCertificateFeedsLocalizationIsTrue = refl

round204IndependentStrongerComparabilityAssumptionNeededIsFalse :
  round204IndependentStrongerComparabilityAssumptionNeeded ≡ false
round204IndependentStrongerComparabilityAssumptionNeededIsFalse = refl

round204LocalizedCCQuarticResidualPaymentClosedIsFalse :
  round204LocalizedCCQuarticResidualPaymentClosed ≡ false
round204LocalizedCCQuarticResidualPaymentClosedIsFalse = refl
