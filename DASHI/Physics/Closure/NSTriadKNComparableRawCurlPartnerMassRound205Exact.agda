module DASHI.Physics.Closure.NSTriadKNComparableRawCurlPartnerMassRound205Exact where

------------------------------------------------------------------------
-- ROUND205 / LOCALIZED CC INCIDENCE -> ACTUAL RAW-CURL PARTNER MASS
--
-- Round203 localizes the literal comparable/CC classifier in shell space.
-- Round204 packages that localization on the same physical incidence.
-- Round187 independently proves the universal physical swap-compressed raw-curl
-- partner estimate
--
--   ||K_pq + K_qp||^2 <= 54 |k|^2 E_p E_q.
--
-- This module welds those two existing owners on ONE physical incidence.
-- Hence the remaining CC theorem no longer has a carrier-identification gap:
-- it must aggregate the actual localized comparable partner cells produced
-- here and pay only their between-partner covariance.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (_≤_)

import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNOrderedEuclideanL2Carrier as L2
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNPartnerBlockGramLedgerRound181Exact as R181
import DASHI.Physics.Closure.NSTriadKNPhysicalRawCurlPartnerBonyRound186Exact as R186
import DASHI.Physics.Closure.NSTriadKNPhysicalRawCurlPartnerMassRound187Exact as R187
import DASHI.Physics.Closure.NSTriadKNComparableResidualProducerBoundaryRound204Exact as R204

F = R187.F

record LocalizedComparableRawCurlPartner
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (system : Audit.FiniteComplex3GalerkinSystem F E I) : Set where
  constructor localized-comparable-raw-curl-partner
  field
    localizedComparable : R204.LocalizedComparableIncidence
    rawCurlData :
      R186.PhysicalRawCurlCellData system
        (R204.incidence localizedComparable)

open LocalizedComparableRawCurlPartner public

comparablePartnerCell :
  ∀ {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    {system : Audit.FiniteComplex3GalerkinSystem F E I} →
  LocalizedComparableRawCurlPartner system → R181.CellPair
comparablePartnerCell partner =
  R186.physicalRawCurlPartnerBlock (rawCurlData partner)

localizedComparablePartnerMassBound :
  ∀ {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    {system : Audit.FiniteComplex3GalerkinSystem F E I}
    (partner : LocalizedComparableRawCurlPartner system) →
  L2.complex3NormSquared (R181.pairCell (comparablePartnerCell partner))
  ≤ R187.fiftyFour
      * C3.normSquared I (Physical.k (R204.incidence (localizedComparable partner)))
      * L2.complex3NormSquared
          (Audit.velocity system
            (Physical.p (R204.incidence (localizedComparable partner))))
      * L2.complex3NormSquared
          (Audit.velocity system
            (Physical.q (R204.incidence (localizedComparable partner))))
localizedComparablePartnerMassBound partner =
  R187.physicalRawCurlPartnerMassBound (rawCurlData partner)

round205ActualLocalizedCCRawCurlPartnerConstructed : Bool
round205ActualLocalizedCCRawCurlPartnerConstructed = true

round205LocalizedCCPartnerMassBoundClosed : Bool
round205LocalizedCCPartnerMassBoundClosed = true

round205LocalizedCCPartnerMassIntroducesShellCount : Bool
round205LocalizedCCPartnerMassIntroducesShellCount = false

round205LocalizedCCBetweenPartnerCovariancePaid : Bool
round205LocalizedCCBetweenPartnerCovariancePaid = false

round205PhysicalCCResidualBudgetClosed : Bool
round205PhysicalCCResidualBudgetClosed = false

round205PackageAClosed : Bool
round205PackageAClosed = false

round205ClayPromotion : Bool
round205ClayPromotion = false

round205ActualLocalizedCCRawCurlPartnerConstructedIsTrue :
  round205ActualLocalizedCCRawCurlPartnerConstructed ≡ true
round205ActualLocalizedCCRawCurlPartnerConstructedIsTrue = refl

round205LocalizedCCPartnerMassBoundClosedIsTrue :
  round205LocalizedCCPartnerMassBoundClosed ≡ true
round205LocalizedCCPartnerMassBoundClosedIsTrue = refl

round205LocalizedCCBetweenPartnerCovariancePaidIsFalse :
  round205LocalizedCCBetweenPartnerCovariancePaid ≡ false
round205LocalizedCCBetweenPartnerCovariancePaidIsFalse = refl
