{-# OPTIONS --safe #-}
module DASHI.Physics.Propulsion.Rocketdyne1974LatestSourceComparisonNote where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- CONTEMPORARY SOTA COMPARATOR, NOT HISTORICAL SAME-OBJECT EVIDENCE
--
-- NASA/TM-20260007877 (Brizes et al., 2026) reports rapid stress-rupture
-- testing at 1093 C and 20.7 MPa for a new low-density niobium ODS alloy.
-- The uncoated alloy survived 21.4 h, described as about tenfold longer than
-- legacy C-103, while an R512E silicide coating extended the new alloy to
-- 84.8 h.  This independently reinforces oxidation/coating as a live
-- survivability coordinate in niobium systems, but it is NOT the 1974 WC103
-- + VH-101 nozzle article and is at a lower temperature than the ~2300 F run.
------------------------------------------------------------------------

record ContemporaryNiobiumComparator : Set where
  constructor contemporary-niobium-comparator
  field
    publicationYear : Nat
    temperatureC : Nat
    stressTenthsMPa : Nat
    uncoatedLDNbODSTenthsHours : Nat
    coatedLDNbODSTenthsHours : Nat
    comparatorStatement : String
    exactHistoricalMaterial : Bool
    exactHistoricalCoating : Bool
    sameTemperatureAsRocketdyne2300F : Bool
    admissibleUse : String
    sourceReference : String

nasa2026NiobiumComparator : ContemporaryNiobiumComparator
nasa2026NiobiumComparator =
  contemporary-niobium-comparator
    2026 1093 207 214 848
    "uncoated LDNb-ODS reported about tenfold longer rupture life than legacy C-103; R512E coating further increased life"
    false false false
    "supports oxidation/coating as a survivability coordinate; cannot calibrate the 1974 WC103/VH-101 stress-life law"
    "NASA/TM-20260007877, A Dispersion-Strengthened Low-Density Niobium Alloy and Its Elevated Temperature Mechanical Performance"

record ContemporaryComparatorBoundary : Set where
  constructor contemporary-comparator-boundary
  field
    oxidationAndCoatingRemainRelevantCoordinates : Bool
    modernComparatorPays1974ConstitutiveLaw : Bool
    modernComparatorPays1974CoatingLaw : Bool
    modernComparatorMayGuideAcquisition : Bool

canonicalContemporaryComparatorBoundary : ContemporaryComparatorBoundary
canonicalContemporaryComparatorBoundary =
  contemporary-comparator-boundary true false false true

contemporaryComparatorDoesNotPayHistoricalLaw : Bool
contemporaryComparatorDoesNotPayHistoricalLaw = true
