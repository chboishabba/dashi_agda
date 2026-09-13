module DASHI.Interop.SensibLawBrightonS185HistoricalAuthorityValidation where

open import DASHI.Core.Prelude
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Law.SensibLawBrightonS185HistoricalAuthoritySourceExact as Historical
import DASHI.Cognition.PNF.SensibLawBrightonS185HistoricalAuthorityWeldExact as Weld

open Historical.HistoricalS185SourceVersionBoundary
open Weld.BrightonHistoricalAuthorityWeldBoundary

primary : publicPrimarySourceOnly Historical.canonicalHistoricalS185SourceVersionBoundary ≡ true
primary = refl
version : exactVersionIdentityPinned Historical.canonicalHistoricalS185SourceVersionBoundary ≡ true
version = refl
date : exactMatterDatePinned Historical.canonicalHistoricalS185SourceVersionBoundary ≡ true
date = refl
envelope : exactReprintEnvelopePinned Historical.canonicalHistoricalS185SourceVersionBoundary ≡ true
envelope = refl
provision : exactProvisionLocatorPinned Historical.canonicalHistoricalS185SourceVersionBoundary ≡ true
provision = refl
actDidNotCease : reprintEndMeansActCeased Historical.canonicalHistoricalS185SourceVersionBoundary ≡ false
actDidNotCease = refl
versionNotFact : historicalVersionCreatesMatterFact Historical.canonicalHistoricalS185SourceVersionBoundary ≡ false
versionNotFact = refl
versionNotBreach : historicalVersionCreatesBreach Historical.canonicalHistoricalS185SourceVersionBoundary ≡ false
versionNotBreach = refl
weldRequired : exactMeetAuthoritySourceWeldRequired Weld.canonicalBrightonHistoricalAuthorityWeldBoundary ≡ true
weldRequired = refl
historicalNotPresent : presentDayValidityRequiredForHistoricalPayment Weld.canonicalBrightonHistoricalAuthorityWeldBoundary ≡ false
historicalNotPresent = refl
