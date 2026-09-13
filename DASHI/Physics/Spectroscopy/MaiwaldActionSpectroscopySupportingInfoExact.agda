module DASHI.Physics.Spectroscopy.MaiwaldActionSpectroscopySupportingInfoExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

record MaiwaldSupportingInfoReceipt : Set where
  constructor maiwald-supporting-info-receipt
  field
    sourceReference : String
    freeSupportingInformationAdvertised : Bool
    figureCount : Nat
    tableCount : Nat
    photodissociationTimesPresent : Bool
    atomicCoordinatesPresent : Bool
    vibrationalFrequenciesPresent : Bool
    rawMeasuredSpectrumArrayPresent : Bool
    calibrationFilePresent : Bool

open MaiwaldSupportingInfoReceipt public

maiwaldSupportingInfoReceipt : MaiwaldSupportingInfoReceipt
maiwaldSupportingInfoReceipt = maiwald-supporting-info-receipt
  "DOI 10.1021/acs.jpca.4c03552 supporting information"
  true
  5
  4
  true
  true
  true
  false
  false

supportingInfoPaysHiddenProducerManifest : Bool
supportingInfoPaysHiddenProducerManifest = true

supportingInfoPaysRawMeasuredSpectrum : Bool
supportingInfoPaysRawMeasuredSpectrum = false

supportingInfoPaysCalibration : Bool
supportingInfoPaysCalibration = false
