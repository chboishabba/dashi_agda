module DASHI.Physics.SpaceWeather.ZhangXiaoxinForecastPublicProducerExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- PUBLIC PRODUCER RECEIPT
-- Wang & Ye public data/code deposits linked by the Space Weather paper
-- DOI 10.1029/2023SW003522.
------------------------------------------------------------------------

record ZhangPublicProducerReceipt : Set where
  constructor zhang-public-producer-receipt
  field
    paperDOI : String
    processedDataDOI : String
    codeDOI : String
    eventListManifest : String
    dataFile1 dataFile2 dataFile3 : String
    dataFile1SizeMB dataFile2SizeMB dataFile3SizeMB : String
    dataFile1MD5 dataFile2MD5 dataFile3MD5 : String
    station : String
    interval : String
    cadence : String
    thresholdRule : String
    meanLeadTimeHours : String
    exactCodeFileManifestPaid : Bool
    codeExecutedByDASHI : Bool
    matPayloadParsedByDASHI : Bool

open ZhangPublicProducerReceipt public

zhangPublicProducerReceipt : ZhangPublicProducerReceipt
zhangPublicProducerReceipt = zhang-public-producer-receipt
  "10.1029/2023SW003522"
  "10.5281/zenodo.8093239"
  "10.5281/zenodo.8093257"
  "publisher Supporting Information: Data Set S1, 2023SW003522-sup-0001-Data Set SI-S01.xlsx"
  "data_initial_v30.mat"
  "output_v30.mat"
  "predicted_table_v30.mat"
  "2.8"
  "225.6"
  "5.1"
  "36fb1d9007c2bec75480bd3d3cae10f6"
  "8d73e89ae0c60efbcacf6963942ffd10"
  "07d3f935841d088b2aa7e523609eb4aa"
  "Oulu neutron monitor, 60.05 N 25.47 E, cutoff rigidity 0.8 GV"
  "1998-2019"
  "30 min"
  "precursor threshold = 1.2 times base value"
  "50.4"
  false
  false
  false

publicDataDepositLocated : Bool
publicDataDepositLocated = true

publicCodeDepositLocated : Bool
publicCodeDepositLocated = true

publicProducerLocationPaysExecution : Bool
publicProducerLocationPaysExecution = false

publicProducerLocationPaysOperationalForecasting : Bool
publicProducerLocationPaysOperationalForecasting = false

publicProducerLocationPaysZhangSoleAuthorship : Bool
publicProducerLocationPaysZhangSoleAuthorship = false
