module DASHI.Physics.Optics.BerkeleyConvRMLParallelComparatorExact where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Physics.Optics.MatchedPhotonImagerComparatorExact as Comparator
import DASHI.Physics.Optics.BerkeleyLenslessInformationDesignSourceExact as InfoSource

------------------------------------------------------------------------
-- CURRENT BERKELEY PARALLEL-COMPARATOR SOURCE RECEIPT
--
-- Kabuli, Hung, Ponomarenko, Markley & Waller,
-- "ConvRML: high-quality lensless imaging with random multi-focal lenslets",
-- Optics Express 34(18), 33992--34005 (2026), DOI 10.1364/OE.608614.
--
-- The paper/project surface reports a standardized parallel acquisition setup
-- that simultaneously images the same scene with random multi-focal lenslet
-- (RML), diffuser and conventional-lens systems, with 100,000 measurements per
-- system. The public ConvRML repository exposes the RML/diffuser training paths
-- and lensed ground-truth coordinates.
--
-- This pays same-scene comparator geometry. It does NOT establish equal photon
-- count/exposure/throughput across all arms, and it has no Fresnel-zone-plate
-- arm. Those remain independent obligations of the stronger DASHI comparator.
------------------------------------------------------------------------

convRMLDOI : String
convRMLDOI = "10.1364/OE.608614"

convRMLArXiv : String
convRMLArXiv = "2602.04834"

convRMLRepository : String
convRMLRepository = "lakabuli/ConvRML"

convRMLCommit : String
convRMLCommit = "0a895cb372a3c7090904027ed7c82fc0a74133c5"

measurementsPerSystem : Nat
measurementsPerSystem = 100000

parallelLensDiffuserRMLAcquisitionPaid : Bool
parallelLensDiffuserRMLAcquisitionPaid = true

sameSceneParallelAcquisitionPaid : Bool
sameSceneParallelAcquisitionPaid = true

hundredThousandMeasurementsPerSystem : Bool
hundredThousandMeasurementsPerSystem = true

publicRMLAndDiffuserDatasetPathsPaid : Bool
publicRMLAndDiffuserDatasetPathsPaid = true

lensedGroundTruthCoordinatePaid : Bool
lensedGroundTruthCoordinatePaid = true

matchedPhotonAcrossSystemsPaid : Bool
matchedPhotonAcrossSystemsPaid = false

fresnelZonePlateArmPaid : Bool
fresnelZonePlateArmPaid = false

record BerkeleyConvRMLParallelComparatorReceipt : Set where
  field
    doi : String
    arxiv : String
    repository : String
    commit : String
    measurementsEach : Nat
    parallelThreeSystemAcquisition : Bool
    sameSceneAcquisition : Bool
    sourceReportsHundredThousandEach : Bool
    publicRMLDiffuserPaths : Bool
    lensedGroundTruthCoordinate : Bool
    matchedPhotonAcrossSystems : Bool
    fresnelZonePlateArm : Bool

open BerkeleyConvRMLParallelComparatorReceipt public

berkeleyConvRMLParallelComparatorReceipt : BerkeleyConvRMLParallelComparatorReceipt
berkeleyConvRMLParallelComparatorReceipt = record
  { doi = convRMLDOI
  ; arxiv = convRMLArXiv
  ; repository = convRMLRepository
  ; commit = convRMLCommit
  ; measurementsEach = measurementsPerSystem
  ; parallelThreeSystemAcquisition = parallelLensDiffuserRMLAcquisitionPaid
  ; sameSceneAcquisition = sameSceneParallelAcquisitionPaid
  ; sourceReportsHundredThousandEach = hundredThousandMeasurementsPerSystem
  ; publicRMLDiffuserPaths = publicRMLAndDiffuserDatasetPathsPaid
  ; lensedGroundTruthCoordinate = lensedGroundTruthCoordinatePaid
  ; matchedPhotonAcrossSystems = matchedPhotonAcrossSystemsPaid
  ; fresnelZonePlateArm = fresnelZonePlateArmPaid
  }

-- Comparator is imported only to identify the stronger target contract.
-- Parallel acquisition cannot manufacture photon matching or an absent FZP arm.
