module DASHI.Physics.ExoticGravity.AntigravityMicroscopicBulkProofSearchBridgeExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.Physics.ExoticGravity.LiTorrMicroscopicToBulkGravitomagneticSumBidiExact as Micro
import DASHI.Physics.ExoticGravity.AntigravityOptimizedAcquisitionPlanExact as Plan
import DASHI.Law.SensibLawProofDirectedSearchIntentExact as Search

currentMicroscopicFirstOpenIsSourceDistribution :
  Micro.currentFirstOpenMicroscopicBulkLeaf ≡ Micro.sourceDistributionLeaf
currentMicroscopicFirstOpenIsSourceDistribution = refl

record MicroscopicPriorReceipt : Set where
  constructor microscopic-prior-receipt
  field
    singleIonEstimate : Micro.SingleIonEstimate
    bulkEstimate : Micro.BulkEstimate
    literatureFormulaScope : String
    literatureIonCountScope : String

open MicroscopicPriorReceipt public

canonicalMicroscopicPrior : MicroscopicPriorReceipt
canonicalMicroscopicPrior = microscopic-prior-receipt
  Micro.canonicalSingleIonEstimate
  Micro.canonicalBulkEstimate
  "Torr/Li single-ion weak-field estimate retained as a literature-side model input"
  "Torr/Li coherent-ion count retained as a literature-side model input; not an empirical count of a newly selected apparatus"

data MicroscopicBundleResidual : Set where
  missingActualSourceDistribution : MicroscopicBundleResidual
  missingAngularMomentumAlignment : MicroscopicBundleResidual
  missingObservationGeometry : MicroscopicBundleResidual
  missingVectorSourceSum : MicroscopicBundleResidual
  missingSameApparatusGRComparison : MicroscopicBundleResidual

producerForMicroscopicBundleResidual :
  MicroscopicBundleResidual → Search.ProducerClass
producerForMicroscopicBundleResidual missingActualSourceDistribution =
  Search.empiricalEvidenceProducer
producerForMicroscopicBundleResidual missingAngularMomentumAlignment =
  Search.empiricalEvidenceProducer
producerForMicroscopicBundleResidual missingObservationGeometry =
  Search.empiricalEvidenceProducer
producerForMicroscopicBundleResidual missingVectorSourceSum =
  Search.discriminatorProducer
producerForMicroscopicBundleResidual missingSameApparatusGRComparison =
  Search.propositionSourceProducer

data MicroscopicPriorToSourceBundleAuthority : Set where

microscopicPriorCannotManufactureSourceBundle :
  MicroscopicPriorToSourceBundleAuthority → Plan.FullSourceGeometryBundleReceipt
microscopicPriorCannotManufactureSourceBundle ()

record MicroscopicBulkProofSearchBoundary : Set where
  constructor microscopic-bulk-proof-search-boundary
  field
    singleIonFormulaAlreadyOwned : Bool
    illustrativeIonCountAlreadyOwned : Bool
    thoseTwoInputsCloseBulkField : Bool
    actualSourceDistributionStillRequired : Bool
    observationGeometryStillRequired : Bool
    vectorSumStillRequired : Bool
    sameApparatusGRComparisonStillRequired : Bool
    literaturePriorAutomaticallyPaysSourceBundle : Bool

canonicalMicroscopicBulkProofSearchBoundary : MicroscopicBulkProofSearchBoundary
canonicalMicroscopicBulkProofSearchBoundary =
  microscopic-bulk-proof-search-boundary
    true true false true true true true false
