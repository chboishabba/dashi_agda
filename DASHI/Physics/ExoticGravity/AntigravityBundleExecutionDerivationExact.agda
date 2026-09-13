module DASHI.Physics.ExoticGravity.AntigravityBundleExecutionDerivationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.Physics.ExoticGravity.AntigravityExperimentalCutProvenanceExact as Provenance
import DASHI.Law.SensibLawProofDirectedSearchIntentExact as Search

------------------------------------------------------------------------
-- GENERIC EXECUTION -> BUNDLE DERIVATION
------------------------------------------------------------------------

record BundleExecutionDerivation
    {Bundle : Set}
    (execution : Provenance.BundleExecutionProvenance)
    (bundle : Bundle) : Set where
  constructor bundle-execution-derivation
  field
    inputRawDataHash : String
    inputRawDataHashMatches :
      inputRawDataHash ≡ Provenance.rawDataHash execution

    inputDataRevision : String
    inputDataRevisionMatches :
      inputDataRevision ≡ Provenance.dataRevision execution

    derivationImplementationCarrier : String
    derivationImplementationRevision : String
    derivationConfigurationCarrier : String
    derivationReceiptCarrier : String

    outputBundle : Bundle
    outputBundleMatches : outputBundle ≡ bundle

open BundleExecutionDerivation public

data BundleExecutionDerivationResidual : Set where
  missingInputHashBinding : BundleExecutionDerivationResidual
  missingInputRevisionBinding : BundleExecutionDerivationResidual
  missingDerivationImplementation : BundleExecutionDerivationResidual
  missingDerivationRevision : BundleExecutionDerivationResidual
  missingDerivationConfiguration : BundleExecutionDerivationResidual
  missingDerivationReceipt : BundleExecutionDerivationResidual
  missingExactOutputBinding : BundleExecutionDerivationResidual

producerForBundleDerivationResidual :
  BundleExecutionDerivationResidual → Search.ProducerClass
producerForBundleDerivationResidual missingInputHashBinding = Search.identityProducer
producerForBundleDerivationResidual missingInputRevisionBinding = Search.identityProducer
producerForBundleDerivationResidual missingDerivationImplementation = Search.identityProducer
producerForBundleDerivationResidual missingDerivationRevision = Search.temporalProducer
producerForBundleDerivationResidual missingDerivationConfiguration = Search.identityProducer
producerForBundleDerivationResidual missingDerivationReceipt = Search.attributionProducer
producerForBundleDerivationResidual missingExactOutputBinding = Search.identityProducer

record BundleExecutionDerivationBoundary : Set where
  constructor bundle-execution-derivation-boundary
  field
    sameApparatusExecutionAutomaticallyDeterminesBundle : Bool
    inputHashAndRevisionMustBeBound : Bool
    derivationImplementationMustBePinned : Bool
    exactOutputBundleIdentityRequired : Bool
    derivationReceiptAutomaticallyProvesPhysicalMechanism : Bool

canonicalBundleExecutionDerivationBoundary : BundleExecutionDerivationBoundary
canonicalBundleExecutionDerivationBoundary =
  bundle-execution-derivation-boundary false true true true false
