module DASHI.Physics.ExoticGravity.AntigravitySourceBundleDerivationLineageExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.Physics.ExoticGravity.AntigravitySourceAcquisitionCompilationExact as Acquisition
import DASHI.Physics.ExoticGravity.AntigravityOptimizedAcquisitionPlanExact as Plan
import DASHI.Law.SensibLawProofDirectedSearchIntentExact as Search

------------------------------------------------------------------------
-- EXACT DATA -> BUNDLE DERIVATION LINEAGE
--
-- A matching apparatus label is weaker than proof that the state witnesses in
-- a FullSourceGeometryBundleReceipt were actually derived from the measurement
-- package.  This owner indexes the derivation by both exact input provenance and
-- exact output bundle.
------------------------------------------------------------------------

record SourceBundleDerivationReceipt
    (receipt : Acquisition.SourceAcquisitionReceipt) : Set where
  constructor source-bundle-derivation-receipt
  field
    inputProvenance : Acquisition.SourceMeasurementProvenance
    inputProvenanceMatches :
      inputProvenance ≡ Acquisition.provenance receipt

    inputRawDataHash : String
    inputRawDataHashMatches :
      inputRawDataHash ≡ Acquisition.rawDataHash inputProvenance

    inputDataRevision : String
    inputDataRevisionMatches :
      inputDataRevision ≡ Acquisition.dataRevision inputProvenance

    derivationImplementationCarrier : String
    derivationImplementationRevision : String
    derivationConfigurationCarrier : String
    derivationReceiptCarrier : String

    outputBundle : Plan.FullSourceGeometryBundleReceipt
    outputBundleMatches :
      outputBundle ≡ Acquisition.compiledBundle receipt

open SourceBundleDerivationReceipt public

record DerivedSourceAcquisitionReceipt : Set where
  constructor derived-source-acquisition-receipt
  field
    acquisition : Acquisition.SourceAcquisitionReceipt
    derivation : SourceBundleDerivationReceipt acquisition

open DerivedSourceAcquisitionReceipt public

compiledDerivedBundle :
  DerivedSourceAcquisitionReceipt → Plan.FullSourceGeometryBundleReceipt
compiledDerivedBundle receipt = Acquisition.compiledBundle (acquisition receipt)

------------------------------------------------------------------------
-- Reverse residuals.
------------------------------------------------------------------------

data DerivationLineageResidual : Set where
  missingDerivationImplementation : DerivationLineageResidual
  missingDerivationRevision : DerivationLineageResidual
  missingDerivationConfiguration : DerivationLineageResidual
  missingInputHashBinding : DerivationLineageResidual
  missingInputRevisionBinding : DerivationLineageResidual
  missingOutputBundleBinding : DerivationLineageResidual
  missingDerivationReceiptCarrier : DerivationLineageResidual

producerForDerivationResidual :
  DerivationLineageResidual → Search.ProducerClass
producerForDerivationResidual missingDerivationImplementation = Search.identityProducer
producerForDerivationResidual missingDerivationRevision = Search.temporalProducer
producerForDerivationResidual missingDerivationConfiguration = Search.identityProducer
producerForDerivationResidual missingInputHashBinding = Search.identityProducer
producerForDerivationResidual missingInputRevisionBinding = Search.identityProducer
producerForDerivationResidual missingOutputBundleBinding = Search.identityProducer
producerForDerivationResidual missingDerivationReceiptCarrier = Search.attributionProducer

------------------------------------------------------------------------
-- No current empirical/derivation inhabitant is manufactured.
------------------------------------------------------------------------

data CurrentDerivedSourceReceiptAuthority : Set where

noCurrentCanonicalDerivedSourceReceipt :
  CurrentDerivedSourceReceiptAuthority → DerivedSourceAcquisitionReceipt
noCurrentCanonicalDerivedSourceReceipt ()

record SourceBundleDerivationBoundary : Set where
  constructor source-bundle-derivation-boundary
  field
    sameApparatusLabelProvesDataToBundleDerivation : Bool
    exactInputHashMustBeBound : Bool
    exactInputRevisionMustBeBound : Bool
    exactOutputBundleMustBeBound : Bool
    derivationImplementationAndRevisionRequired : Bool
    derivationReceiptAutomaticallyValidatesPhysicalMechanism : Bool

canonicalSourceBundleDerivationBoundary : SourceBundleDerivationBoundary
canonicalSourceBundleDerivationBoundary =
  source-bundle-derivation-boundary false true true true true false
