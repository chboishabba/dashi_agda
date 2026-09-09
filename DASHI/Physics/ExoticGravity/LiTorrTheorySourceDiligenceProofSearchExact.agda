module DASHI.Physics.ExoticGravity.LiTorrTheorySourceDiligenceProofSearchExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.List using (List; []; _∷_)

import DASHI.Physics.ExoticGravity.LiTorrCoupledPotentialModelExact as LiTorr
import DASHI.Law.SensibLawProofDirectedSearchIntentExact as Search

------------------------------------------------------------------------
-- THEORY-SOURCE DILIGENCE IS NOT APPARATUS-SOURCE ACQUISITION
--
-- The Li/Torr owner already contains useful bibliographic identity.  We retain
-- exactly what is known in-repo and keep title/carrier/inspection/locator gaps
-- explicit.  Paying these gaps improves theory provenance; it does not measure
-- the source distribution of a physical apparatus.
------------------------------------------------------------------------

data LiTorrTheorySource : Set where
  prd1991Source : LiTorrTheorySource
  prb1992Source : LiTorrTheorySource
  fopl1993Source : LiTorrTheorySource

data MetadataStatus : Set where
  metadataKnown : String → MetadataStatus
  metadataUnresolved : MetadataStatus

data StableIdentifierStatus : Set where
  stableIdentifierKnown : String → StableIdentifierStatus
  stableIdentifierUnresolved : StableIdentifierStatus

data CarrierInspectionStatus : Set where
  carrierInspected : String → String → CarrierInspectionStatus
  carrierNotPinnedOrInspected : CarrierInspectionStatus

data ExactLocatorStatus : Set where
  exactLocatorKnown : String → ExactLocatorStatus
  exactLocatorUnresolved : ExactLocatorStatus

record LiTorrTheorySourceCandidate : Set where
  constructor li-torr-theory-source-candidate
  field
    source : LiTorrTheorySource
    authorOrResponsibleBody : MetadataStatus
    canonicalTitle : MetadataStatus
    stableIdentifier : StableIdentifierStatus
    carrierInspection : CarrierInspectionStatus
    exactLocator : ExactLocatorStatus
    boundedTheoryUse : String
    registryReference : String

open LiTorrTheorySourceCandidate public

prd1991Candidate : LiTorrTheorySourceCandidate
prd1991Candidate = li-torr-theory-source-candidate
  prd1991Source
  (metadataKnown "Ning Li; D. G. Torr")
  metadataUnresolved
  (stableIdentifierKnown "10.1103/PhysRevD.43.457")
  carrierNotPinnedOrInspected
  exactLocatorUnresolved
  "historical Li/Torr coupled electromagnetic/gravitational response model context only"
  (LiTorr.LiTorrSourceRegistry.prd1991 LiTorr.canonicalLiTorrSourceRegistry)

prb1992Candidate : LiTorrTheorySourceCandidate
prb1992Candidate = li-torr-theory-source-candidate
  prb1992Source
  (metadataKnown "Ning Li; D. G. Torr")
  metadataUnresolved
  (stableIdentifierKnown "10.1103/PhysRevB.46.5489")
  carrierNotPinnedOrInspected
  exactLocatorUnresolved
  "historical equation-shape context for the combined A + (m/q) A_g coordinate and separate response equations"
  (LiTorr.LiTorrSourceRegistry.prb1992 LiTorr.canonicalLiTorrSourceRegistry)

fopl1993Candidate : LiTorrTheorySourceCandidate
fopl1993Candidate = li-torr-theory-source-candidate
  fopl1993Source
  (metadataKnown "Douglas G. Torr; Ning Li")
  (metadataKnown "Gravitoelectric-electric coupling via superconductivity")
  stableIdentifierUnresolved
  carrierNotPinnedOrInspected
  exactLocatorUnresolved
  "historical microscopic narrative concerning coherent lattice-ion motion, mass-current and gravitoelectric/gravitomagnetic claims"
  (LiTorr.LiTorrSourceRegistry.fopl1993 LiTorr.canonicalLiTorrSourceRegistry)

data LiTorrTheoryDiligenceResidual : Set where
  missingCanonicalTitle : LiTorrTheoryDiligenceResidual
  missingStableIdentifier : LiTorrTheoryDiligenceResidual
  missingInspectedCarrier : LiTorrTheoryDiligenceResidual
  missingExactLocator : LiTorrTheoryDiligenceResidual

producerForTheoryDiligenceResidual :
  LiTorrTheoryDiligenceResidual → Search.ProducerClass
producerForTheoryDiligenceResidual missingCanonicalTitle = Search.attributionProducer
producerForTheoryDiligenceResidual missingStableIdentifier = Search.identityProducer
producerForTheoryDiligenceResidual missingInspectedCarrier = Search.propositionSourceProducer
producerForTheoryDiligenceResidual missingExactLocator = Search.discriminatorProducer

prd1991CurrentResiduals : List LiTorrTheoryDiligenceResidual
prd1991CurrentResiduals =
  missingCanonicalTitle ∷ missingInspectedCarrier ∷ missingExactLocator ∷ []

prb1992CurrentResiduals : List LiTorrTheoryDiligenceResidual
prb1992CurrentResiduals =
  missingCanonicalTitle ∷ missingInspectedCarrier ∷ missingExactLocator ∷ []

fopl1993CurrentResiduals : List LiTorrTheoryDiligenceResidual
fopl1993CurrentResiduals =
  missingStableIdentifier ∷ missingInspectedCarrier ∷ missingExactLocator ∷ []

record TheoryDiligenceVsApparatusBoundary : Set where
  constructor theory-diligence-vs-apparatus-boundary
  field
    doiIdentityMayPayTheorySourceIdentity : Bool
    sourceRegistryStringIsFullyInspectedAttributedSource : Bool
    theoryPaperAttributionPaysActualApparatusSourceDistribution : Bool
    exactTheoryLocatorStillRequiredForSourceEntitledEquationClaim : Bool
    apparatusMeasurementStillRequiredAfterTheoryDiligence : Bool

canonicalTheoryDiligenceVsApparatusBoundary : TheoryDiligenceVsApparatusBoundary
canonicalTheoryDiligenceVsApparatusBoundary =
  theory-diligence-vs-apparatus-boundary true false false true true
