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
-- exactly what is verified and keep carrier-inspection/locator gaps explicit.
-- Paying metadata gaps improves theory provenance; it does not measure the
-- source distribution of a physical apparatus and does not make an equation
-- source-entitled without an inspected carrier + exact locator.
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
  (metadataKnown "N. Li; D. G. Torr")
  (metadataKnown "Effects of a gravitomagnetic field on pure superconductors")
  (stableIdentifierKnown "10.1103/PhysRevD.43.457")
  carrierNotPinnedOrInspected
  exactLocatorUnresolved
  "historical Li/Torr coupled electromagnetic/gravitational response model context only; APS bibliographic identity verified, exact equation/model-form use still requires inspected carrier + locator"
  (LiTorr.LiTorrSourceRegistry.prd1991 LiTorr.canonicalLiTorrSourceRegistry)

prb1992Candidate : LiTorrTheorySourceCandidate
prb1992Candidate = li-torr-theory-source-candidate
  prb1992Source
  (metadataKnown "Ning Li; D. G. Torr")
  (metadataKnown "Gravitational effects on the magnetic attenuation of superconductors")
  (stableIdentifierKnown "10.1103/PhysRevB.46.5489")
  carrierNotPinnedOrInspected
  exactLocatorUnresolved
  "historical equation-shape context for the combined electromagnetic/gravitational response coordinates; APS bibliographic identity verified, exact equation/model-form use still requires inspected carrier + locator"
  (LiTorr.LiTorrSourceRegistry.prb1992 LiTorr.canonicalLiTorrSourceRegistry)

fopl1993Candidate : LiTorrTheorySourceCandidate
fopl1993Candidate = li-torr-theory-source-candidate
  fopl1993Source
  (metadataKnown "Douglas G. Torr; Ning Li")
  (metadataKnown "Gravitoelectric-electric coupling via superconductivity")
  (stableIdentifierKnown "10.1007/BF00665654")
  carrierNotPinnedOrInspected
  exactLocatorUnresolved
  "historical microscopic narrative concerning coherent lattice-ion motion, mass-current and gravitoelectric/gravitomagnetic claims; bibliographic identity recovered, original carrier inspection + exact model-form locator still required"
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

-- Bibliographic identity is now paid for all three current candidates.  The
-- surviving residuals are source-content obligations, not metadata guesses.
prd1991CurrentResiduals : List LiTorrTheoryDiligenceResidual
prd1991CurrentResiduals = missingInspectedCarrier ∷ missingExactLocator ∷ []

prb1992CurrentResiduals : List LiTorrTheoryDiligenceResidual
prb1992CurrentResiduals = missingInspectedCarrier ∷ missingExactLocator ∷ []

fopl1993CurrentResiduals : List LiTorrTheoryDiligenceResidual
fopl1993CurrentResiduals = missingInspectedCarrier ∷ missingExactLocator ∷ []

record TheoryDiligenceVsApparatusBoundary : Set where
  constructor theory-diligence-vs-apparatus-boundary
  field
    doiIdentityMayPayTheorySourceIdentity : Bool
    verifiedTitleMayPayBibliographicTitleIdentity : Bool
    sourceRegistryStringIsFullyInspectedAttributedSource : Bool
    bibliographicIdentityPaysExactEquationLocator : Bool
    theoryPaperAttributionPaysActualApparatusSourceDistribution : Bool
    exactTheoryLocatorStillRequiredForSourceEntitledEquationClaim : Bool
    apparatusMeasurementStillRequiredAfterTheoryDiligence : Bool

canonicalTheoryDiligenceVsApparatusBoundary : TheoryDiligenceVsApparatusBoundary
canonicalTheoryDiligenceVsApparatusBoundary =
  theory-diligence-vs-apparatus-boundary true true false false false true true
