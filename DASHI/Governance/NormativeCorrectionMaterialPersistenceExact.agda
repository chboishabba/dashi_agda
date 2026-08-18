module DASHI.Governance.NormativeCorrectionMaterialPersistenceExact where

------------------------------------------------------------------------
-- NORMATIVE / LEGAL CORRECTION != MATERIAL REPAIR
--
-- A rule, representation, funding route or legal doctrine can be corrected
-- while institutional/material state persists.  This module factors those
-- coordinates rather than treating a successful legal challenge as a complete
-- implementation theorem.
--
-- SOURCES / BOUNDED ROLES
--
-- Cooper v Stuart (1889) 14 App Cas 286 (Privy Council), no DOI asserted.
-- Bounded role: settled-colony classification / non-recognition surface.
--
-- Mabo v Queensland (No 2) [1992] HCA 23; 175 CLR 1,
-- High Court of Australia, 3 June 1992; no DOI asserted.
-- Bounded role: rejection of the enlarged terra-nullius doctrine as an
-- impediment to native-title recognition.  The judgment alone is not a receipt
-- for complete restitution, redistribution or repair of historical effects.
--
-- Williams v Commonwealth [2012] HCA 23, High Court of Australia,
-- 20 June 2012; no DOI asserted.
-- Williams v Commonwealth [2014] HCA 23, High Court of Australia,
-- 19 June 2014; no DOI asserted.
-- Bounded role: constitutional invalidity of the relevant Commonwealth funding
-- arrangements; neither holding establishes that chaplaincy disappeared as an
-- institutional practice.
--
-- Renae Barker,
-- "A Critical Analysis of Religious Aspects of the Australian Chaplaincy
-- Cases", Oxford Journal of Law and Religion 4(1):26-53 (2015),
-- DOI 10.1093/ojlr/rwv002.
-- Bounded role: legal/institutional analysis noting continued program reality
-- despite successful challenges; not an empirical coercion claim.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

record CorrectionSource : Set where
  constructor correctionSource
  field
    authorOrCourt : String
    title : String
    year : Nat
    identifierOrDOI : String
    boundedRole : String

open CorrectionSource public

data CorrectionKind : Set where
  doctrinalCorrection : CorrectionKind
  constitutionalInvalidity : CorrectionKind
  statutoryCorrection : CorrectionKind
  administrativeCorrection : CorrectionKind

data MaterialDimension : Set where
  landControl : MaterialDimension
  assetDistribution : MaterialDimension
  institutionalProgramPresence : MaterialDimension
  providerNetwork : MaterialDimension
  serviceAccess : MaterialDimension
  historicalResidue : MaterialDimension

data Status : Set where
  established : Status
  notEstablished : Status
  partialOrMixed : Status

record CorrectionPersistenceCase : Set where
  constructor correctionPersistenceCase
  field
    correctionSource : CorrectionSource
    correctionKind : CorrectionKind
    legalOrNormativeCorrection : Status
    institutionAltered : Status
    assetsOrLandRedistributed : Status
    accessChanged : Status
    historicalResidueRepaired : Status
    materialPersistenceEvidence : Status

open CorrectionPersistenceCase public

maboSource : CorrectionSource
maboSource = correctionSource
  "High Court of Australia"
  "Mabo v Queensland (No 2)"
  1992
  "[1992] HCA 23; 175 CLR 1; no DOI asserted"
  "rejects enlarged terra-nullius doctrine / permits native-title recognition; no complete-repair inference"

williams2012Source : CorrectionSource
williams2012Source = correctionSource
  "High Court of Australia"
  "Williams v Commonwealth"
  2012
  "[2012] HCA 23; no DOI asserted"
  "constitutional funding/executive-power correction; not a theorem of institutional disappearance"

williams2014Source : CorrectionSource
williams2014Source = correctionSource
  "High Court of Australia"
  "Williams v Commonwealth"
  2014
  "[2014] HCA 23; no DOI asserted"
  "second constitutional invalidity holding; program persistence remains a separate empirical question"

barker2015Source : CorrectionSource
barker2015Source = correctionSource
  "Renae Barker"
  "A Critical Analysis of Religious Aspects of the Australian Chaplaincy Cases"
  2015
  "10.1093/ojlr/rwv002"
  "analysis of Williams cases and persistence/reconfiguration of school chaplaincy; not coercion evidence"

------------------------------------------------------------------------
-- Case records deliberately leave dimensions unresolved unless the cited
-- source itself supplies them.
------------------------------------------------------------------------

maboCorrectionCase : CorrectionPersistenceCase
maboCorrectionCase = correctionPersistenceCase
  maboSource doctrinalCorrection
  established partialOrMixed notEstablished partialOrMixed
  notEstablished established

williamsCorrectionCase : CorrectionPersistenceCase
williamsCorrectionCase = correctionPersistenceCase
  barker2015Source constitutionalInvalidity
  established partialOrMixed notEstablished partialOrMixed
  notEstablished established

------------------------------------------------------------------------
-- No collapse from one corrected layer to every downstream layer.
------------------------------------------------------------------------

data LegalCorrectionPromotesCompleteMaterialRepair : Set where

data DoctrineChangePromotesAssetRedistribution : Set where

data FundingInvalidityPromotesProgramDisappearance : Set where

data PersistencePromotesLegalFailure : Set where

legalCorrectionDoesNotPromoteCompleteMaterialRepair :
  LegalCorrectionPromotesCompleteMaterialRepair → ⊥
legalCorrectionDoesNotPromoteCompleteMaterialRepair ()

doctrineChangeDoesNotPromoteAssetRedistribution :
  DoctrineChangePromotesAssetRedistribution → ⊥
doctrineChangeDoesNotPromoteAssetRedistribution ()

fundingInvalidityDoesNotPromoteProgramDisappearance :
  FundingInvalidityPromotesProgramDisappearance → ⊥
fundingInvalidityDoesNotPromoteProgramDisappearance ()

materialPersistenceDoesNotEraseLegalCorrection :
  PersistencePromotesLegalFailure → ⊥
materialPersistenceDoesNotEraseLegalCorrection ()

record NormativeCorrectionMaterialPersistenceBoundary : Set where
  constructor normativeCorrectionMaterialPersistenceBoundary
  field
    legalAndMaterialStatesSeparated : Bool
    legalCorrectionCanCoexistWithMaterialPersistence : Bool
    legalCorrectionEqualsCompleteRepair : Bool
    materialPersistenceErasesLegalVictory : Bool
    MaboJudgmentAloneEstablishesCompleteRestitution : Bool
    WilliamsInvalidityAloneEstablishesProgramDisappearance : Bool

canonicalNormativeCorrectionMaterialPersistenceBoundary :
  NormativeCorrectionMaterialPersistenceBoundary
canonicalNormativeCorrectionMaterialPersistenceBoundary =
  normativeCorrectionMaterialPersistenceBoundary true true false false false false
