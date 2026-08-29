module DASHI.Governance.IndigenousEnvironmentalAuthorityRound2CapstoneExact where

open import DASHI.Core.Prelude
import DASHI.Governance.IndigenousEnvironmentalAuthorityCapstoneExact as Base
import DASHI.Governance.NavdanyaSeedSovereigntyNonseparabilityExact as Seed
import DASHI.Governance.CaceresAuthorityWithoutEnforcementExact as Caceres
import DASHI.Governance.ThomasIntersectionalEnvironmentalismExact as Thomas
import DASHI.Governance.CaceresDefenderPatternBridgeExact as Defenders
import DASHI.Governance.EscazuProtectionEnforcementGapExact as Escazu
import DASHI.Governance.ShivaBtCottonSuicideClaimContestedExact as Shiva
import DASHI.Governance.BudjBimAquacultureAuthorityExact as BudjBim
import DASHI.Governance.MithakaArchaeologicalEvidenceExact as Mithaka
import DASHI.Governance.DarkEmuClaimStatusDecompositionExact as DarkEmu
import DASHI.Governance.KunmingMontrealTarget3AuthorityBoundaryExact as GBF

------------------------------------------------------------------------
-- ROUND-TWO CAPSTONE
--
-- Adds claim-level adjudication and independent material-practice evidence to
-- the earlier authority-envelope capstone.  The central pattern is that source
-- authority is indexed by claim and consumer rather than inherited wholesale.
------------------------------------------------------------------------

baseSeedNonseparability :
  Seed.control Seed.enclosedSeed ≡ Seed.control Seed.communitySeed → ⊥
baseSeedNonseparability = Base.sameSeedMaterialDoesNotRecoverCommunityControl

ThomasFrameworkDoesNotBecomeCausalLaw :
  Thomas.AuthorizedThomasUse Thomas.empiricalCausalLaw → ⊥
ThomasFrameworkDoesNotBecomeCausalLaw = Thomas.empiricalLawNotPromoted

CaceresStandingStillNotEnforcement :
  Caceres.EffectiveEnforcement Caceres.victimStanding → ⊥
CaceresStandingStillNotEnforcement = Defenders.caseStandingStillDoesNotConstructEnforcement

EscazuTreatyStillNotImplementation :
  Escazu.ProtectionSystemState.enforcement Escazu.formalProtectionWithContinuingRisk ≡
  Escazu.effectiveProtection → ⊥
EscazuTreatyStillNotImplementation = Escazu.treatyInstrumentDoesNotDefinitionallyEqualEffectiveProtection

ShivaStructuralClaimDoesNotPromoteBtCausation :
  Shiva.ClaimStatus Shiva.btCottonNationalSuicideCausal
ShivaStructuralClaimDoesNotPromoteBtCausation = Shiva.empiricallyContested

BudjBimAquacultureIsIndependentEvidence :
  BudjBim.EvidenceAuthority BudjBim.systematicKooyangAquaculture
BudjBimAquacultureIsIndependentEvidence = BudjBim.unescoAquaculture

MithakaQuarryingIsIndependentEvidence :
  Mithaka.ClaimStatus Mithaka.largeScaleQuarrying
MithakaQuarryingIsIndependentEvidence = Mithaka.evidencedQuarrying

DarkEmuLocalPracticeCanBeSupportedWhileFramingContested :
  DarkEmu.ClaimStatus DarkEmu.localMaterialPractice ×
  DarkEmu.ClaimStatus DarkEmu.classificatoryLabel
DarkEmuLocalPracticeCanBeSupportedWhileFramingContested =
  DarkEmu.independentlySupportedLocalPractice , DarkEmu.contestedClassification

GBFCoverageDoesNotCreateTerritorialAuthority :
  GBF.Target3State.authority GBF.coverageWithoutAuthorityTransfer ≡
  GBF.originatingCommunityAuthority → ⊥
GBFCoverageDoesNotCreateTerritorialAuthority = GBF.thirtyPercentDoesNotConstructOriginatingAuthority

record Round2AuthorityBoundary : Set where
  constructor round2AuthorityBoundary
  field
    sourcePromotedOnceMeansAllClaimsPromoted : Bool
    sourcePromotedOnceMeansAllClaimsPromotedIsFalse : sourcePromotedOnceMeansAllClaimsPromoted ≡ false
    independentMaterialEvidenceSettlesHistoricalFraming : Bool
    independentMaterialEvidenceSettlesHistoricalFramingIsFalse : independentMaterialEvidenceSettlesHistoricalFraming ≡ false
    legalInstrumentEqualsEffectiveEnforcement : Bool
    legalInstrumentEqualsEffectiveEnforcementIsFalse : legalInstrumentEqualsEffectiveEnforcement ≡ false
    movementAuthorityEqualsEpidemiologicalAuthority : Bool
    movementAuthorityEqualsEpidemiologicalAuthorityIsFalse : movementAuthorityEqualsEpidemiologicalAuthority ≡ false
    conservationRecognitionTransfersTerritorialAuthority : Bool
    conservationRecognitionTransfersTerritorialAuthorityIsFalse : conservationRecognitionTransfersTerritorialAuthority ≡ false

canonicalRound2AuthorityBoundary : Round2AuthorityBoundary
canonicalRound2AuthorityBoundary = round2AuthorityBoundary false refl false refl false refl false refl false refl
