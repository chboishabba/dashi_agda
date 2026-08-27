module DASHI.Governance.CaceresDefenderPatternBridgeExact where

open import DASHI.Core.Prelude
import DASHI.Governance.CaceresAuthorityWithoutEnforcementExact as Caceres
import DASHI.Governance.EnvironmentalAuthoritySourceRegistryRound2Exact as Sources

------------------------------------------------------------------------
-- CACERES AS JUDICIALLY / INSTITUTIONALLY DOCUMENTED EXEMPLAR INSIDE A
-- BROADER DOCUMENTED DEFENDER-RISK PATTERN.
--
-- Goldman Environmental Prize supplies independent institutional recognition
-- of the Agua Zarca campaign.  Global Witness supplies a separately scoped
-- global monitoring series.  The aggregate dataset does not make every case
-- legally identical to Caceres, and Caceres does not prove the global count.
------------------------------------------------------------------------

data EvidenceScale : Set where
  caseSpecificJudicial institutionalRecognition globalMonitoring : EvidenceScale

record DefenderEvidenceLayer : Set where
  constructor defenderEvidenceLayer
  field
    scale : EvidenceScale
    protectionOrStandingCode : Nat
    enforcementFailureCode : Nat

caceresCaseLayer : DefenderEvidenceLayer
caceresCaseLayer = defenderEvidenceLayer caseSpecificJudicial 1 1

goldmanRecognitionLayer : DefenderEvidenceLayer
goldmanRecognitionLayer = defenderEvidenceLayer institutionalRecognition 1 0

globalWitnessPatternLayer : DefenderEvidenceLayer
globalWitnessPatternLayer = defenderEvidenceLayer globalMonitoring 2253 146

caseStandingStillDoesNotConstructEnforcement :
  Caceres.EffectiveEnforcement Caceres.victimStanding → ⊥
caseStandingStillDoesNotConstructEnforcement = Caceres.victimStandingDoesNotConstructEnforcement

goldmanSource : Sources.SourceReference
goldmanSource = Sources.goldmanCaceres2015

globalWitnessSource : Sources.SourceReference
globalWitnessSource = Sources.globalWitness2025

record DefenderPatternBoundary : Set where
  constructor defenderPatternBoundary
  field
    globalCountMakesEveryCaseLegallyEquivalent : Bool
    globalCountMakesEveryCaseLegallyEquivalentIsFalse : globalCountMakesEveryCaseLegallyEquivalent ≡ false
    prizeRecognitionEqualsEffectiveProtection : Bool
    prizeRecognitionEqualsEffectiveProtectionIsFalse : prizeRecognitionEqualsEffectiveProtection ≡ false
    oneJudicialCaseAloneEstablishesGlobalBaseRate : Bool
    oneJudicialCaseAloneEstablishesGlobalBaseRateIsFalse : oneJudicialCaseAloneEstablishesGlobalBaseRate ≡ false

canonicalDefenderPatternBoundary : DefenderPatternBoundary
canonicalDefenderPatternBoundary = defenderPatternBoundary false refl false refl false refl
