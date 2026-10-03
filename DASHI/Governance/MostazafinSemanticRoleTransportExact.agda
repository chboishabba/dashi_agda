module DASHI.Governance.MostazafinSemanticRoleTransportExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Governance.MostazafinRepresentedConstituencyDivergenceExact as Divergence
import DASHI.Governance.Iran2026RevolutionarySubjectStatePressureExact as Current

------------------------------------------------------------------------
-- MOSTAZAFIN SEMANTIC ROLE TRANSPORT
--
-- Same lexical carrier != same represented relation.
------------------------------------------------------------------------

data MostazafinCarrier : Set where
  quranicOppressedCarrier : MostazafinCarrier
  shariatiRevolutionaryCarrier : MostazafinCarrier
  khomeiniStateIdeologyCarrier : MostazafinCarrier
  foundationCarrier : MostazafinCarrier
  basijCarrier : MostazafinCarrier

data RelationalRole : Set where
  oppressedSubjectRole : RelationalRole
  revolutionaryConstituencyRole : RelationalRole
  claimedBeneficiaryRole : RelationalRole
  antiImperialForeignPolicyRole : RelationalRole
  economicInstitutionRole : RelationalRole
  securityMobilisationRole : RelationalRole

record RoleTransportReceipt : Set where
  constructor role-transport-receipt
  field
    carrier : MostazafinCarrier
    role : RelationalRole
    sourceRef : String
    lexicalContinuity : Bool
    lexicalContinuityIsTrue : lexicalContinuity ≡ true
    sameRelationalRoleAsEveryOtherCarrier : Bool
    sameRelationalRoleAsEveryOtherCarrierIsFalse :
      sameRelationalRoleAsEveryOtherCarrier ≡ false
    institutionalNamingProvesFidelity : Bool
    institutionalNamingProvesFidelityIsFalse :
      institutionalNamingProvesFidelity ≡ false

open RoleTransportReceipt public

revolutionarySubjectTransport : RoleTransportReceipt
revolutionarySubjectTransport =
  role-transport-receipt
    shariatiRevolutionaryCarrier
    revolutionaryConstituencyRole
    "IRGCMostazafinInstitutionalGrammarMechanismExact.glombitza2026"
    true refl false refl false refl

foundationTransport : RoleTransportReceipt
foundationTransport =
  role-transport-receipt
    foundationCarrier
    economicInstitutionRole
    "MostazafinRepresentedConstituencyDivergenceExact.iranicaKhomeiniFoundation"
    true refl false refl false refl

basijTransport : RoleTransportReceipt
basijTransport =
  role-transport-receipt
    basijCarrier
    securityMobilisationRole
    "MostazafinRepresentedConstituencyDivergenceExact.iranicaBasij"
    true refl false refl false refl

data SameLexemeSurface : Set where
  mostazafinLexeme : SameLexemeSurface

data CarrierState : Set where
  revolutionaryState : CarrierState
  foundationState : CarrierState
  basijState : CarrierState

lexemeObserver : CarrierState → SameLexemeSurface
lexemeObserver _ = mostazafinLexeme

roleOutcome : CarrierState → RelationalRole
roleOutcome revolutionaryState = revolutionaryConstituencyRole
roleOutcome foundationState = economicInstitutionRole
roleOutcome basijState = securityMobilisationRole

revolutionaryFoundationDiffer :
  roleOutcome revolutionaryState ≡ roleOutcome foundationState → ⊥
revolutionaryFoundationDiffer ()

sameLexemeDoesNotDetermineRole :
  INF.FactorsThrough lexemeObserver roleOutcome → ⊥
sameLexemeDoesNotDetermineRole =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness
      revolutionaryState
      foundationState
      refl
      revolutionaryFoundationDiffer)

record SemanticPersistenceBoundary : Set where
  constructor semantic-persistence-boundary
  field
    lexemePersistsAcrossInstitutions : Bool
    roleMayChangeAcrossInstitutions : Bool
    roleChangeErasesHistoricalMeaning : Bool
    lexicalPersistenceProvesMaterialFidelity : Bool
    currentSecurityUseDefinesOriginalMeaning : Bool
    originalMeaningDeterminesCurrentPractice : Bool

canonicalBoundary : SemanticPersistenceBoundary
canonicalBoundary =
  semantic-persistence-boundary true true false false false false

currentBasijCommand : Current.CurrentStateReceipt
currentBasijCommand = Current.currentBasijCommandReceipt

divergenceCandidate : Divergence.StateActionDivergenceCandidate
divergenceCandidate = Divergence.labourDivergenceCandidate

data RoleInversionMeansSemanticExtinction : Set where
data OriginalMeaningGuaranteesLaterInstitutionalPractice : Set where
data SecurityInstitutionNameProvesProtectedSubjectRelation : Set where

roleInversionDoesNotProveSemanticExtinction :
  RoleInversionMeansSemanticExtinction → ⊥
roleInversionDoesNotProveSemanticExtinction ()

originalMeaningDoesNotGuaranteePractice :
  OriginalMeaningGuaranteesLaterInstitutionalPractice → ⊥
originalMeaningDoesNotGuaranteePractice ()

securityNameDoesNotProveProtection :
  SecurityInstitutionNameProvesProtectedSubjectRelation → ⊥
securityNameDoesNotProveProtection ()
