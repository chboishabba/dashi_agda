module DASHI.Governance.ReligiousPoliticalIdentityNoncollapseExact where

open import DASHI.Core.Prelude
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- RELIGIOUS / PEOPLEHOOD / POLITICAL-IDEOLOGY / STATE NONCOLLAPSE
--
-- Generic boundary.  It does not decide whether any concrete utterance is
-- antisemitic, anti-Zionist, Zionist, religious, nationalist or lawful.
-- Those are source- and context-specific downstream judgements.
------------------------------------------------------------------------

data JewishReligiousPoliticalLayer : Set where
  judaismReligiousTradition : JewishReligiousPoliticalLayer
  jewishPeoplehoodIdentity : JewishReligiousPoliticalLayer
  jewishPoliticalPosition : JewishReligiousPoliticalLayer
  zionistPoliticalIdeology : JewishReligiousPoliticalLayer
  antiZionistPoliticalPosition : JewishReligiousPoliticalLayer
  stateOfIsraelInstitution : JewishReligiousPoliticalLayer
  israeliGovernmentInstitution : JewishReligiousPoliticalLayer
  israeliPolicyPosition : JewishReligiousPoliticalLayer
  antisemitismHateCategory : JewishReligiousPoliticalLayer

data JewishIdentityImpliesZionism : Set where
data ZionismImpliesReligiousJudaism : Set where
data StateOfIsraelEqualsJudaism : Set where
data IsraeliGovernmentRepresentsAllJewishPeople : Set where
data CriticismOfIsraelIsDefinitionallyAntisemitic : Set where
data AntiZionismIsDefinitionallyAntisemitic : Set where

jewishIdentityDoesNotDefinitionallyImplyZionism :
  JewishIdentityImpliesZionism → ⊥
jewishIdentityDoesNotDefinitionallyImplyZionism ()

zionismDoesNotDefinitionallyImplyReligiousJudaism :
  ZionismImpliesReligiousJudaism → ⊥
zionismDoesNotDefinitionallyImplyReligiousJudaism ()

stateOfIsraelDoesNotDefinitionallyEqualJudaism :
  StateOfIsraelEqualsJudaism → ⊥
stateOfIsraelDoesNotDefinitionallyEqualJudaism ()

israeliGovernmentDoesNotDefinitionallyRepresentAllJewishPeople :
  IsraeliGovernmentRepresentsAllJewishPeople → ⊥
israeliGovernmentDoesNotDefinitionallyRepresentAllJewishPeople ()

criticismOfIsraelIsNotDefinitionallyAntisemitic :
  CriticismOfIsraelIsDefinitionallyAntisemitic → ⊥
criticismOfIsraelIsNotDefinitionallyAntisemitic ()

antiZionismIsNotDefinitionallyAntisemitic :
  AntiZionismIsDefinitionallyAntisemitic → ⊥
antiZionismIsNotDefinitionallyAntisemitic ()

data ContextualSpeechRisk : Set where
  politicalCriticism : ContextualSpeechRisk
  ambiguousProxyUse : ContextualSpeechRisk
  antiJewishHateEvidence : ContextualSpeechRisk

record ContextualClassificationReceipt : Set where
  constructor contextual-classification-receipt
  field
    risk : ContextualSpeechRisk
    utteranceReceipt : String
    targetReceipt : String
    surroundingContextReceipt : String
    politicalCriticismProtectedAsDistinctCategory : Bool
    hateClassificationRequiresContextualEvidence : Bool
    lexicalTermAloneClosesClassification : Bool

open ContextualClassificationReceipt public

mkContextualReceipt :
  ContextualSpeechRisk → String → String → String →
  ContextualClassificationReceipt
mkContextualReceipt risk utterance target context =
  contextual-classification-receipt
    risk utterance target context
    true true false
