module DASHI.Foundations.Wette1969Rule915ParameterCoherenceExact where

------------------------------------------------------------------------
-- WETTE 1969 RULE 9.1.5 SAME-OBJECT PARAMETER COHERENCE
--
-- The first-seven and later-premise modules were intentionally recovered in
-- stages.  Several source words occur in both blocks: V, W2, V2, V1, W1, U,
-- U1.  A complete historical instance must identify those occurrences as the
-- SAME words, not merely words with compatible roles.
--
-- This module closes that staging seam explicitly rather than relying on naming
-- conventions.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Foundations.Wette1969Rule915PredicateProducerExact as First
import DASHI.Foundations.Wette1969Rule915LaterPremiseTemplatesExact as Later

record Rule915ParameterCoherence
    (first : First.Rule915FirstSevenParameters)
    (later : Later.Rule915LaterParameters) : Set where
  constructor rule915ParameterCoherence
  field
    sameArityV : Later.arityWord later ≡ First.arityWord first
    samePredicateMarkW2 : Later.predicateMarkW2 later ≡ First.predicateMarkWord first
    sameVariableTupleV2 : Later.tupleV2 later ≡ First.variableTupleWord first
    samePredicateSchemaV1 : Later.schemaV1 later ≡ First.predicateSchemaWord first
    samePredicateSchemaW1 :
      Later.schemaW1 later ≡ First.doubledPredicateSchemaWord first
    sameDefiniensU : Later.definiensSchemaWord later ≡ First.definiensSchemaWord first
    sameDefinitionPrerequisiteU1 :
      Later.definitionPrerequisiteWord later ≡ First.definitionPrerequisiteWord first

open Rule915ParameterCoherence public

record CoherentRule915Parameters : Set₁ where
  constructor coherentRule915Parameters
  field
    firstSeven : First.Rule915FirstSevenParameters
    laterTwenty : Later.Rule915LaterParameters
    coherence : Rule915ParameterCoherence firstSeven laterTwenty

open CoherentRule915Parameters public

coherentTranscription :
  CoherentRule915Parameters → First.Rule915PremiseTranscription
coherentTranscription parameters =
  Later.completeTypedTranscription
    (firstSeven parameters)
    (laterTwenty parameters)

-- Useful same-object receipts consumed by later welds.
coherentDefiniensWord :
  (parameters : CoherentRule915Parameters) →
  Later.definiensSchemaWord (laterTwenty parameters)
    ≡ First.definiensSchemaWord (firstSeven parameters)
coherentDefiniensWord parameters = sameDefiniensU (coherence parameters)

coherentDefinitionPrerequisite :
  (parameters : CoherentRule915Parameters) →
  Later.definitionPrerequisiteWord (laterTwenty parameters)
    ≡ First.definitionPrerequisiteWord (firstSeven parameters)
coherentDefinitionPrerequisite parameters =
  sameDefinitionPrerequisiteU1 (coherence parameters)

record Wette1969Rule915ParameterCoherenceBoundary : Set where
  constructor wette1969Rule915ParameterCoherenceBoundary
  field
    stagedPremiseBlocksNowRequireSameObjectWeld : Bool
    stagedPremiseBlocksNowRequireSameObjectWeldIsTrue :
      stagedPremiseBlocksNowRequireSameObjectWeld ≡ true
    roleCompatibilityAloneIsEnoughForHistoricalIdentity : Bool
    roleCompatibilityAloneIsEnoughForHistoricalIdentityIsFalse :
      roleCompatibilityAloneIsEnoughForHistoricalIdentity ≡ false
    coherentParameterPackageStillDoesNotProvePremises : Bool
    coherentParameterPackageStillDoesNotProvePremisesIsTrue :
      coherentParameterPackageStillDoesNotProvePremises ≡ true

canonicalWette1969Rule915ParameterCoherenceBoundary :
  Wette1969Rule915ParameterCoherenceBoundary
canonicalWette1969Rule915ParameterCoherenceBoundary =
  wette1969Rule915ParameterCoherenceBoundary
    true refl false refl true refl
