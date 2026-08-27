module DASHI.Core.RelationalEpistemicProcessSourceBridgeExact where

------------------------------------------------------------------------
-- RELATIONAL EPISTEMIC PROCESS — SOURCE BRIDGE
--
-- Source context:
--   Tyson Yunkaporta, "Sand Talk: How Indigenous Thinking Can Save the World",
--   Text Publishing, 2019, ISBN 9781925773996.
--   Robin Wall Kimmerer, "Braiding Sweetgrass: Indigenous Wisdom, Scientific
--   Knowledge and the Teachings of Plants", later Penguin edition,
--   ISBN 9780141991955.
--
-- The user-supplied DASHI reconstruction describes these works as important
-- conceptual ancestry for relation/context, pattern, story/trajectory,
-- reciprocity, and the rule that action should follow listening/reflection.
--
-- CRITICAL BOUNDARY:
-- This module does NOT formalise Indigenous epistemologies, assert that either
-- author endorses DASHI, or identify their concepts with DASHI motifs.  It owns
-- only a generic process-order abstraction motivated by the supplied reading:
-- gather/contextualise -> relate -> reflect -> act.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Generic process phases.
------------------------------------------------------------------------

data RelationalPhase : Set where
  contextualisePhase relatePhase reflectPhase actPhase : RelationalPhase

contextualise≠act : contextualisePhase ≡ actPhase → ⊥
contextualise≠act ()

relate≠act : relatePhase ≡ actPhase → ⊥
relate≠act ()

reflect≠act : reflectPhase ≡ actPhase → ⊥
reflect≠act ()

record RelationalEpistemicProcess
    (State Context Relation Reflection Action : Set) : Set₁ where
  field
    contextualise : State → Context
    relate : State → Context → Relation
    reflect : State → Context → Relation → Reflection
    act : State → Context → Relation → Reflection → Action

open RelationalEpistemicProcess public

------------------------------------------------------------------------
-- Provenance record: source roles remain metadata, not theorem authority.
------------------------------------------------------------------------

data SourceRole : Set where
  relationalPatternSource reciprocityAndMoreThanHumanRelationSource : SourceRole

record SourceEntry : Set where
  constructor source-entry
  field
    author : String
    title : String
    identifier : String
    role : SourceRole
    theoremAuthority : Bool
    theoremAuthorityIsFalse : theoremAuthority ≡ false

sandTalkSource : SourceEntry
sandTalkSource =
  source-entry
    "Tyson Yunkaporta"
    "Sand Talk: How Indigenous Thinking Can Save the World"
    "ISBN 9781925773996"
    relationalPatternSource
    false refl

braidingSweetgrassSource : SourceEntry
braidingSweetgrassSource =
  source-entry
    "Robin Wall Kimmerer"
    "Braiding Sweetgrass: Indigenous Wisdom, Scientific Knowledge and the Teachings of Plants"
    "ISBN 9780141991955 (Penguin edition)"
    reciprocityAndMoreThanHumanRelationSource
    false refl

------------------------------------------------------------------------
-- No automatic bridge from source vocabulary to motif/stage vocabulary.
------------------------------------------------------------------------

data SourceToMotifIdentificationPermission : Set where

noAutomaticSourceToMotifIdentification :
  SourceToMotifIdentificationPermission → ⊥
noAutomaticSourceToMotifIdentification ()

record RelationalEpistemicProcessBoundary : Set where
  constructor relational-epistemic-process-boundary
  field
    indigenousKnowledgeFormalisedByThisModule : Bool
    indigenousKnowledgeFormalisedByThisModuleIsFalse :
      indigenousKnowledgeFormalisedByThisModule ≡ false
    sourceAuthorEndorsesDASHI : Bool
    sourceAuthorEndorsesDASHIIsFalse : sourceAuthorEndorsesDASHI ≡ false
    sourceConceptEqualsMotif : Bool
    sourceConceptEqualsMotifIsFalse : sourceConceptEqualsMotif ≡ false
    actionMayBypassContextRelationAndReflection : Bool
    actionMayBypassContextRelationAndReflectionIsFalse :
      actionMayBypassContextRelationAndReflection ≡ false

canonicalRelationalEpistemicProcessBoundary : RelationalEpistemicProcessBoundary
canonicalRelationalEpistemicProcessBoundary =
  relational-epistemic-process-boundary
    false refl false refl false refl false refl
