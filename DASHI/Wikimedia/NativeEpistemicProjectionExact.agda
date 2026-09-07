module DASHI.Wikimedia.NativeEpistemicProjectionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)

import DASHI.Ontology.EpistemicTrit as Trit
import DASHI.Ontology.WikidataEpistemicBridge as Epistemic
import DASHI.Wikimedia.NativeStatementExact as Native

------------------------------------------------------------------------
-- NATIVE WIKIDATA -> EXISTING DASHI EPISTEMIC PROJECTION
--
-- The native statement carrier is the data-language authority inside DASHI.
-- EpistemicTrit remains a downstream interpretation.  This projection therefore
-- requires an explicit qualifier/context interpretation rather than pretending
-- that Wikidata rank/snaks are already epistemic truth values.
------------------------------------------------------------------------

projectRank : Native.StatementRank → Epistemic.StatementRank
projectRank Native.preferred = Epistemic.preferred
projectRank Native.normal = Epistemic.normal
projectRank Native.deprecated = Epistemic.deprecated

referenceIds : List Native.ReferenceBlock → List String
referenceIds [] = []
referenceIds (reference ∷ rest) =
  Native.referenceId reference ∷ referenceIds rest

projectStatement :
  {QualifierAxis : Set} →
  Native.Statement →
  (QualifierAxis → Trit.EpistemicTrit) →
  Epistemic.StatementEnvelope QualifierAxis
projectStatement statement qualifierInterpretation =
  Epistemic.statementEnvelope
    (Native.statementId statement)
    qualifierInterpretation
    (referenceIds (Native.references statement))
    (projectRank (Native.rank statement))

statementIdPreserved :
  {QualifierAxis : Set}
  (statement : Native.Statement)
  (interpretation : QualifierAxis → Trit.EpistemicTrit) →
  Epistemic.statementId (projectStatement statement interpretation)
  ≡ Native.statementId statement
statementIdPreserved statement interpretation = refl

rankPreserved :
  {QualifierAxis : Set}
  (statement : Native.Statement)
  (interpretation : QualifierAxis → Trit.EpistemicTrit) →
  Epistemic.rankMetadata (projectStatement statement interpretation)
  ≡ projectRank (Native.rank statement)
rankPreserved statement interpretation = refl

referencesPreservedByIdentifier :
  {QualifierAxis : Set}
  (statement : Native.Statement)
  (interpretation : QualifierAxis → Trit.EpistemicTrit) →
  Epistemic.sourceReferences (projectStatement statement interpretation)
  ≡ referenceIds (Native.references statement)
referencesPreservedByIdentifier statement interpretation = refl

-- The interpretation is explicit and survives projection unchanged.
qualifierInterpretationPreserved :
  {QualifierAxis : Set}
  (statement : Native.Statement)
  (interpretation : QualifierAxis → Trit.EpistemicTrit)
  (axis : QualifierAxis) →
  Epistemic.qualifierState (projectStatement statement interpretation) axis
  ≡ interpretation axis
qualifierInterpretationPreserved statement interpretation axis = refl

data NativeRankDeterminesEpistemicState : Set where
data NativeSnakAutomaticallyInterpretsQualifierAxis : Set where

rankDoesNotDetermineEpistemicState : NativeRankDeterminesEpistemicState → ⊥
rankDoesNotDetermineEpistemicState ()

snakDoesNotAutomaticallyInterpretQualifierAxis :
  NativeSnakAutomaticallyInterpretsQualifierAxis → ⊥
snakDoesNotAutomaticallyInterpretsQualifierAxis ()
