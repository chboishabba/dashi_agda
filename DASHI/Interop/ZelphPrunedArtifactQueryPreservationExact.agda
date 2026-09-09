module DASHI.Interop.ZelphPrunedArtifactQueryPreservationExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- Archive donor: RequestProject.CompilerPipeline.
--
-- The generic compiled base is deletion-only for the modeled relation families.
-- Aristotle proves monotonicity of relation-word answers from compiled -> source;
-- stronger equality is proved only for specifically certified stages/corpora.
-- Therefore a pruned Zelph artifact receives no blanket full-graph completeness.
------------------------------------------------------------------------

record AristotleCompilerContract : Set where
  constructor aristotle-compiler-contract
  field
    sourceModule : String
    declaration : String
    contractReference : String
open AristotleCompilerContract public

subDeletionContract : AristotleCompilerContract
subDeletionContract =
  aristotle-compiler-contract
    "RequestProject.CompilerPipeline"
    "Wikidata.CompilerPipeline.compiled_sub_subset"
    "compiled subclass edges are a subset of source subclass edges"

instancePreservationContract : AristotleCompilerContract
instancePreservationContract =
  aristotle-compiler-contract
    "RequestProject.CompilerPipeline"
    "Wikidata.CompilerPipeline.compiled_inst"
    "the modeled compiler preserves the instance edge set"

wordMonotonicityContract : AristotleCompilerContract
wordMonotonicityContract =
  aristotle-compiler-contract
    "RequestProject.CompilerPipeline"
    "Wikidata.CompilerPipeline.wordStep_compiled_mono"
    "every relation-word answer in the compiled base is also an answer in the source base"

record QueryFamilyPreservationReceipt : Set where
  constructor query-family-preservation-receipt
  field
    sourceArtifactReference : String
    prunedArtifactReference : String
    queryFamilyReference : String
    sourceRevisionReference : String
    prunedRevisionReference : String
    soundnessReference : String
    completenessReference : String
    preservesSoundness : Bool
    preservesSoundnessIsTrue : preservesSoundness ≡ true
    preservesCompleteness : Bool
    preservesCompletenessIsTrue : preservesCompleteness ≡ true
open QueryFamilyPreservationReceipt public

record QueryFamilySoundnessReceipt : Set where
  constructor query-family-soundness-receipt
  field
    sourceArtifactReference : String
    prunedArtifactReference : String
    queryFamilyReference : String
    soundnessReference : String
    preservesSoundness : Bool
    preservesSoundnessIsTrue : preservesSoundness ≡ true
open QueryFamilySoundnessReceipt public

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data PrunedAnswerImpliesSourceAnswer : Set where
  pruned-to-source : PrunedAnswerImpliesSourceAnswer

data SourceAnswerImpliesPrunedAnswerWithoutCertificate : Set where
data PrunedArtifactEquivalentToFullGraphWithoutCertificate : Set where
data PrunedAbsenceImpliesSourceAbsenceWithoutCertificate : Set where

sourceAnswerDoesNotFollowBackWithoutCompleteness :
  SourceAnswerImpliesPrunedAnswerWithoutCertificate → ⊥
sourceAnswerDoesNotFollowBackWithoutCompleteness ()

prunedArtifactDoesNotBecomeFullGraphEquivalent :
  PrunedArtifactEquivalentToFullGraphWithoutCertificate → ⊥
prunedArtifactDoesNotBecomeFullGraphEquivalent ()

prunedNonObservationDoesNotProveSourceAbsence :
  PrunedAbsenceImpliesSourceAbsenceWithoutCertificate → ⊥
prunedNonObservationDoesNotProveSourceAbsence ()

record PrunedArtifactBoundary : Set where
  constructor pruned-artifact-boundary
  field
    compiledToSourceMonotonicityAvailable : Bool
    sourceToCompiledCompletenessAutomatic : Bool
    queryFamilyCertificateMayAddCompleteness : Bool
    prunedAbsenceProvesSourceAbsenceWithoutCertificate : Bool

canonicalPrunedArtifactBoundary : PrunedArtifactBoundary
canonicalPrunedArtifactBoundary =
  pruned-artifact-boundary true false true false

prunedArtifactStatement : String
prunedArtifactStatement =
  "A pruned Zelph/Wikidata artifact may be used soundly for a declared query family when its construction guarantees deletion-only monotonicity, but source-to-pruned completeness is not automatic. Absence in the pruned artifact is not absence in the source unless a revision-bound query-family preservation receipt proves completeness for that family."
