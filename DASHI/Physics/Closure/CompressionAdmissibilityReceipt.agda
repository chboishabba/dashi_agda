module DASHI.Physics.Closure.CompressionAdmissibilityReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- ITIR semantic-compression admissibility.
--
-- CID identity and semantic identity stay separate.  The receipt below only
-- records that a compression is admissible at an active projection grade when
-- every finer grade has an explicit recoverability witness.

data ProjectionGrade : Set where
  exact :
    ProjectionGrade

  pnf :
    ProjectionGrade

  motif :
    ProjectionGrade

  narrative :
    ProjectionGrade

data _≤grade_ : ProjectionGrade → ProjectionGrade → Set where
  exact≤exact :
    exact ≤grade exact

  exact≤pnf :
    exact ≤grade pnf

  exact≤motif :
    exact ≤grade motif

  exact≤narrative :
    exact ≤grade narrative

  pnf≤pnf :
    pnf ≤grade pnf

  pnf≤motif :
    pnf ≤grade motif

  pnf≤narrative :
    pnf ≤grade narrative

  motif≤motif :
    motif ≤grade motif

  motif≤narrative :
    motif ≤grade narrative

  narrative≤narrative :
    narrative ≤grade narrative

data CompressionSourceIdentity : Set where
  cidByteExact :
    String →
    CompressionSourceIdentity

data SemanticIdentity : Set where
  semanticPNFGrade :
    String →
    SemanticIdentity

data CompressionStatus : Set where
  compressionAdmissibleDiagnostic :
    CompressionStatus

data TritRegime : Set where
  tritRefinementOrbitPreserving :
    TritRegime

  tritReframeQuotientProjection :
    TritRegime

  tritDependencyPushBranching :
    TritRegime

record GradeRecoverabilityWitness
    (grade : ProjectionGrade) : Setω where
  field
    requiredDistinctions :
      List String

    recoverableDistinctions :
      List String

    residualsPreserved :
      List String

    recoverabilityHolds :
      Bool

    recoverabilityHoldsIsTrue :
      recoverabilityHolds ≡ true

record CompressionAdmissibilityReceipt : Setω where
  field
    status :
      CompressionStatus

    sourceCID :
      CompressionSourceIdentity

    semanticIdentity :
      SemanticIdentity

    activeGrade :
      ProjectionGrade

    compressedState :
      String

    -- Sharpened §IX condition:
    -- all finer grades Ω' ≤ Ω must have recoverability witnesses.
    recoverabilityAtFinerGrade :
      (grade : ProjectionGrade) →
      grade ≤grade activeGrade →
      GradeRecoverabilityWitness grade

    residualCarrierPreserved :
      Bool

    residualCarrierPreservedIsTrue :
      residualCarrierPreserved ≡ true

    cidSemanticIdentitySeparated :
      Bool

    cidSemanticIdentitySeparatedIsTrue :
      cidSemanticIdentitySeparated ≡ true

    falseSemanticCollapseExcluded :
      Bool

    falseSemanticCollapseExcludedIsTrue :
      falseSemanticCollapseExcluded ≡ true

    tritOrbitTrace :
      List TritRegime

    ultrametricAncestryDescription :
      String

    theoremBoundary :
      List String

canonicalExactRecoverabilityWitness :
  GradeRecoverabilityWitness exact
canonicalExactRecoverabilityWitness =
  record
    { requiredDistinctions =
        "byte-exact CID identity"
        ∷ "semantic PNF-grade identity"
        ∷ "first-class residual carrier"
        ∷ []
    ; recoverableDistinctions =
        "byte-exact CID identity"
        ∷ "semantic PNF-grade identity"
        ∷ "first-class residual carrier"
        ∷ []
    ; residualsPreserved =
        "residuals are retained as visible compression boundary objects"
        ∷ []
    ; recoverabilityHolds =
        true
    ; recoverabilityHoldsIsTrue =
        refl
    }

canonicalPNFRecoverabilityWitness :
  GradeRecoverabilityWitness pnf
canonicalPNFRecoverabilityWitness =
  record
    { requiredDistinctions =
        "projection normal form grade"
        ∷ "PNF residual witness"
        ∷ []
    ; recoverableDistinctions =
        "projection normal form grade"
        ∷ "PNF residual witness"
        ∷ []
    ; residualsPreserved =
        "PNF residuals are not collapsed into semantic equivalence"
        ∷ []
    ; recoverabilityHolds =
        true
    ; recoverabilityHoldsIsTrue =
        refl
    }

canonicalMotifRecoverabilityWitness :
  GradeRecoverabilityWitness motif
canonicalMotifRecoverabilityWitness =
  record
    { requiredDistinctions =
        "shared refinement ancestry"
        ∷ "motif-level semantic carrier"
        ∷ []
    ; recoverableDistinctions =
        "shared refinement ancestry"
        ∷ "motif-level semantic carrier"
        ∷ []
    ; residualsPreserved =
        "motif compression keeps residual disagreement visible"
        ∷ []
    ; recoverabilityHolds =
        true
    ; recoverabilityHoldsIsTrue =
        refl
    }

canonicalNarrativeRecoverabilityWitness :
  GradeRecoverabilityWitness narrative
canonicalNarrativeRecoverabilityWitness =
  record
    { requiredDistinctions =
        "narrative-grade semantic summary"
        ∷ "visible lower-grade recovery request"
        ∷ []
    ; recoverableDistinctions =
        "narrative-grade semantic summary"
        ∷ "visible lower-grade recovery request"
        ∷ []
    ; residualsPreserved =
        "narrative compression records the request to recover lower grades"
        ∷ []
    ; recoverabilityHolds =
        true
    ; recoverabilityHoldsIsTrue =
        refl
    }

canonicalRecoverabilityAtFinerGrade :
  (grade : ProjectionGrade) →
  grade ≤grade motif →
  GradeRecoverabilityWitness grade
canonicalRecoverabilityAtFinerGrade exact exact≤motif =
  canonicalExactRecoverabilityWitness
canonicalRecoverabilityAtFinerGrade pnf pnf≤motif =
  canonicalPNFRecoverabilityWitness
canonicalRecoverabilityAtFinerGrade motif motif≤motif =
  canonicalMotifRecoverabilityWitness

canonicalCompressionAdmissibilityReceipt :
  CompressionAdmissibilityReceipt
canonicalCompressionAdmissibilityReceipt =
  record
    { status =
        compressionAdmissibleDiagnostic
    ; sourceCID =
        cidByteExact "CID identity remains byte-exact and non-semantic"
    ; semanticIdentity =
        semanticPNFGrade "semantic identity is PNF-grade, not CID equality"
    ; activeGrade =
        motif
    ; compressedState =
        "ITIR semantic compression diagnostic at motif grade"
    ; recoverabilityAtFinerGrade =
        canonicalRecoverabilityAtFinerGrade
    ; residualCarrierPreserved =
        true
    ; residualCarrierPreservedIsTrue =
        refl
    ; cidSemanticIdentitySeparated =
        true
    ; cidSemanticIdentitySeparatedIsTrue =
        refl
    ; falseSemanticCollapseExcluded =
        true
    ; falseSemanticCollapseExcludedIsTrue =
        refl
    ; tritOrbitTrace =
        tritRefinementOrbitPreserving
        ∷ tritReframeQuotientProjection
        ∷ tritDependencyPushBranching
        ∷ []
    ; ultrametricAncestryDescription =
        "semantic proximity is shared refinement ancestry, not arithmetic distance"
    ; theoremBoundary =
        "compression at motif grade requires witnesses for exact, PNF, and motif recoverability"
        ∷ "CID equality and semantic equivalence are intentionally not identified"
        ∷ "false semantic collapse is excluded only because residual carriers remain first-class"
        ∷ "this receipt is diagnostic and does not construct an external ITIR runtime authority token"
        ∷ []
    }
