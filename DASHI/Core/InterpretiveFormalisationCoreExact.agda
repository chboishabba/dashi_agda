module DASHI.Core.InterpretiveFormalisationCoreExact where

------------------------------------------------------------------------
-- INTERPRETIVE FORMALISATION CORE
--
-- Generic DASHI meta-governance substrate. A source expression may be mapped
-- into a formal claim without that map being an equivalence, source theorem,
-- empirical law, or authority transfer. Historical/theoretical sources used by
-- consumers calibrate interpretation; this record calculus is DASHI-owned.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

data TranslationRole : Set where
  directEncoding
  boundedInterpretation
  retrospectiveAnalogy
  conceptualCalibration
  : TranslationRole

data ClaimScope : Set where
  formalOnly
  sourceInterpretive
  empiricalCandidate
  normativeCandidate
  : ClaimScope

data FormalisationCompatibility : Set where
  compatibleBySource
  boundedInterpretiveUse
  methodologicalTension
  contested
  unknown
  : FormalisationCompatibility

record InterpretiveFormalisation : Set₁ where
  constructor interpretive-formalisation
  field
    SourceExpression : Set
    FormalCarrier : Set
    FormalClaim : Set
    sourceReference : String
    formalisationAuthor : String
    formalisationPosition : String
    translation : SourceExpression → FormalClaim
    translationRole : TranslationRole
    formalProofScope : ClaimScope
    sourceInterpretationScope : ClaimScope
    compatibility : FormalisationCompatibility
    claimedLosses : String
    unresolvedResidual : String

open InterpretiveFormalisation public

record InterpretiveFormalisationBoundary : Set where
  constructor interpretive-formalisation-boundary
  field
    translationImpliesEquivalence : Bool
    translationImpliesEquivalenceIsFalse : translationImpliesEquivalence ≡ false
    formalTheoremImpliesSourceTheorem : Bool
    formalTheoremImpliesSourceTheoremIsFalse : formalTheoremImpliesSourceTheorem ≡ false
    sourceMetaphorImpliesFormalIdentity : Bool
    sourceMetaphorImpliesFormalIdentityIsFalse : sourceMetaphorImpliesFormalIdentity ≡ false
    kernelProofImpliesEmpiricalConfirmation : Bool
    kernelProofImpliesEmpiricalConfirmationIsFalse : kernelProofImpliesEmpiricalConfirmation ≡ false
    unresolvedMethodologicalTensionIsFormalDefect : Bool
    unresolvedMethodologicalTensionIsFormalDefectIsFalse :
      unresolvedMethodologicalTensionIsFormalDefect ≡ false

canonicalInterpretiveFormalisationBoundary : InterpretiveFormalisationBoundary
canonicalInterpretiveFormalisationBoundary =
  interpretive-formalisation-boundary false refl false refl false refl false refl false refl
