module DASHI.Reasoning.KantAntinomyCore where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Cognition.PNF.EventAlgebra as PNF
import DASHI.Reasoning.KantCriticalCompiler as Kant

------------------------------------------------------------------------
-- Antinomy is distinct from ordinary same-scope contradiction.
------------------------------------------------------------------------

data AntinomyKind : Set where
  mathematicalAntinomy dynamicalAntinomy : AntinomyKind

record AntinomyReceipt : Set₁ where
  field
    thesis antithesis : PNF.EventPNF
    thesisDerivation antithesisDerivation : String
    sharedUnconditionedAssumption : String
    kind : AntinomyKind
    boundaryTransgression : Kant.CriticalBoundary
    ordinarySameScopeContradictionClaimed : Bool

record MathematicalAntinomyResolution : Set₁ where
  field
    receipt : AntinomyReceipt
    receiptIsMathematical :
      AntinomyReceipt.kind receipt ≡ mathematicalAntinomy
    completedWorldGivenAsPhenomenalObject : Bool
    thesisConstitutivelyPromoted : Bool
    antithesisConstitutivelyPromoted : Bool
    regressRemainsOpen : Bool
    resolutionReceipt : String

record DynamicalAntinomyResolution : Set₁ where
  field
    receipt : AntinomyReceipt
    receiptIsDynamical :
      AntinomyReceipt.kind receipt ≡ dynamicalAntinomy
    phenomenalScope : String
    intelligibleScope : String
    scopesDistinct : Bool
    sameScopeContradictionClaimed : Bool
    crossScopeCompatibilityCandidate : Bool
    resolutionReceipt : String

record AntinomyFailureDistinction : Set where
  field
    contradictionResult : Kant.CriticalResult
    noMeetResult : Kant.CriticalResult
    antinomyResult : Kant.CriticalResult
    equivocationResult : Kant.CriticalResult
    scopeExcessResult : Kant.CriticalResult
    allCollapsedToOneFailureCode : Bool

canonicalAntinomyFailureDistinction : AntinomyFailureDistinction
canonicalAntinomyFailureDistinction = record
  { contradictionResult = Kant.contradictionResult
  ; noMeetResult = Kant.noTypedMeetResult
  ; antinomyResult = Kant.antinomicResult
  ; equivocationResult = Kant.formallyValidEquivocationResult
  ; scopeExcessResult = Kant.scopeExceededResult
  ; allCollapsedToOneFailureCode = false
  }

record KantAntinomyAuthorityBoundary : Set where
  field
    mathematicalAndDynamicalResolutionsDistinguished : Bool
    mathematicalThesisAutomaticallyTrue : Bool
    mathematicalAntithesisAutomaticallyTrue : Bool
    dynamicalClaimsForcedIntoSameScope : Bool
    antinomyEqualsOrdinaryContradiction : Bool
    cantorIsKantsOwnResolutionClaimed : Bool
    politicalConflictAutomaticallyAntinomy : Bool
    boundaryNote : String

canonicalKantAntinomyAuthorityBoundary : KantAntinomyAuthorityBoundary
canonicalKantAntinomyAuthorityBoundary = record
  { mathematicalAndDynamicalResolutionsDistinguished = true
  ; mathematicalThesisAutomaticallyTrue = false
  ; mathematicalAntithesisAutomaticallyTrue = false
  ; dynamicalClaimsForcedIntoSameScope = false
  ; antinomyEqualsOrdinaryContradiction = false
  ; cantorIsKantsOwnResolutionClaimed = false
  ; politicalConflictAutomaticallyAntinomy = false
  ; boundaryNote =
      "Mathematical antinomies audit a presumed completed whole; dynamical antinomies permit scope-separated compatibility. Both remain distinct from PNF contradiction and no-typed-meet."
  }
