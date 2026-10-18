module DASHI.Core.LexicalScopeResolutionExact where

open import DASHI.Core.Prelude

------------------------------------------------------------------------
-- INNERMOST-FIRST LEXICAL LOOKUP
--
-- Concrete extractors may encode scope identities however they like, but local
-- name resolution obeys one invariant: inspect the nearest scope first; only
-- when it has no matching binder may lookup continue outward.
------------------------------------------------------------------------

data ScopeLookup : Set where
  binderPresent : ScopeLookup
  binderAbsent : ScopeLookup

data TwoScopeResolution : Set where
  useInnerBinder : TwoScopeResolution
  useOuterBinder : TwoScopeResolution
  noLocalBinder : TwoScopeResolution

resolveTwoScopes :
  ScopeLookup →
  ScopeLookup →
  TwoScopeResolution
resolveTwoScopes binderPresent _ = useInnerBinder
resolveTwoScopes binderAbsent binderPresent = useOuterBinder
resolveTwoScopes binderAbsent binderAbsent = noLocalBinder

innerBinderShadowsOuter :
  ∀ outer →
  resolveTwoScopes binderPresent outer
    ≡ useInnerBinder
innerBinderShadowsOuter _ = refl

missingInnerFallsBackToOuter :
  resolveTwoScopes binderAbsent binderPresent
    ≡ useOuterBinder
missingInnerFallsBackToOuter = refl

missingBothLeavesLocalResolution :
  resolveTwoScopes binderAbsent binderAbsent
    ≡ noLocalBinder
missingBothLeavesLocalResolution = refl

data LexicalScopeKind : Set where
  clauseScope : LexicalScopeKind
  lambdaScope : LexicalScopeKind
  forallScope : LexicalScopeKind

record LexicalScopeResolutionBoundary : Set where
  constructor lexicalScopeResolutionBoundary
  field
    innerBinderMayBeSkippedForOuterSameName : Bool
    innerBinderMayBeSkippedForOuterSameNameIsFalse :
      innerBinderMayBeSkippedForOuterSameName ≡ false

    absentInnerMayFallBackOutward : Bool
    absentInnerMayFallBackOutwardIsTrue :
      absentInnerMayFallBackOutward ≡ true

    lexicalMissMayInventGlobalBinder : Bool
    lexicalMissMayInventGlobalBinderIsFalse :
      lexicalMissMayInventGlobalBinder ≡ false

canonicalLexicalScopeResolutionBoundary :
  LexicalScopeResolutionBoundary
canonicalLexicalScopeResolutionBoundary =
  lexicalScopeResolutionBoundary
    false refl
    true refl
    false refl
