module DASHI.Core.RepresentationSubjectPositionNonfactorabilityExact where

------------------------------------------------------------------------
-- REPRESENTABILITY != ORIGINATING SUBJECT POSITION
--
-- SOURCE CONTEXT
--
-- Luce Irigaray, "This Sex Which Is Not One", Cornell University Press,
-- 1985 English edition. ISBN 9780801493317.
--
-- Irigaray motivates the representational/symbolic-order reading.  The exact
-- non-factorability statements below are DASHI constructions and are not
-- attributed to her as formal theorems.
--
-- CENTRAL DISTINCTIONS
--
--   system has a category for x != x occupies an originating subject-position
--   speech observable          != transparent access to underlying position
--   represented exchange node  != originating authority in the relation
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Core.IntersectionalNonFactorability as INF

------------------------------------------------------------------------
-- Category visibility can collapse subject-position authority.
------------------------------------------------------------------------

data RepresentedState : Set where
  representedOnly originatingSubject : RepresentedState

data CategoryVisibility : Set where
  visibleCategory : CategoryVisibility

data SubjectPosition : Set where
  representedPosition originatingPosition : SubjectPosition

categoryVisibility : RepresentedState → CategoryVisibility
categoryVisibility representedOnly = visibleCategory
categoryVisibility originatingSubject = visibleCategory

subjectPosition : RepresentedState → SubjectPosition
subjectPosition representedOnly = representedPosition
subjectPosition originatingSubject = originatingPosition

subjectPositionDiffers :
  subjectPosition representedOnly ≡ subjectPosition originatingSubject → ⊥
subjectPositionDiffers ()

categoryVisibilityCannotRecoverSubjectPosition :
  INF.FactorsThrough categoryVisibility subjectPosition → ⊥
categoryVisibilityCannotRecoverSubjectPosition =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness
      representedOnly originatingSubject refl subjectPositionDiffers)

------------------------------------------------------------------------
-- Language is an observer, not transparent access to the fine subject state.
------------------------------------------------------------------------

data FineSubjectState : Set where
  fineStateA fineStateB : FineSubjectState

data UtteranceSurface : Set where
  sameUtterance : UtteranceSurface

data FinePosition : Set where
  finePositionA finePositionB : FinePosition

speechObserver : FineSubjectState → UtteranceSurface
speechObserver fineStateA = sameUtterance
speechObserver fineStateB = sameUtterance

finePosition : FineSubjectState → FinePosition
finePosition fineStateA = finePositionA
finePosition fineStateB = finePositionB

finePositionDiffers :
  finePosition fineStateA ≡ finePosition fineStateB → ⊥
finePositionDiffers ()

speechSurfaceCannotRecoverFinePosition :
  INF.FactorsThrough speechObserver finePosition → ⊥
speechSurfaceCannotRecoverFinePosition =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness fineStateA fineStateB refl finePositionDiffers)

------------------------------------------------------------------------
-- Exchange/object visibility can likewise collapse originating authority.
------------------------------------------------------------------------

data ExchangeState : Set where
  exchangedObjectState originatingAuthorityState : ExchangeState

data ExchangeSurface : Set where
  sameExchangeNode : ExchangeSurface

data ExchangeAuthority : Set where
  representedObjectRole originatingAuthorityRole : ExchangeAuthority

exchangeSurface : ExchangeState → ExchangeSurface
exchangeSurface exchangedObjectState = sameExchangeNode
exchangeSurface originatingAuthorityState = sameExchangeNode

exchangeAuthority : ExchangeState → ExchangeAuthority
exchangeAuthority exchangedObjectState = representedObjectRole
exchangeAuthority originatingAuthorityState = originatingAuthorityRole

exchangeAuthorityDiffers :
  exchangeAuthority exchangedObjectState
  ≡ exchangeAuthority originatingAuthorityState → ⊥
exchangeAuthorityDiffers ()

exchangeSurfaceCannotRecoverOriginatingAuthority :
  INF.FactorsThrough exchangeSurface exchangeAuthority → ⊥
exchangeSurfaceCannotRecoverOriginatingAuthority =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness
      exchangedObjectState originatingAuthorityState
      refl exchangeAuthorityDiffers)

------------------------------------------------------------------------
-- Boundary.
------------------------------------------------------------------------

record RepresentationSubjectPositionBoundary : Set where
  constructor representation-subject-position-boundary
  field
    representableImpliesOriginatingSubject : Bool
    representableImpliesOriginatingSubjectIsFalse :
      representableImpliesOriginatingSubject ≡ false
    utteranceSurfaceTransparentlyDeterminesFineSubject : Bool
    utteranceSurfaceTransparentlyDeterminesFineSubjectIsFalse :
      utteranceSurfaceTransparentlyDeterminesFineSubject ≡ false
    exchangeVisibilityImpliesOriginatingAuthority : Bool
    exchangeVisibilityImpliesOriginatingAuthorityIsFalse :
      exchangeVisibilityImpliesOriginatingAuthority ≡ false
    structuralWitnessProvesEmpiricalSocialClaim : Bool
    structuralWitnessProvesEmpiricalSocialClaimIsFalse :
      structuralWitnessProvesEmpiricalSocialClaim ≡ false

canonicalRepresentationSubjectPositionBoundary :
  RepresentationSubjectPositionBoundary
canonicalRepresentationSubjectPositionBoundary =
  representation-subject-position-boundary
    false refl
    false refl
    false refl
    false refl
