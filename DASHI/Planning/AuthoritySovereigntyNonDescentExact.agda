module DASHI.Planning.AuthoritySovereigntyNonDescentExact where

open import DASHI.Core.Prelude
import DASHI.Core.IntersectionalNonFactorability as INF

------------------------------------------------------------------------
-- AUTHORITY / SOVEREIGNTY NON-DESCENT
--
-- A state's jurisdictional or recognition surface is not treated as the
-- constitutive source of every authority relation present in a place.
-- This is deliberately generic: source-specific Indigenous authority modules
-- may instantiate it without being absorbed into the planning ontology.
------------------------------------------------------------------------

data AuthorityOrigin : Set where
  independentlyConstituted delegatedByState : AuthorityOrigin

data StateRecognition : Set where
  sameRecognitionSurface : StateRecognition

data AuthorityCode : Set where
  independentAuthority delegatedAuthority : AuthorityCode

recognitionObserver : AuthorityOrigin → StateRecognition
recognitionObserver independentlyConstituted = sameRecognitionSurface
recognitionObserver delegatedByState = sameRecognitionSurface

authorityObserver : AuthorityOrigin → AuthorityCode
authorityObserver independentlyConstituted = independentAuthority
authorityObserver delegatedByState = delegatedAuthority

sameRecognition :
  recognitionObserver independentlyConstituted ≡
  recognitionObserver delegatedByState
sameRecognition = refl

differentAuthorityOrigin :
  authorityObserver independentlyConstituted ≡
  authorityObserver delegatedByState → ⊥
differentAuthorityOrigin ()

recognitionCollision :
  INF.NonFactorabilityWitness recognitionObserver authorityObserver
recognitionCollision =
  INF.nonFactorabilityWitness
    independentlyConstituted delegatedByState refl (λ ())

stateRecognitionCannotConstituteEveryAuthority :
  INF.FactorsThrough recognitionObserver authorityObserver → ⊥
stateRecognitionCannotConstituteEveryAuthority =
  INF.witnessRulesOutEveryFlatFactorisation recognitionCollision

record SovereigntyAuthorityBoundary : Set where
  constructor sovereigntyAuthorityBoundary
  field
    effectiveControlImpliesVoluntaryCession : Bool
    effectiveControlImpliesVoluntaryCessionIsFalse :
      effectiveControlImpliesVoluntaryCession ≡ false
    stateRecognitionConstitutesAuthorityOrigin : Bool
    stateRecognitionConstitutesAuthorityOriginIsFalse :
      stateRecognitionConstitutesAuthorityOrigin ≡ false
    administrativeContainmentImpliesAuthorityContainment : Bool
    administrativeContainmentImpliesAuthorityContainmentIsFalse :
      administrativeContainmentImpliesAuthorityContainment ≡ false
    propertyTitleExhaustsCustodialRelation : Bool
    propertyTitleExhaustsCustodialRelationIsFalse :
      propertyTitleExhaustsCustodialRelation ≡ false
    consultationCreatesSovereignty : Bool
    consultationCreatesSovereigntyIsFalse : consultationCreatesSovereignty ≡ false

canonicalSovereigntyAuthorityBoundary : SovereigntyAuthorityBoundary
canonicalSovereigntyAuthorityBoundary =
  sovereigntyAuthorityBoundary false refl false refl false refl false refl false refl
