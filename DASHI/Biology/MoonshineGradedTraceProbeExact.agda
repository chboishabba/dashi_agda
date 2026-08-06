module DASHI.Biology.MoonshineGradedTraceProbeExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Richard E. Borcherds,
-- "Monstrous Moonshine and Monstrous Lie Superalgebras".
-- DOI: 10.1007/BF01232032.
--
-- Chongying Dong, Robert L. Griess Jr. and Ching Hung Lam,
-- "Uniqueness Results for the Moonshine Vertex Operator Algebra".
-- DOI: 10.1353/ajm.2007.0009.
--
-- James Lepowsky and Haisheng Li,
-- "Introduction to Vertex Operator Algebras and Their Representations".
-- DOI: 10.1007/978-0-8176-8186-9.
--
-- DASHI CONTRIBUTION
-- Replace one-dimensional arithmetic matching by a finite grade-indexed trace
-- probe family.  Equality on the three explicit identity-trace probes
-- determines a truncated profile exactly.  Dimension, finite-character,
-- graded-trace, mode-compatibility and VOA-isomorphism authority levels remain
-- distinct constructors; no promotion theorem is fabricated.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Empty using (⊥)

import DASHI.Physics.Common.SeparatingProbeFamilyExact as Common

data TraceGrade : Set where
  traceWeightZero : TraceGrade
  traceWeightOne : TraceGrade
  traceWeightTwo : TraceGrade

record TruncatedIdentityTraceProfile : Set where
  constructor truncatedIdentityTraceProfile
  field
    traceAtWeightZero : Nat
    traceAtWeightOne : Nat
    traceAtWeightTwo : Nat

open TruncatedIdentityTraceProfile public

observeIdentityTrace :
  TraceGrade → TruncatedIdentityTraceProfile → Nat
observeIdentityTrace traceWeightZero profile = traceAtWeightZero profile
observeIdentityTrace traceWeightOne profile = traceAtWeightOne profile
observeIdentityTrace traceWeightTwo profile = traceAtWeightTwo profile

identityTraceProbesSeparate :
  ∀ left right →
  ((probe : TraceGrade) →
    observeIdentityTrace probe left ≡ observeIdentityTrace probe right) →
  left ≡ right
identityTraceProbesSeparate
  (truncatedIdentityTraceProfile leftZero leftOne leftTwo)
  (truncatedIdentityTraceProfile rightZero rightOne rightTwo)
  agreement
  rewrite agreement traceWeightZero
        | agreement traceWeightOne
        | agreement traceWeightTwo = refl

identityTraceProbeSystem :
  Common.SeparatingProbeSystem TruncatedIdentityTraceProfile Nat
identityTraceProbeSystem =
  Common.separatingProbeSystem
    TraceGrade
    observeIdentityTrace
    identityTraceProbesSeparate

moonshineInitialIdentityTraceProfile : TruncatedIdentityTraceProfile
moonshineInitialIdentityTraceProfile =
  truncatedIdentityTraceProfile 1 0 196884

moonshineWeightZeroTraceExact :
  observeIdentityTrace traceWeightZero moonshineInitialIdentityTraceProfile ≡ 1
moonshineWeightZeroTraceExact = refl

moonshineWeightOneTraceExact :
  observeIdentityTrace traceWeightOne moonshineInitialIdentityTraceProfile ≡ 0
moonshineWeightOneTraceExact = refl

moonshineWeightTwoTraceExact :
  observeIdentityTrace traceWeightTwo moonshineInitialIdentityTraceProfile
  ≡ 196884
moonshineWeightTwoTraceExact = refl

data AuthorityLevel : Set where
  dimensionAgreement : AuthorityLevel
  finiteCharacterAgreement : AuthorityLevel
  gradedTraceAgreement : AuthorityLevel
  modeCompatibility : AuthorityLevel
  voaIsomorphism : AuthorityLevel

dimensionIsNotVOAIsomorphism :
  dimensionAgreement ≡ voaIsomorphism → ⊥
dimensionIsNotVOAIsomorphism ()

gradedTraceIsNotVOAIsomorphism :
  gradedTraceAgreement ≡ voaIsomorphism → ⊥
gradedTraceIsNotVOAIsomorphism ()

data UniquenessCondition : Set where
  selfDualAndC2Cofinite : UniquenessCondition
  dimensionBoundFromWeightThree : UniquenessCondition
  centralChargeTwentyFour : UniquenessCondition
  weightOneVanishes : UniquenessCondition
  weightTwoFirstProductIsGriess : UniquenessCondition

data UniquenessRoute : Set where
  selfDualRoute : UniquenessRoute
  dimensionBoundRoute : UniquenessRoute

routeRequires : UniquenessRoute → UniquenessCondition → Bool
routeRequires selfDualRoute selfDualAndC2Cofinite = true
routeRequires selfDualRoute dimensionBoundFromWeightThree = false
routeRequires selfDualRoute centralChargeTwentyFour = true
routeRequires selfDualRoute weightOneVanishes = true
routeRequires selfDualRoute weightTwoFirstProductIsGriess = true
routeRequires dimensionBoundRoute selfDualAndC2Cofinite = false
routeRequires dimensionBoundRoute dimensionBoundFromWeightThree = true
routeRequires dimensionBoundRoute centralChargeTwentyFour = true
routeRequires dimensionBoundRoute weightOneVanishes = true
routeRequires dimensionBoundRoute weightTwoFirstProductIsGriess = true

selfDualRouteRequiresC2 :
  routeRequires selfDualRoute selfDualAndC2Cofinite ≡ true
selfDualRouteRequiresC2 = refl

dimensionRouteRequiresHigherWeightBound :
  routeRequires dimensionBoundRoute dimensionBoundFromWeightThree ≡ true
dimensionRouteRequiresHigherWeightBound = refl

bothRoutesRequireGriessWeightTwo :
  routeRequires selfDualRoute weightTwoFirstProductIsGriess
  ≡ routeRequires dimensionBoundRoute weightTwoFirstProductIsGriess
bothRoutesRequireGriessWeightTwo = refl

record GradedTraceAuthorityBoundary : Set where
  constructor gradedTraceAuthorityBoundary
  field
    truncatedIdentityTraceDeterminesVOA : Set
    truncatedIdentityTraceDoesNotDetermineVOA :
      truncatedIdentityTraceDeterminesVOA → Set

    uniquenessConditionsProvedForDASHICarrier : Set
    uniquenessConditionsNotProvedForDASHICarrier :
      uniquenessConditionsProvedForDASHICarrier → Set

canonicalGradedTraceAuthorityBoundary : GradedTraceAuthorityBoundary
canonicalGradedTraceAuthorityBoundary =
  gradedTraceAuthorityBoundary
    ⊥ (λ impossible → ⊥)
    ⊥ (λ impossible → ⊥)
