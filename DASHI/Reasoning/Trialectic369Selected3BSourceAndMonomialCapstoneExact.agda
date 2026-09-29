module DASHI.Reasoning.Trialectic369Selected3BSourceAndMonomialCapstoneExact where

------------------------------------------------------------------------
-- THE TWO DISTINCT REMAINING SELECTED-3B PAYMENTS
--
-- 1. MANDATORY: source-native linear same-object action intertwining.
--    Compile it by comparing action images after an injective inclusion
--    into the existing literal full weight-two grade.
--
-- 2. OPTIONAL: a scalar-aware monomial basis of the same linear route.
--    This is not the pure Fin90-permutation action excluded by the
--    source-paid Suzuki central character.
--
-- The canonical linear completion is independent of (2). No constructor
-- in this module assumes that either external/source witness exists.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Data.Empty using (⊥)

import DASHI.Reasoning.Trialectic369CanonicalSelected3BLinearCoreExact as Core
import DASHI.Reasoning.Trialectic369Selected3BActionViaFaithfulInclusionExact as Comparison
import DASHI.Reasoning.Trialectic369MonomialMultiplicityBasisSpecialisationExact as Monomial
import DASHI.Reasoning.Trialectic369MonomialTenByNineTransportExact as TenByNine
import DASHI.Wikimedia.IbrahimMonster3BMultiplicityBasisLinearWrongTypeCorrectionExact as WrongType
import DASHI.Geometry.HilbertLorentzForcing as Linear

-- The actual source-action comparison pays the canonical mandatory route.
canonicalCompletionFromFaithfulGradeTwoComparison :
  ∀ {Monster K}
    (core : Core.CanonicalSelected3BLinearCore {Monster} {K}) →
  Comparison.FaithfulConstituentActionComparison core →
  Core.CanonicalSelected3BLinearCompletion {Monster} {K}
canonicalCompletionFromFaithfulGradeTwoComparison core receipt =
  record
    { core = core
    ; actionIntertwining =
        Comparison.compileActionIntertwiningFromInclusion core receipt
    }

-- On the SAME core, an optional monomial witness reuses the canonical
-- linear route; it never alters or reconstructs that route.
record SameCoreMonomialSpecialisation
    {Monster K : Set}
    (core : Core.CanonicalSelected3BLinearCore {Monster} {K})
    : Setω where
  field
    receipt :
      Monomial.FullMonomialBasisReceipt
        (Core.canonicalLinearRoute core)

open SameCoreMonomialSpecialisation public

compiledMonomialAction :
  ∀ {Monster K}
    (core : Core.CanonicalSelected3BLinearCore {Monster} {K}) →
  SameCoreMonomialSpecialisation core →
  Monomial.MonomialMultiplicityBasisSpecialisation
    (Core.canonicalLinearRoute core)
compiledMonomialAction core specialisation =
  Monomial.monomial (receipt specialisation)

-- Transport the OPTIONAL monomial action through the existing 10x9 codec.
-- Both the index and the scalar are retained on the SAME route.
compiledTenByNineIndexAction :
  ∀ {Monster K}
    (core : Core.CanonicalSelected3BLinearCore {Monster} {K}) →
  SameCoreMonomialSpecialisation core →
  Monomial.RouteGroup (Core.canonicalLinearRoute core) →
  TenByNine.TenByNine →
  TenByNine.TenByNine
compiledTenByNineIndexAction core specialisation =
  TenByNine.indexActionOnTenByNine
    (Core.canonicalLinearRoute core)
    (compiledMonomialAction core specialisation)

compiledTenByNineScalarAction :
  ∀ {Monster K}
    (core : Core.CanonicalSelected3BLinearCore {Monster} {K}) →
  SameCoreMonomialSpecialisation core →
  Monomial.RouteGroup (Core.canonicalLinearRoute core) →
  TenByNine.TenByNine →
  Linear.Scalar
    (WrongType.linearCarrier
      (WrongType.linearRepresentation
        (Core.canonicalLinearRoute core)))
compiledTenByNineScalarAction core specialisation =
  TenByNine.scalarOnTenByNine
    (Core.canonicalLinearRoute core)
    (compiledMonomialAction core specialisation)

-- Scalar-triviality is an ADDITIONAL receipt; only then can one reach
-- the older Fin90 basis-permutation compiler.
optionalPurePermutationFromMonomial :
  ∀ {Monster K}
    (core : Core.CanonicalSelected3BLinearCore {Monster} {K})
    (specialisation : SameCoreMonomialSpecialisation core) →
  Monomial.ScalarTrivialOnBasis
    (Core.canonicalLinearRoute core)
    (compiledMonomialAction core specialisation) →
  WrongType.PermutationBasisSpecialisation
    (WrongType.linearRepresentation
      (Core.canonicalLinearRoute core))
optionalPurePermutationFromMonomial core specialisation trivial =
  Monomial.purePermutationFromTrivialScalars
    (Core.canonicalLinearRoute core)
    (compiledMonomialAction core specialisation)
    trivial

-- Genuine source-action failure blocks the mandatory canonical completion.
sourceCounterexampleRejectsCanonicalCompletion :
  ∀ {Monster K}
    (core : Core.CanonicalSelected3BLinearCore {Monster} {K}) →
  Comparison.IncludedActionCounterexample core →
  Core.CanonicalSelected3BActionIntertwining core →
  ⊥
sourceCounterexampleRejectsCanonicalCompletion =
  Comparison.counterexampleRejectsActionIntertwining

record Boundary : Set where
  constructor boundary
  field
    canonicalLinearCompletionCompilerOwned : Bool
    fullGradeTwoInjectivityAndComparisonStillRequired : Bool
    optionalMonomialActionTracksScalars : Bool
    optionalMonomialRouteSharesCanonicalLinearCore : Bool
    monomialTenByNineRetainsScalars : Bool
    purePermutationRequiresScalarTriviality : Bool
    purePermutationNotInferredFromCharacter : Bool
    actualSourceActionPaidHere : Bool
    actualMonomialBasisPaidHere : Bool

canonicalBoundary : Boundary
canonicalBoundary =
  boundary true true true true true true true false false
