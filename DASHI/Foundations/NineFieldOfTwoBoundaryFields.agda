module DASHI.Foundations.NineFieldOfTwoBoundaryFields where

open import DASHI.Core.Prelude
open import DASHI.Algebra.Trit using (Trit)
open import DASHI.Foundations.TwoBoundarySystem
open import DASHI.Foundations.DiachronicFieldZeroToNine

------------------------------------------------------------------------
-- Stage 9 as a family of stage-6/two-boundary contexts
--
-- A nine-field need not be a flat 3 × 3 table.  Contexts may have different
-- carriers and boundary types, so the natural structure is dependent.
------------------------------------------------------------------------

record TwoBoundaryFamily : Set₁ where
  field
    Context  : Set
    systemAt : Context → TwoBoundarySystem

record ContextualState (F : TwoBoundaryFamily) : Set₁ where
  constructor contextualState
  field
    context : TwoBoundaryFamily.Context F
    state :
      TwoBoundarySystem.State
        (TwoBoundaryFamily.systemAt F context)

record ContextualBoundaryPair (F : TwoBoundaryFamily) : Set₁ where
  constructor contextualBoundaries
  field
    context : TwoBoundaryFamily.Context F
    initial :
      TwoBoundarySystem.InitialBoundary
        (TwoBoundaryFamily.systemAt F context)
    final :
      TwoBoundarySystem.FinalBoundary
        (TwoBoundaryFamily.systemAt F context)

------------------------------------------------------------------------
-- Kinds of higher-order contexts already present in the diachronic hierarchy
------------------------------------------------------------------------

data NineContextKind : Set where
  selfHistoryContext      : NineContextKind
  societyFormContext      : NineContextKind
  societyThoughtContext   : NineContextKind
  physicalLawContext      : NineContextKind
  externalCausalityContext : NineContextKind

record NineBoundaryField : Set₁ where
  field
    family : TwoBoundaryFamily

    kindOf :
      TwoBoundaryFamily.Context family →
      NineContextKind

    triadicViewAt :
      TwoBoundaryFamily.Context family →
      Viewpoint →
      TriadicResolution

    sixViewAt :
      TwoBoundaryFamily.Context family →
      Viewpoint →
      SixField

    tensorSignAt :
      TwoBoundaryFamily.Context family →
      Trit

------------------------------------------------------------------------
-- Higher-order coupling
--
-- Distinct two-boundary sectors may be alternatives, independent factors, or
-- coupled systems.  This record does not silently identify direct sums with
-- tensor products; a concrete model must provide its intended coupling law.
------------------------------------------------------------------------

record ContextCoupling
  (F : TwoBoundaryFamily)
  (left right : TwoBoundaryFamily.Context F) : Set₁ where
  field
    CoupledState : Set

    combine :
      TwoBoundarySystem.State (TwoBoundaryFamily.systemAt F left) →
      TwoBoundarySystem.State (TwoBoundaryFamily.systemAt F right) →
      CoupledState

------------------------------------------------------------------------
-- Generalized two-time sectors
------------------------------------------------------------------------

record WeightedBoundarySector
  (F : TwoBoundaryFamily)
  (Coefficient : Set) : Set₁ where
  constructor weightedSector
  field
    context : TwoBoundaryFamily.Context F
    initial :
      TwoBoundarySystem.InitialBoundary
        (TwoBoundaryFamily.systemAt F context)
    final :
      TwoBoundarySystem.FinalBoundary
        (TwoBoundaryFamily.systemAt F context)
    coefficient : Coefficient

-- A list of sectors is only an indexed family of alternatives.  Calling it a
-- coherent quantum superposition additionally requires complex coefficients,
-- amplitude addition, phase, and interference laws from DASHI.Quantum.TSVF.
BoundarySectorFamily :
  (F : TwoBoundaryFamily) →
  Set →
  Set₁
BoundarySectorFamily F Coefficient =
  List (WeightedBoundarySector F Coefficient)

------------------------------------------------------------------------
-- Nested closure preservation at the family level
------------------------------------------------------------------------

record ContextClosure (F : TwoBoundaryFamily) : Set₁ where
  field
    closeContext :
      TwoBoundaryFamily.Context F →
      TwoBoundaryFamily.Context F

    closeContext-idempotent :
      (c : TwoBoundaryFamily.Context F) →
      closeContext (closeContext c) ≡ closeContext c

record PreservesContextClosure
  {F G : TwoBoundaryFamily}
  (CF : ContextClosure F)
  (CG : ContextClosure G) : Set₁ where
  field
    embedContext :
      TwoBoundaryFamily.Context F →
      TwoBoundaryFamily.Context G

    commutesWithClosure :
      (c : TwoBoundaryFamily.Context F) →
      embedContext (ContextClosure.closeContext CF c)
      ≡
      ContextClosure.closeContext CG (embedContext c)

------------------------------------------------------------------------
-- Interpretation boundary
------------------------------------------------------------------------

-- physicalLawContext and externalCausalityContext permit a nine-field to
-- represent sectors not reducible to the focal person's autobiography.  They
-- do not prove that physical laws vary, nor that unrelated causal sectors are
-- quantum-coherent with the diachronic self-model.  Those are separate model
-- choices and promotion obligations.
