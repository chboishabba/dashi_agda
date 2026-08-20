module DASHI.Core.RequiredAxisSupportSquareExact where

------------------------------------------------------------------------
-- REQUIRED-AXIS SUPPORT SQUARE
--
-- This module separates two operations that must not be conflated:
--
--   1. evidence may exist somewhere in a derivation / provenance family;
--   2. every axis required by the current query may be positively resolved.
--
-- The support square is not new.  We reuse
-- DASHI.Algebra.DisagreementFourViewBoundary.PolarAssessment, whose coordinates
-- are independent support for P and support for not-P.  The required-axis
-- completeness layer below is a DASHI construction.
--
-- Logical / informational precedent:
--
-- Nuel D. Belnap, "A Useful Four-Valued Logic", in J. Michael Dunn and
-- George Epstein (eds.), Modern Uses of Multiple-Valued Logic, 1977, pp. 5-37.
-- DOI: 10.1007/978-94-010-1161-7_2.
--
-- J. Michael Dunn, "Intuitive Semantics for First-Degree Entailments and
-- 'Coupled Trees'", Philosophical Studies 29(3), 149-168 (1976).
-- DOI: 10.1007/BF00373152.
--
-- These references motivate the independent positive/negative information
-- coordinates only.  They do not imply the required-axis routing discipline,
-- which is formalised here as a repository-local theorem layer.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Algebra.DisagreementFourViewBoundary as Four

SupportSquare : Set
SupportSquare = Four.PolarAssessment

supportSquare : Bool → Bool → SupportSquare
supportSquare = Four.assess

------------------------------------------------------------------------
-- Four informational states remain distinct before any downstream collapse.
------------------------------------------------------------------------

data SupportState : Set where
  positiveOnly negativeOnly conflictingState missingState : SupportState

supportState : SupportSquare → SupportState
supportState (Four.assess true false) = positiveOnly
supportState (Four.assess false true) = negativeOnly
supportState (Four.assess true true) = conflictingState
supportState (Four.assess false false) = missingState

positiveOnlyReceipt :
  supportState (supportSquare true false) ≡ positiveOnly
positiveOnlyReceipt = refl

negativeOnlyReceipt :
  supportState (supportSquare false true) ≡ negativeOnly
negativeOnlyReceipt = refl

conflictingReceipt :
  supportState (supportSquare true true) ≡ conflictingState
conflictingReceipt = refl

missingReceipt :
  supportState (supportSquare false false) ≡ missingState
missingReceipt = refl

conflictingIsNotMissing :
  supportState (supportSquare true true)
  ≡ supportState (supportSquare false false) →
  ⊥
conflictingIsNotMissing ()

ResolvedPositive : SupportSquare → Set
ResolvedPositive square =
  Four.supportsP square ≡ true × Four.supportsNotP square ≡ false

ResolvedNegative : SupportSquare → Set
ResolvedNegative square =
  Four.supportsP square ≡ false × Four.supportsNotP square ≡ true

MissingEvidence : SupportSquare → Set
MissingEvidence square =
  Four.supportsP square ≡ false × Four.supportsNotP square ≡ false

ConflictingEvidence : SupportSquare → Set
ConflictingEvidence square =
  Four.supportsP square ≡ true × Four.supportsNotP square ≡ true

missingCannotBeResolvedPositive :
  ∀ {square} →
  MissingEvidence square →
  ResolvedPositive square →
  ⊥
missingCannotBeResolvedPositive missingEvidence resolved with
  trans (sym (proj₁ missingEvidence)) (proj₁ resolved)
... | ()

missingCannotBeResolvedNegative :
  ∀ {square} →
  MissingEvidence square →
  ResolvedNegative square →
  ⊥
missingCannotBeResolvedNegative missingEvidence resolved with
  trans (sym (proj₂ missingEvidence)) (proj₂ resolved)
... | ()

conflictingCannotBeResolvedPositive :
  ∀ {square} →
  ConflictingEvidence square →
  ResolvedPositive square →
  ⊥
conflictingCannotBeResolvedPositive conflictingEvidence resolved with
  trans (sym (proj₂ resolved)) (proj₂ conflictingEvidence)
... | ()

conflictingCannotBeResolvedNegative :
  ∀ {square} →
  ConflictingEvidence square →
  ResolvedNegative square →
  ⊥
conflictingCannotBeResolvedNegative conflictingEvidence resolved with
  trans (sym (proj₁ resolved)) (proj₁ conflictingEvidence)
... | ()

------------------------------------------------------------------------
-- Required-axis evidence family.
------------------------------------------------------------------------

record AxisEvidenceFamily (Axis : Set) : Set₁ where
  constructor axisEvidenceFamily
  field
    evidenceAt : Axis → SupportSquare
    Required : Axis → Set

open AxisEvidenceFamily public

record RequiredAxesResolved
    {Axis : Set}
    (family : AxisEvidenceFamily Axis) : Set₁ where
  constructor requiredAxesResolved
  field
    resolveRequired :
      (axis : Axis) →
      Required family axis →
      ResolvedPositive (evidenceAt family axis)

open RequiredAxesResolved public

record MissingRequiredAxis
    {Axis : Set}
    (family : AxisEvidenceFamily Axis) : Set₁ where
  constructor missingRequiredAxis
  field
    missingAxisValue : Axis
    missingAxisRequired : Required family missingAxisValue
    missingAxisEvidence : MissingEvidence (evidenceAt family missingAxisValue)

open MissingRequiredAxis public

record ConflictingRequiredAxis
    {Axis : Set}
    (family : AxisEvidenceFamily Axis) : Set₁ where
  constructor conflictingRequiredAxis
  field
    conflictingAxisValue : Axis
    conflictingAxisRequired : Required family conflictingAxisValue
    conflictingAxisEvidence :
      ConflictingEvidence (evidenceAt family conflictingAxisValue)

open ConflictingRequiredAxis public

record PositiveSupportSomewhere
    {Axis : Set}
    (family : AxisEvidenceFamily Axis) : Set₁ where
  constructor positiveSupportSomewhere
  field
    positiveAxisValue : Axis
    positiveSupport :
      Four.supportsP (evidenceAt family positiveAxisValue) ≡ true

open PositiveSupportSomewhere public

missingRequiredAxisBlocksResolution :
  ∀ {Axis}
    {family : AxisEvidenceFamily Axis} →
  MissingRequiredAxis family →
  RequiredAxesResolved family →
  ⊥
missingRequiredAxisBlocksResolution missingAxis resolved =
  missingCannotBeResolvedPositive
    (missingAxisEvidence missingAxis)
    (resolveRequired resolved
      (missingAxisValue missingAxis)
      (missingAxisRequired missingAxis))

conflictingRequiredAxisBlocksResolvedPositive :
  ∀ {Axis}
    {family : AxisEvidenceFamily Axis} →
  ConflictingRequiredAxis family →
  RequiredAxesResolved family →
  ⊥
conflictingRequiredAxisBlocksResolvedPositive conflictAxis resolved =
  conflictingCannotBeResolvedPositive
    (conflictingAxisEvidence conflictAxis)
    (resolveRequired resolved
      (conflictingAxisValue conflictAxis)
      (conflictingAxisRequired conflictAxis))

-- This is the generic non-compensation theorem: even explicit positive evidence
-- somewhere else cannot fill a required axis whose evidence is absent.
positiveSupportOnAnotherAxisCannotFillMissingRequiredAxis :
  ∀ {Axis}
    {family : AxisEvidenceFamily Axis} →
  PositiveSupportSomewhere family →
  MissingRequiredAxis family →
  RequiredAxesResolved family →
  ⊥
positiveSupportOnAnotherAxisCannotFillMissingRequiredAxis
  positive missingAxis resolved =
  missingRequiredAxisBlocksResolution missingAxis resolved

------------------------------------------------------------------------
-- Exact finite witness: strong source evidence, missing downstream evidence.
------------------------------------------------------------------------

data DemoAxis : Set where
  sourceAxis targetAxis : DemoAxis

demoEvidence : DemoAxis → SupportSquare
demoEvidence sourceAxis = supportSquare true false
demoEvidence targetAxis = supportSquare false false

demoRequired : DemoAxis → Set
demoRequired sourceAxis = ⊤
demoRequired targetAxis = ⊤

demoFamily : AxisEvidenceFamily DemoAxis
demoFamily = axisEvidenceFamily demoEvidence demoRequired

demoHasPositiveSupport : PositiveSupportSomewhere demoFamily
demoHasPositiveSupport = positiveSupportSomewhere sourceAxis refl

demoHasMissingRequiredTarget : MissingRequiredAxis demoFamily
demoHasMissingRequiredTarget =
  missingRequiredAxis targetAxis tt (refl , refl)

demoPooledPositiveStillCannotResolveRequiredAxes :
  RequiredAxesResolved demoFamily → ⊥
demoPooledPositiveStillCannotResolveRequiredAxes =
  positiveSupportOnAnotherAxisCannotFillMissingRequiredAxis
    demoHasPositiveSupport
    demoHasMissingRequiredTarget

record RequiredAxisSupportSquareBoundary : Set where
  constructor requiredAxisSupportSquareBoundary
  field
    conflictingEqualsMissing : Bool
    positiveEvidenceSomewhereResolvesEveryRequiredAxis : Bool
    missingRequiredAxisBlocksResolution : Bool
    conflictingRequiredAxisCountsAsResolvedPositive : Bool
    missingCountsAsResolvedNegative : Bool

canonicalRequiredAxisSupportSquareBoundary :
  RequiredAxisSupportSquareBoundary
canonicalRequiredAxisSupportSquareBoundary =
  requiredAxisSupportSquareBoundary false false true false false
