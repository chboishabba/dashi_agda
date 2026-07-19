module DASHI.Foundations.DiachronicTwoBoundaryBridge where

open import DASHI.Core.Prelude
open import DASHI.Algebra.Trit using (Trit; neg; zer; pos)
open import DASHI.Foundations.TwoBoundarySystem
open import DASHI.Foundations.DiachronicFieldZeroToNine

------------------------------------------------------------------------
-- Non-quantum diachronic instance
--
-- Remembered pasts and anticipated futures jointly constrain a present
-- interpretation.  This is a two-boundary architecture, not a claim that
-- autobiographical interpretation is a Hilbert-space quantum process.
------------------------------------------------------------------------

record RememberedBoundary : Set where
  constructor remembered
  field
    rememberedClaim : IdentityClaim
    rememberedSign  : Trit

record AnticipatedBoundary : Set where
  constructor anticipated
  field
    anticipatedClaim : IdentityClaim
    anticipatedSign  : Trit

record PresentInterpretation : Set where
  constructor interpreted
  field
    viewpoint : Viewpoint
    presentClaim : IdentityClaim
    presentSign  : Trit

-- Compatibility is explicit evidence supplied by an interpretation procedure.
-- We do not force a single universal criterion for every person or context.
data DiachronicCompatibility :
  RememberedBoundary →
  AnticipatedBoundary →
  PresentInterpretation →
  Set where
  situated-compatible :
    {past : RememberedBoundary}
    {future : AnticipatedBoundary}
    {present : PresentInterpretation} →
    DiachronicCompatibility past future present

diachronicSystem : TwoBoundarySystem
diachronicSystem = record
  { State = PresentInterpretation
  ; InitialBoundary = RememberedBoundary
  ; FinalBoundary = AnticipatedBoundary
  ; compatible = DiachronicCompatibility
  }

------------------------------------------------------------------------
-- Oriented propagation into the present
------------------------------------------------------------------------

fromRemembered : RememberedBoundary → PresentInterpretation
fromRemembered (remembered claim sign) =
  interpreted rememberedSelf claim sign

fromAnticipated : AnticipatedBoundary → PresentInterpretation
fromAnticipated (anticipated claim sign) =
  interpreted anticipatedSelf claim sign

diachronicPropagation : TwoBoundaryPropagation diachronicSystem
diachronicPropagation = record
  { forwardFrom = fromRemembered
  ; backwardFrom = fromAnticipated
  }

------------------------------------------------------------------------
-- A typed bridge into the existing stage-6 field
------------------------------------------------------------------------

toSixField :
  RememberedBoundary →
  PresentInterpretation →
  AnticipatedBoundary →
  IdentityClaim →
  SixField
toSixField past present future other =
  sixView
    (RememberedBoundary.rememberedClaim past)
    (PresentInterpretation.presentClaim present)
    (AnticipatedBoundary.anticipatedClaim future)
    other

record DiachronicSixWitness : Set where
  constructor diachronicSix
  field
    past    : RememberedBoundary
    present : PresentInterpretation
    future  : AnticipatedBoundary
    other   : IdentityClaim
    compatibility :
      DiachronicCompatibility past future present

    sixField : SixField
    sixField-correct :
      sixField ≡ toSixField past present future other

------------------------------------------------------------------------
-- Psychological fold
--
-- The fold exchanges remembered and anticipated roles only after an explicit
-- interpretation map translates between their carriers.  Unlike quantum time
-- reversal it carries no antiunitary, amplitude, or unitary-evolution claim.
------------------------------------------------------------------------

record DiachronicFold : Set₁ where
  field
    rememberAsFuture : RememberedBoundary → AnticipatedBoundary
    anticipateAsPast : AnticipatedBoundary → RememberedBoundary

    remembered-roundtrip :
      (x : RememberedBoundary) →
      anticipateAsPast (rememberAsFuture x) ≡ x

    anticipated-roundtrip :
      (x : AnticipatedBoundary) →
      rememberAsFuture (anticipateAsPast x) ≡ x

------------------------------------------------------------------------
-- Example trans-story boundaries
------------------------------------------------------------------------

rememberedUncertainty : RememberedBoundary
rememberedUncertainty = remembered indeterminate zer

anticipatedAffirmation : AnticipatedBoundary
anticipatedAffirmation = anticipated transClaim pos

presentTransInterpretation : PresentInterpretation
presentTransInterpretation = interpreted embodiedSelf transClaim pos

exampleCompatibility :
  DiachronicCompatibility
    rememberedUncertainty
    anticipatedAffirmation
    presentTransInterpretation
exampleCompatibility = situated-compatible

exampleSixField : SixField
exampleSixField =
  toSixField
    rememberedUncertainty
    presentTransInterpretation
    anticipatedAffirmation
    notTransClaim

-- Boundary statement: this example records conditional viewpoints and social
-- tension.  It neither decides another person's identity nor treats negative
-- Trit values as moral valuations of a person.
