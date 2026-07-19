module DASHI.Foundations.EpistemicGapBoundary where

open import DASHI.Core.Prelude

------------------------------------------------------------------------
-- Evidence states and the boundary against gap-filling promotion
------------------------------------------------------------------------

-- The parameter A is the content carried by positive evidence.
data EvidenceState (A : Set) : Set where
  observed   : A → EvidenceState A
  derived    : A → EvidenceState A
  postulated : EvidenceState A
  unknown    : EvidenceState A

-- Grounded is deliberately indexed by the evidence state.  There are no
-- constructors for postulated or unknown states.
data Grounded {A : Set} : EvidenceState A → Set where
  observedGrounded : (a : A) → Grounded (observed a)
  derivedGrounded  : (a : A) → Grounded (derived a)

unknownIsNotGrounded : {A : Set} → Grounded (unknown {A}) → ⊥
unknownIsNotGrounded ()

postulateIsNotGrounded : {A : Set} → Grounded (postulated {A}) → ⊥
postulateIsNotGrounded ()

------------------------------------------------------------------------
-- Explanatory claims
------------------------------------------------------------------------

record ExplanatoryClaim (Phenomenon Explanation : Set) : Set₁ where
  field
    phenomenon  : Phenomenon
    explanation : Explanation
    evidence    : EvidenceState Explanation

-- Promotion to a warranted causal claim requires a Grounded witness.
record WarrantedClaim (Phenomenon Explanation : Set) : Set₁ where
  field
    claim    : ExplanatoryClaim Phenomenon Explanation
    warrant  : Grounded (ExplanatoryClaim.evidence claim)

promoteObserved :
  {Phenomenon Explanation : Set} →
  (p : Phenomenon) → (e : Explanation) →
  WarrantedClaim Phenomenon Explanation
promoteObserved p e = record
  { claim = record
      { phenomenon = p
      ; explanation = e
      ; evidence = observed e
      }
  ; warrant = observedGrounded e
  }

promoteDerived :
  {Phenomenon Explanation : Set} →
  (p : Phenomenon) → (e : Explanation) →
  WarrantedClaim Phenomenon Explanation
promoteDerived p e = record
  { claim = record
      { phenomenon = p
      ; explanation = e
      ; evidence = derived e
      }
  ; warrant = derivedGrounded e
  }

noUnknownPromotion :
  {Phenomenon Explanation : Set} →
  (c : ExplanatoryClaim Phenomenon Explanation) →
  ExplanatoryClaim.evidence c ≡ unknown →
  Grounded (ExplanatoryClaim.evidence c) →
  ⊥
noUnknownPromotion c refl = unknownIsNotGrounded

noPostulatePromotion :
  {Phenomenon Explanation : Set} →
  (c : ExplanatoryClaim Phenomenon Explanation) →
  ExplanatoryClaim.evidence c ≡ postulated →
  Grounded (ExplanatoryClaim.evidence c) →
  ⊥
noPostulatePromotion c refl = postulateIsNotGrounded

------------------------------------------------------------------------
-- Interpretive meaning remains admissible, but is a different type
------------------------------------------------------------------------

-- A spiritual, existential, mathematical, or Indigenous interpretive frame
-- can organize meaning without pretending to be a causal explanation.
data MeaningMode : Set where
  spiritual relational mathematical existential contemplative : MeaningMode

record InterpretiveFrame (Phenomenon Meaning : Set) : Set₁ where
  field
    phenomenon : Phenomenon
    meaning    : Meaning
    mode       : MeaningMode

-- The separation is constructive: an interpretation does not contain the
-- Grounded witness required by WarrantedClaim.  Any bridge must be supplied
-- explicitly as new evidence, rather than inferred from an epistemic gap.
record InterpretationToExplanation
  (Phenomenon Meaning Explanation : Set) : Set₁ where
  field
    interpret : InterpretiveFrame Phenomenon Meaning
    claim     : ExplanatoryClaim Phenomenon Explanation
    warrant   : Grounded (ExplanatoryClaim.evidence claim)

------------------------------------------------------------------------
-- Open inquiry
------------------------------------------------------------------------

-- Unknowns may generate questions and obligations without generating answers.
record ResearchObligation (Phenomenon : Set) : Set₁ where
  field
    phenomenon : Phenomenon
    openQuestion : Set

unknownGeneratesObligation :
  {Phenomenon Explanation : Set} →
  (p : Phenomenon) →
  EvidenceState Explanation →
  ResearchObligation Phenomenon
unknownGeneratesObligation p unknown = record
  { phenomenon = p
  ; openQuestion = ⊤
  }
unknownGeneratesObligation p _ = record
  { phenomenon = p
  ; openQuestion = ⊥
  }
