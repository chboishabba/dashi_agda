module DASHI.Environment.GlyphosateSauerkrautGenericBidiBridgeExact where

open import DASHI.Core.Prelude

import DASHI.Core.BidiResidualApproximationExact as Bidi
import DASHI.Environment.GlyphosateSauerkrautBioremediationBidiExact as Kraut
import DASHI.Environment.GlyphosateSauerkrautResidualRefinementExact as Residual

------------------------------------------------------------------------
-- The glyphosate Nat interval is an instance of the generic admissible-fibre
-- calculus.  Numeric nesting therefore inherits the generic monotone BIDI
-- semantics rather than owning a separate notion of refinement.
------------------------------------------------------------------------

natEnvelopeFibre : Residual.NatEnvelope → Bidi.ResidualFibre Nat
natEnvelopeFibre envelope value =
  Residual.lower envelope Residual.≤ᴺ value ×
  value Residual.≤ᴺ Residual.upper envelope

natEnvelopeRefinementGivesGenericFibreRefinement :
  {child parent : Residual.NatEnvelope} →
  child Residual.Refines parent →
  Bidi.FibreRefines
    (natEnvelopeFibre child)
    (natEnvelopeFibre parent)
natEnvelopeRefinementGivesGenericFibreRefinement refinement value childMember =
  Residual.≤ᴺ-trans
    (Residual.lowerNarrows refinement)
    (proj₁ childMember)
  ,
  Residual.≤ᴺ-trans
    (proj₂ childMember)
    (Residual.upperNarrows refinement)

shioctonGrossEnvelopeIsGenericResidualFibre :
  Bidi.ResidualFibre Nat
shioctonGrossEnvelopeIsGenericResidualFibre =
  natEnvelopeFibre Residual.shioctonGrossCausalEnvelope

record GlyphosateGenericBidiBoundary : Set where
  constructor glyphosateGenericBidiBoundary
  field
    glyphosateNumericRefinementUsesGenericFibreSemantics : Bool
    glyphosateNumericRefinementUsesGenericFibreSemanticsIsTrue :
      glyphosateNumericRefinementUsesGenericFibreSemantics ≡ true
    narrowerGlyphosateIntervalIsGenericMechanismIdentification : Bool
    narrowerGlyphosateIntervalIsGenericMechanismIdentificationIsFalse :
      narrowerGlyphosateIntervalIsGenericMechanismIdentification ≡ false
    unresolvedKrautResidualsRemainSeparateFromIntervalMembership : Bool
    unresolvedKrautResidualsRemainSeparateFromIntervalMembershipIsTrue :
      unresolvedKrautResidualsRemainSeparateFromIntervalMembership ≡ true

canonicalGlyphosateGenericBidiBoundary : GlyphosateGenericBidiBoundary
canonicalGlyphosateGenericBidiBoundary =
  glyphosateGenericBidiBoundary true refl false refl true refl
