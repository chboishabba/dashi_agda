module DASHI.Environment.GlyphosateSauerkrautGenericBidiBridgeExact where

open import DASHI.Core.Prelude

import DASHI.Core.BidiResidualApproximationExact as Bidi
import DASHI.Environment.GlyphosateSauerkrautResidualRefinementExact as Residual

------------------------------------------------------------------------
-- The glyphosate Nat interval instantiates the generic admissible-fibre
-- calculus, so numeric nesting inherits the monotone BIDI semantics.
------------------------------------------------------------------------

natEnvelopeFibre : Residual.NatEnvelope → Bidi.ResidualFibre Nat
natEnvelopeFibre envelope value =
  Residual._≤ᴺ_ (Residual.lower envelope) value ×
  Residual._≤ᴺ_ value (Residual.upper envelope)

natEnvelopeRefinementGivesGenericFibreRefinement :
  {child parent : Residual.NatEnvelope} →
  Residual._Refines_ child parent →
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

shioctonGrossEnvelopeIsGenericResidualFibre : Bidi.ResidualFibre Nat
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
