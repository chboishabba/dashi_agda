module DASHI.Physics.Closure.NSClayOfficialSemanticPromotionBoundaryExact where

------------------------------------------------------------------------
-- OFFICIAL CLAY PROMOTION REQUIRES A CONCRETE SEMANTIC REALIZATION
--
-- NSClayLiteralABCDExact intentionally defines reusable proposition schemas over
-- supplied carriers.  A theorem of one such schema is a theorem of THAT model.
-- It is not, by type alone, a theorem about Fefferman's concrete R^3/T^3 PDE
-- semantics.
--
-- This owner makes the missing promotion coordinate explicit and fail-closed:
--
--   model-level AnyOneClayResolution
--     + checked official semantic realization of the SAME instance
--     -> OfficialAnyOneClayResolution.
--
-- There is deliberately no constructor for OfficialSemanticRealization yet.
-- A future owner may add one only after the concrete continuum function spaces,
-- smoothness/decay/periodicity predicates and exact Navier--Stokes equations are
-- represented and welded to the schema carriers.
--
-- This blocks vacuous choices such as GlobalVelocityD = bottom from being
-- mistaken for a Clay proof while preserving every generic theorem compiler.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Closure.NSClayLiteralABCDExact as Literal

data OfficialSemanticRealization
    (instance : Literal.LiteralClayABCDInstance) : Set where

record OfficialAnyOneClayResolution : Set₂ where
  constructor official-any-one-clay-resolution
  field
    instance : Literal.LiteralClayABCDInstance
    officialSemantics : OfficialSemanticRealization instance
    resolution : Literal.AnyOneClayResolution instance

open OfficialAnyOneClayResolution public

record OfficialFourAlternativeCompletion : Set₂ where
  constructor official-four-alternative-completion
  field
    instance4 : Literal.LiteralClayABCDInstance
    officialSemantics4 : OfficialSemanticRealization instance4
    completion4 : Literal.LiteralFourAlternativeCompletion instance4

open OfficialFourAlternativeCompletion public

officialAllFourImpliesOfficialAnyOne :
  OfficialFourAlternativeCompletion → OfficialAnyOneClayResolution
officialAllFourImpliesOfficialAnyOne C =
  official-any-one-clay-resolution
    (instance4 C)
    (officialSemantics4 C)
    (Literal.literalAllFourImpliesAnyOne (completion4 C))

modelResolutionAlonePromotesOfficialClay : Bool
modelResolutionAlonePromotesOfficialClay = false

officialSemanticRealizationConstructed : Bool
officialSemanticRealizationConstructed = false

releasedLeanReceiptConstructsAgdaSemanticRealization : Bool
releasedLeanReceiptConstructsAgdaSemanticRealization = false

officialPromotionBoundaryFailClosed : Bool
officialPromotionBoundaryFailClosed = true

modelResolutionAlonePromotesOfficialClayIsFalse :
  modelResolutionAlonePromotesOfficialClay ≡ false
modelResolutionAlonePromotesOfficialClayIsFalse = refl

officialSemanticRealizationConstructedIsFalse :
  officialSemanticRealizationConstructed ≡ false
officialSemanticRealizationConstructedIsFalse = refl

officialPromotionBoundaryFailClosedIsTrue :
  officialPromotionBoundaryFailClosed ≡ true
officialPromotionBoundaryFailClosedIsTrue = refl
