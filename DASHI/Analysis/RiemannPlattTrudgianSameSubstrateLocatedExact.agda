module DASHI.Analysis.RiemannPlattTrudgianSameSubstrateLocatedExact where

------------------------------------------------------------------------
-- EXACT REMAINING PLATT--TRUDGIAN SOURCE WELD
--
-- Published authority:
--   Platt--Trudgian (2021), Theorem 1 verifies all nontrivial zeta zeros
--   through T_PT = 3000175332800 on the critical line (the usual statement is
--   for positive ordinate; conjugation supplies the symmetric reading).
--
-- This module does not turn that publication into a proof term.  It names the
-- exact theorem that must be transported onto DASHI's selected completed-zeta
-- carrier after the concrete ordinate/height geometry has already been fixed.
------------------------------------------------------------------------

open import Agda.Primitive using (Set₁)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.Analysis.RiemannAnalyticSubstrate as Analytic
import DASHI.Analysis.RiemannAnalyticLocatedHeightCarrierRealizationExact as Located
import DASHI.Analysis.RiemannAnalyticLocatedLowCriticalityCompilerExact as Compile
import DASHI.Analysis.RiemannBishopComplexAnalyticCarrierExact as BishopComplex
import DASHI.Analysis.RiemannBishopLocatedHeightCarrierExact as BishopHeight
import DASHI.Analysis.RiemannBishopAnalyticLocatedHeightAttachmentExact as BishopAttachment
import DASHI.Analysis.RiemannLowOrdinateSourceAtlasExact as Source

record PlattTrudgianSameSubstrateLocatedVerification
    {analytic : Analytic.AnalyticSubstrate}
    {functions : BishopComplex.BishopComplexAnalyticFunctionLayer}
    (carrier :
      BishopComplex.CanonicalBishopComplexCarrierRealization analytic functions)
    : Set₁ where
  field
    verifiedLocatedZeroCritical :
      (rho :
        DASHI.Analysis.RiemannAristotleUniversalEvenConeBidiExact.AnalyticNontrivialZero analytic) →
      Located.LocatedVerifiedRegion
        (BishopAttachment.toBishopLocatedHeightAttachment carrier)
        rho →
      DASHI.Analysis.RiemannAristotleUniversalEvenConeBidiExact.analyticCritical rho

    transportReference : String

open PlattTrudgianSameSubstrateLocatedVerification public

compilePublishedLocatedLowCriticality :
  ∀ {analytic functions}
    (carrier :
      BishopComplex.CanonicalBishopComplexCarrierRealization analytic functions) →
  PlattTrudgianSameSubstrateLocatedVerification carrier →
  Compile.PublishedLocatedLowCriticality
    (BishopAttachment.toBishopLocatedHeightAttachment carrier)
compilePublishedLocatedLowCriticality carrier verification = record
  { Compile.verifiedLocatedZeroCritical =
      verifiedLocatedZeroCritical verification
  ; Compile.sourceReference =
      Source.plattTrudgianSourceReference
  ; Compile.sameSubstrateReference =
      transportReference verification
  }

record PlattTrudgianSameSubstrateLocatedBoundary : Set where
  constructor platt-trudgian-same-substrate-located-boundary
  field
    exactHeightGeometryAlreadyConcrete : Bool
    sourceCitationAloneIsProofTerm : Bool
    sameCompletedZetaTransportStillRequired : Bool
    positiveToAbsoluteSymmetryMustBeAccountedFor : Bool
    sameSubstrateLowCriticalityIsSingleRemainingSourceTheorem : Bool
    rhDerivedHere : Bool

open PlattTrudgianSameSubstrateLocatedBoundary public

canonicalPlattTrudgianSameSubstrateLocatedBoundary :
  PlattTrudgianSameSubstrateLocatedBoundary
canonicalPlattTrudgianSameSubstrateLocatedBoundary =
  platt-trudgian-same-substrate-located-boundary
    true false true true true false
