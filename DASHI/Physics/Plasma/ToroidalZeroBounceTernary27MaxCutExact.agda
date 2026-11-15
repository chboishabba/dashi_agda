module DASHI.Physics.Plasma.ToroidalZeroBounceTernary27MaxCutExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Physics.Plasma.ToroidalZeroBounceAdmissibleSearchMaxCutExact as Prior
import DASHI.Physics.Plasma.Ternary27SpectralGeometryCarrierExact as Carrier
import DASHI.Physics.Plasma.ToroidalZeroBounceTernary27ConeSearchExact as Search27
import DASHI.Physics.Plasma.ZeroBouncePopulationExact as ZeroBounce

------------------------------------------------------------------------
-- TERNARY-27 SEARCH-SPACE EXPANSION MAX-CUT
--
-- Expand the numerical/design chart before imposing semantics, then compress
-- by the repo-native admissible-cone programme.  This is the carrier/function-
-- space lesson only: broad coordinate availability is not physical freedom.
------------------------------------------------------------------------

record Ternary27SearchMaxCut
    (population : ZeroBounce.DeclaredParticlePopulation) : Set₁ where
  constructor ternary27-search-max-cut
  field
    priorPhysicsMaxCut : Prior.AdmissibleSearchMaxCut population
    expandedSearch : Search27.Ternary27ConeSearch population
    literalTwentySevenSiteCarrierReceipt : Set
    explicitPhysicalRealizationReceipt : Set
    hardConstraintCompressionReceipt : Set
    c3nSymmetryCompressionReceipt : Set
    continuationPatchReceipt : Set
    paretoFrontierReceipt : Set
    coilAndOrbitVerificationStillDownstreamReceipt : Set
    maxCutReference : String

open Ternary27SearchMaxCut public

record Ternary27SearchMaxCutBoundary : Set where
  constructor ternary27-search-max-cut-boundary
  field
    broadAmbientChartWeakensHardPhysics : Bool
    broadAmbientChartWeakensHardPhysicsIsFalse :
      broadAmbientChartWeakensHardPhysics ≡ false

    carrierFunctionSpaceDistinctionIsPreserved : Bool
    carrierFunctionSpaceDistinctionIsPreservedIsTrue :
      carrierFunctionSpaceDistinctionIsPreserved ≡ true

    exceptionalAlgebraSemanticsAreImportedIntoPlasma : Bool
    exceptionalAlgebraSemanticsAreImportedIntoPlasmaIsFalse :
      exceptionalAlgebraSemanticsAreImportedIntoPlasma ≡ false

    largerAmbientSearchCanStillBeLowerDimensionalAfterConstraints : Bool
    largerAmbientSearchCanStillBeLowerDimensionalAfterConstraintsIsTrue :
      largerAmbientSearchCanStillBeLowerDimensionalAfterConstraints ≡ true

canonicalTernary27SearchMaxCutBoundary : Ternary27SearchMaxCutBoundary
canonicalTernary27SearchMaxCutBoundary =
  ternary27-search-max-cut-boundary
    false refl
    true refl
    false refl
    true refl

maxCutReference : String
maxCutReference =
  "T3^3 supplies 27 typed search sites; physical realization + admissible cone + C_(3^n) quotient determine the surviving magnet-geometry degrees of freedom."
