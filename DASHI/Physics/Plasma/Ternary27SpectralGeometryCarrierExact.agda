module DASHI.Physics.Plasma.Ternary27SpectralGeometryCarrierExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Foundations.Base369Ternary27HypervoxelFabricGeometryExact as T27

------------------------------------------------------------------------
-- TERNARY-27 SEARCH CARRIER
--
-- The literal T3^3 carrier supplies exactly 27 coordinate sites.  A search
-- coefficient field is a function from those sites into an application-chosen
-- coefficient type.  Physical semantics are supplied only by an explicit
-- realization map into a surface/field perturbation chart.
------------------------------------------------------------------------

record Ternary27CoefficientField (Coefficient : Set) : Set where
  constructor ternary27-coefficient-field
  field
    coefficientAt : T27.Ternary27Point → Coefficient

open Ternary27CoefficientField public

record Ternary27PhysicalRealization
    (Coefficient PhysicalPerturbation : Set) : Set₁ where
  constructor ternary27-physical-realization
  field
    coefficients : Ternary27CoefficientField Coefficient
    realize : T27.Ternary27Point → Coefficient → PhysicalPerturbation
    superpose : (T27.Ternary27Point → PhysicalPerturbation) → PhysicalPerturbation
    sameSearchChartReceipt : Set
    c3CompatibleSpectralReceipt : Set
    realizationReference : String

open Ternary27PhysicalRealization public

coordinateCount : Nat
coordinateCount = T27.hypervoxelStateCount

coordinateCountIsTwentySeven : coordinateCount ≡ 27
coordinateCountIsTwentySeven = T27.hypervoxelStateCountIs27

record Ternary27CarrierBoundary : Set where
  constructor ternary27-carrier-boundary
  field
    literalCarrierHasTwentySevenSites : Bool
    literalCarrierHasTwentySevenSitesIsTrue :
      literalCarrierHasTwentySevenSites ≡ true

    coefficientFieldRequiresExplicitPhysicalRealization : Bool
    coefficientFieldRequiresExplicitPhysicalRealizationIsTrue :
      coefficientFieldRequiresExplicitPhysicalRealization ≡ true

    ternaryCarrierIsAlbertAlgebraByPlasmaDefinition : Bool
    ternaryCarrierIsAlbertAlgebraByPlasmaDefinitionIsFalse :
      ternaryCarrierIsAlbertAlgebraByPlasmaDefinition ≡ false

    ternaryCarrierIsMagneticFieldByDefinition : Bool
    ternaryCarrierIsMagneticFieldByDefinitionIsFalse :
      ternaryCarrierIsMagneticFieldByDefinition ≡ false

    twentySevenCoordinatesMayIndexBroadSearchBeforeAdmissibility : Bool
    twentySevenCoordinatesMayIndexBroadSearchBeforeAdmissibilityIsTrue :
      twentySevenCoordinatesMayIndexBroadSearchBeforeAdmissibility ≡ true

canonicalTernary27CarrierBoundary : Ternary27CarrierBoundary
canonicalTernary27CarrierBoundary =
  ternary27-carrier-boundary
    true refl
    true refl
    false refl
    false refl
    true refl

carrierReference : String
carrierReference =
  "DASHI.Foundations.Base369Ternary27HypervoxelFabricGeometryExact: literal 27-site carrier reused only as a typed search-coordinate index."
