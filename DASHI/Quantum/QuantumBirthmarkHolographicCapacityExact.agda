{-# OPTIONS --safe #-}
module DASHI.Quantum.QuantumBirthmarkHolographicCapacityExact where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Data.Nat using (_*_)

import DASHI.Algebra.Quantum.UVFiniteness as UV
import DASHI.Algebra.Quantum.UVFinitenessHolographyTests as HoloUV
import DASHI.Algebra.Quantum.UVFinitenessHolographyInstance as HoloInstance
import DASHI.Physics.Holography.AreaLaw as AreaLaw
import DASHI.Quantum.AgreementDepth as AgreementDepth

------------------------------------------------------------------------
-- HOLOGRAPHIC AREA CAPACITY -> UV FINITENESS
--
-- The repo has TWO related but non-identical area-capacity owners:
--
--   1. UVFinitenessHolographyTests:
--        dimH(l) <= eta * area(l)
--      implies a UVFinite bounded-dimension bundle.
--
--   2. Physics.Holography.AreaLaw:
--        admCount(r) <= K ^ area(r)
--      is itself the minimal holographic area-law / UV-finiteness interface.
--
-- A concrete UVFinitenessHolographyInstance exists for both surfaces.  This
-- file reuses them exactly and keeps the two notions distinct.  Neither one
-- computes von-Neumann entropy, birthmark amplitude, residual-information
-- density, or gravitational curvature.
------------------------------------------------------------------------

areaBoundImpliesUVFinite :
  (A : HoloUV.UVFinitenessAxioms) →
  (areaBound : HoloUV.AreaBound A) →
  UV.UVFinite
    (record
      { L = HoloUV.L A
      ; dimH = HoloUV.dimH A
      ; bound = λ l → HoloUV.eta A * HoloUV.area A l
      ; dimH≤bound = areaBound
      })
areaBoundImpliesUVFinite = HoloUV.UVFinitenessTheorem

canonicalAreaLawUVInstance : AreaLaw.UVFinite HoloInstance.areaRegion
canonicalAreaLawUVInstance = HoloInstance.areaLawUV

agreementDepthUVFinite :
  (bundle : AgreementDepth.AgreementDepthBundle) →
  UV.UVFinite (AgreementDepth.AgreementDepthBundle.uv-bounded bundle)
agreementDepthUVFinite = AgreementDepth.AgreementDepth-theorem

------------------------------------------------------------------------
-- AgreementDepth audit.
--
-- `AgreementDepthBundle` carries both an area-bound on `uv-axioms` and a
-- separately supplied `uv-bounded`.  `AgreementDepth-theorem` calls generic
-- `uvFiniteness` on the latter.  Therefore the theorem is real UV-finiteness,
-- but it does not prove that the supplied UVBounded object is the one generated
-- by the holographic area-bound.  That same-object capacity weld remains open.
------------------------------------------------------------------------

record AgreementDepthCapacityBoundary : Set where
  constructor agreementDepthCapacityBoundary
  field
    agreementDepthTheoremOwned : Bool
    bundleCarriesHolographicAreaBound : Bool
    bundleCarriesSeparateUVBoundedObject : Bool
    theoremUsesSuppliedUVBoundedObject : Bool
    agreementDepthDoesNotWeldAreaBoundToUVBounded : Bool

canonicalAgreementDepthCapacityBoundary : AgreementDepthCapacityBoundary
canonicalAgreementDepthCapacityBoundary =
  agreementDepthCapacityBoundary true true true true true

record HolographicCapacityBoundary : Set where
  constructor holographicCapacityBoundary
  field
    suppliedAreaBoundImpliesUVFinite : Bool
    areaBoundConstrainsEffectiveHilbertDimension : Bool
    exponentialAdmissibleCountAreaLawOwned : Bool
    concreteAreaLawUVInstanceOwned : Bool
    linearDimensionBoundIsNotExponentialCountBoundByDefinition : Bool
    areaCapacityDoesNotDetermineBoundaryEntropy : Bool
    areaCapacityDoesNotDetermineBirthmarkValue : Bool
    areaCapacityDoesNotDetermineResidualInformationDensity : Bool
    areaCapacityDoesNotDetermineCurvature : Bool

canonicalHolographicCapacityBoundary : HolographicCapacityBoundary
canonicalHolographicCapacityBoundary =
  holographicCapacityBoundary true true true true true true true true true

agreementDepthDoesNotWeldAreaBoundToUVBounded : Bool
agreementDepthDoesNotWeldAreaBoundToUVBounded = true

areaCapacityDoesNotDetermineBirthmarkValue : Bool
areaCapacityDoesNotDetermineBirthmarkValue = true

areaCapacityDoesNotDetermineResidualInformationDensity : Bool
areaCapacityDoesNotDetermineResidualInformationDensity = true
