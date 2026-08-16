module DASHI.Physics.Closure.NSTriadKNCanonicalCutoffPhysicalVectorFieldRound62Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Jean Leray.
-- Title: "Sur le mouvement d'un liquide visqueux emplissant l'espace".
-- DOI: 10.1007/BF02547354.
--
-- Author: Roger Temam.
-- Title: "Navier-Stokes Equations: Theory and Numerical Analysis".
-- DOI: 10.1090/chel/343.
--
-- ROUND 62 CONTRIBUTION
--
-- Several older finite-flow ledgers still list construction of the literal
-- physical Galerkin vector field as open.  The mature repository has already
-- closed the two halves separately:
--
--   * Round34 constructs the exact finite physical system from a
--     `CutoffSameObjectDatum`;
--   * Round30's concrete vector-field module constructs every output
--     transverse coefficient from the literal viscous-plus-exhaustive-
--     quadratic formula, once a state-indexed physical system is supplied.
--
-- This file composes those objects directly.  From
--
--   CutoffSameObjectFamily F E
--
-- we construct
--
--   StateIndexedPhysicalGalerkinSystem F E,
--   LiteralPhysicalGalerkinProducer F E,
--   ReconstructedPhysicalState F E -> ReconstructedPhysicalState F E,
--   and the dependent physical-carrier vector field.
--
-- No new coefficient, transversality, reality, or support theorem is assumed.
-- The ONLY remaining input at this composition layer is the actual family of
-- cutoff-compatible same-object data for every state under consideration.
-- The existing Round34 flag correctly records that such a family is not
-- automatically inhabited by the unrestricted raw reconstructed-state carrier.
-- Thus this closes a stale composition seam without hiding the real invariant-
-- state/fixed-cutoff problem.
------------------------------------------------------------------------

open import Agda.Primitive using (Level)
open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNConcreteReconstructedPhysicalSelectorRound29Exact as State
import DASHI.Physics.Closure.NSTriadKNCommutingPhysicalCarrierSelectorRound28Exact as Selector
import DASHI.Physics.Closure.NSTriadKNCanonicalCutoffSameObjectSystemRound34Exact as Canonical
import DASHI.Physics.Closure.NSTriadKNConcretePhysicalGalerkinVectorFieldRound30Exact as Concrete
import DASHI.Physics.Closure.NSTriadKNPhysicalGalerkinVectorFieldRound30Exact as Field

canonicalStateIndexedPhysicalGalerkinSystem :
  ∀ {r} {F : C3.RealField r} {E : C3.IntegerEmbedding F} →
  Canonical.CutoffSameObjectFamily F E →
  Concrete.StateIndexedPhysicalGalerkinSystem F E
canonicalStateIndexedPhysicalGalerkinSystem family = record
  { Concrete.StateIndexedPhysicalGalerkinSystem.physicalSystemAt =
      λ state →
        Canonical.canonicalPhysicalFiniteSystem
          (Canonical.datumAt family state)
  ; Concrete.StateIndexedPhysicalGalerkinSystem.embeddingExact =
      λ state →
        Canonical.canonicalFiniteSystemEmbeddingExact
          (Canonical.datumAt family state)
  }

canonicalLiteralPhysicalGalerkinProducer :
  ∀ {r} {F : C3.RealField r} {E : C3.IntegerEmbedding F} →
  Canonical.CutoffSameObjectFamily F E →
  Field.LiteralPhysicalGalerkinProducer F E
canonicalLiteralPhysicalGalerkinProducer family =
  Concrete.concreteLiteralPhysicalGalerkinProducer
    (canonicalStateIndexedPhysicalGalerkinSystem family)

canonicalConcretePhysicalGalerkinVectorField :
  ∀ {r} {F : C3.RealField r} {E : C3.IntegerEmbedding F} →
  Canonical.CutoffSameObjectFamily F E →
  State.ReconstructedPhysicalState F E →
  State.ReconstructedPhysicalState F E
canonicalConcretePhysicalGalerkinVectorField family =
  Concrete.concretePhysicalGalerkinVectorField
    (canonicalStateIndexedPhysicalGalerkinSystem family)

canonicalDependentPhysicalGalerkinVectorField :
  ∀ {r} {F : C3.RealField r} {E : C3.IntegerEmbedding F} →
  Canonical.CutoffSameObjectFamily F E →
  Selector.PhysicalCarrier (State.reconstructedPhysicalSelectors F E) →
  Selector.PhysicalCarrier (State.reconstructedPhysicalSelectors F E)
canonicalDependentPhysicalGalerkinVectorField family =
  Field.physicalGalerkinDependentVectorField
    (canonicalLiteralPhysicalGalerkinProducer family)

canonicalCutoffFamilyToLiteralProducerClosed : Bool
canonicalCutoffFamilyToLiteralProducerClosed = true

canonicalCutoffFamilyToDependentVectorFieldClosed : Bool
canonicalCutoffFamilyToDependentVectorFieldClosed = true

canonicalCutoffFamilyToLiteralProducerClosedIsTrue :
  canonicalCutoffFamilyToLiteralProducerClosed ≡ true
canonicalCutoffFamilyToLiteralProducerClosedIsTrue = refl

canonicalCutoffFamilyToDependentVectorFieldClosedIsTrue :
  canonicalCutoffFamilyToDependentVectorFieldClosed ≡ true
canonicalCutoffFamilyToDependentVectorFieldClosedIsTrue = refl
