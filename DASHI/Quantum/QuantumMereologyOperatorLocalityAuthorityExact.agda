{-# OPTIONS --safe #-}
module DASHI.Quantum.QuantumMereologyOperatorLocalityAuthorityExact where

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Quantum.QuantumMereologyExact as QM
import DASHI.Quantum.QuantumMereologyInnerProductTPSAuthorityExact as Inner
import DASHI.Quantum.QuantumMereologySourceAtlasExact as Sources

------------------------------------------------------------------------
-- OPERATOR LOCALITY AUTHORITY SOCKET
--
-- Lean owns the concrete tensor-map reconstruction. Agda records only the
-- authority needed by downstream quantum-mereology consumers.
------------------------------------------------------------------------

record OperatorLocalityAuthority
    (W : QM.BareQuantumWorld)
    (T : QM.TensorProductStructure W) : Set₁ where
  field
    innerProductTPSAuthority :
      Inner.InnerProductTPSAuthority W T

    GlobalOperator LocalLeftOperator LocalRightOperator InteractionOperator : Set

    globalOperator : GlobalOperator
    localLeftOperator : LocalLeftOperator
    localRightOperator : LocalRightOperator
    interactionOperator : InteractionOperator

    PullbackDecompositionAuthority : Set
    pullbackDecompositionAuthority :
      PullbackDecompositionAuthority

open OperatorLocalityAuthority public

record OperatorLocalityPromotionBoundary : Set where
  field
    decompositionCreatesSelfAdjointHamiltonian : Bool
    decompositionCreatesSelfAdjointHamiltonianIsFalse :
      decompositionCreatesSelfAdjointHamiltonian ≡ false

    decompositionCreatesSmallInteraction : Bool
    decompositionCreatesSmallInteractionIsFalse :
      decompositionCreatesSmallInteraction ≡ false

    decompositionSelectsPreferredTPS : Bool
    decompositionSelectsPreferredTPSIsFalse :
      decompositionSelectsPreferredTPS ≡ false

    interactionFreeCreatesPhysicalIndependence : Bool
    interactionFreeCreatesPhysicalIndependenceIsFalse :
      interactionFreeCreatesPhysicalIndependence ≡ false

canonicalOperatorLocalityPromotionBoundary :
  OperatorLocalityPromotionBoundary
canonicalOperatorLocalityPromotionBoundary = record
  { decompositionCreatesSelfAdjointHamiltonian = false
  ; decompositionCreatesSelfAdjointHamiltonianIsFalse = refl
  ; decompositionCreatesSmallInteraction = false
  ; decompositionCreatesSmallInteractionIsFalse = refl
  ; decompositionSelectsPreferredTPS = false
  ; decompositionSelectsPreferredTPSIsFalse = refl
  ; interactionFreeCreatesPhysicalIndependence = false
  ; interactionFreeCreatesPhysicalIndependenceIsFalse = refl
  }

leanOperatorLocalitySourceWrittenReceipt : Sources.AttributionReceipt
leanOperatorLocalitySourceWrittenReceipt =
  Sources.attribution-receipt
    Sources.importedFormalTheoremSource
    "DASHI Lean: RequestProject.QuantumMereologyOperatorLocality"
    "Source-written Lean owner for U^-1 A U = A_L tensor I + I tensor A_R + V using mathlib tensor-map operators. This is source lineage only until an exact-head Lean kernel/build receipt exists."

agdaOperatorLocalityAuthoritySocketReceipt : Sources.AttributionReceipt
agdaOperatorLocalityAuthoritySocketReceipt =
  Sources.attribution-receipt
    Sources.crossModuleInference
    "DASHI Agda"
    "Agda exposes only an explicit operator-locality authority socket layered over the inner-product TPS authority; no tensor-map theorem is manufactured locally."
