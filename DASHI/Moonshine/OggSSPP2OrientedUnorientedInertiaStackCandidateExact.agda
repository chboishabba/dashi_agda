module DASHI.Moonshine.OggSSPP2OrientedUnorientedInertiaStackCandidateExact where

------------------------------------------------------------------------
-- p=2 ORIENTATION-DOUBLET x UNORIENTED-INERTIA STACK CANDIDATE
--
-- STANDARD INGREDIENTS
--
--  * Over a geometric point x of an algebraic stack X, the inertia fibre
--    records automorphisms of x; its connected sectors are indexed by
--    conjugacy classes in Aut(x).
--
--  * At the unique characteristic-2 supersingular elliptic-curve point,
--    Aut(E) is binary tetrahedral, and the sourced class table has seven
--    conjugacy classes.
--
--  * DASHI's loop-reversal involution [g] |-> [g^{-1}] quotients those seven
--    inertia sectors to five unoriented sectors.
--
--  * Goren--Love provide the independent two-element oriented quadratic-order
--    doublet, exchanged by Galois.
--
-- DASHI CONSTRUCTION
--
-- Their product is the already formalized ten-state carrier:
--
--   OrientationDoublet x (InertiaConjugacyClasses / loop-reversal).
--
-- This module gives that product a stack-theoretically meaningful description.
-- It does NOT assert that the literature gives this exact product a standard
-- name, nor that its five inertia labels have Base369 axis/diagonal semantics.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)

import DASHI.Moonshine.OggSSPP2BinaryTetrahedralInertiaFiveOrbitExact as Inertia
import DASHI.Moonshine.OggSSPP2OrientedInertiaTenStateRecognitionExact as Ten
import DASHI.Moonshine.OggSSPSmallCharacteristicClassicalSourceAtlasExact as Classical
import DASHI.Moonshine.OggSSPMonstrousExponentSourceAttributionExact as Attribution

------------------------------------------------------------------------
-- 1. Standard inertia interpretation of the seven-class donor.
------------------------------------------------------------------------

data InertiaSectorInterpretation : Set where
  conjugacyClassSector :
    Inertia.BinaryTetrahedralConjugacyClass ->
    InertiaSectorInterpretation

loopReverse :
  Inertia.BinaryTetrahedralConjugacyClass ->
  Inertia.BinaryTetrahedralConjugacyClass
loopReverse =
  Inertia.inverseClass

loopReverseInvolutive :
  (class : Inertia.BinaryTetrahedralConjugacyClass) ->
  loopReverse (loopReverse class) ≡ class
loopReverseInvolutive =
  Inertia.inverseClassInvolutive

UnorientedInertiaSector : Set
UnorientedInertiaSector =
  Inertia.BinaryTetrahedralInversionOrbit

unorientedInertiaQuotient :
  Inertia.BinaryTetrahedralConjugacyClass ->
  UnorientedInertiaSector
unorientedInertiaQuotient =
  Inertia.quotientByInversion

unorientedInertiaQuotientRespectsLoopReversal :
  (class : Inertia.BinaryTetrahedralConjugacyClass) ->
  unorientedInertiaQuotient (loopReverse class)
  ≡
  unorientedInertiaQuotient class
unorientedInertiaQuotientRespectsLoopReversal =
  Inertia.quotientByInversionInvariant

------------------------------------------------------------------------
-- 2. Orientation-doublet x unoriented-inertia fibre.
------------------------------------------------------------------------

P2OrientedUnorientedInertiaState : Set
P2OrientedUnorientedInertiaState =
  Ten.P2OrientedInertiaState

toExistingTenState =
  Ten.toP2CMMarkedState

fromExistingTenState =
  Ten.fromP2CMMarkedState

tenStateRoundTripLeft =
  Ten.orientedInertiaRoundTrip

tenStateRoundTripRight =
  Ten.p2CMRoundTrip

tenStateFullRecognition =
  Ten.orientedInertiaFullRecognition

------------------------------------------------------------------------
-- 3. Interpretation boundary.
------------------------------------------------------------------------

classicalBoundary :
  Classical.SmallCharacteristicClassicalSourcingBoundary
classicalBoundary =
  Classical.canonicalSmallCharacteristicClassicalSourcingBoundary

data ExactProductHasStandardLiteratureName : Set where
data LoopReversalQuotientIsRigidifiedInertiaByDefinition : Set where
data FiveInertiaSectorsHaveNineOrbitSemantics : Set where
data ProductIsGamma04SupersingularFibre : Set where

exactProductNotPromotedToNamedLiteratureObject :
  ExactProductHasStandardLiteratureName -> ⊥
exactProductNotPromotedToNamedLiteratureObject ()

loopReversalQuotientNotSilentlyCalledRigidifiedInertia :
  LoopReversalQuotientIsRigidifiedInertiaByDefinition -> ⊥
loopReversalQuotientNotSilentlyCalledRigidifiedInertia ()

fiveInertiaSectorsDoNotAcquireNineOrbitSemantics :
  FiveInertiaSectorsHaveNineOrbitSemantics -> ⊥
fiveInertiaSectorsDoNotAcquireNineOrbitSemantics ()

productIsNotGamma04SupersingularFibre :
  ProductIsGamma04SupersingularFibre -> ⊥
productIsNotGamma04SupersingularFibre ()

claimOrigin : Attribution.ClaimOrigin
claimOrigin =
  Attribution.repositoryCrossModuleInference

record P2OrientedUnorientedInertiaStackCandidateBoundary : Set where
  constructor p2-oriented-unoriented-inertia-stack-candidate-boundary
  field
    inertiaConjugacyClassInterpretationClassical : Bool
    binaryTetrahedralSevenSectorDonorClassical : Bool
    loopReversalQuotientToFiveConstructed : Bool
    orientationDoubletClassical : Bool
    exactTwoTimesFiveProductConstructed : Bool
    exactRecognitionToDASHITenStatePaid : Bool
    stackShapedInterpretationAvailable : Bool
    exactProductNamedInClassicalLiterature : Bool
    rigidifiedInertiaIdentityClaimed : Bool
    gamma04FibreIdentityClaimed : Bool
    base369SemanticIdentityClaimed : Bool

canonicalP2OrientedUnorientedInertiaStackCandidateBoundary :
  P2OrientedUnorientedInertiaStackCandidateBoundary
canonicalP2OrientedUnorientedInertiaStackCandidateBoundary =
  p2-oriented-unoriented-inertia-stack-candidate-boundary
    true true true true true true true false false false false
