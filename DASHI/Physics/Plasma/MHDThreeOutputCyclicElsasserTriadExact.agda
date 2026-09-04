module DASHI.Physics.Plasma.MHDThreeOutputCyclicElsasserTriadExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Physics.Plasma.MHDEnergyCrossHelicityTriadBidiExact as EC

------------------------------------------------------------------------
-- LITERAL THREE-OUTPUT CYCLIC TRIAD SOCKET
--
-- A conservative triad theorem is not one p,q->k equation.  It must carry the
-- k-, p-, and q-output equations for the same physical triad, together with
-- their cyclic identification and projection/pressure cancellation.
------------------------------------------------------------------------

record ThreeOutputCyclicTriad {r : _} (F : _) : Set₁ where
  constructor three-output-cyclic-triad
  field
    KSlot PSlot QSlot : Set
    kOutput pOutput qOutput : Set
    sameWavevectorTriadAcrossOutputs : Set
    cyclicPermutationKtoP : Set
    cyclicPermutationPtoQ : Set
    cyclicPermutationQtoK : Set
    sameHelicalOrientationConvention : Set
    sameElsasserOrientationConvention : Set
    pressureProjectionCancellation : Set
    triadReference : String

open ThreeOutputCyclicTriad public

record ElsasserCyclicVariationSocket : Set₁ where
  constructor elsasser-cyclic-variation-socket
  field
    Scalar : Set
    zeroScalar : Scalar
    plusK plusP plusQ : Scalar
    minusK minusP minusQ : Scalar
    plusCyclicSum : Scalar
    minusCyclicSum : Scalar
    plusSumRepresentsSameLiteralTriad : Set
    minusSumRepresentsSameLiteralTriad : Set
    pressureProjectionReceipt : Set
    socketReference : String

open ElsasserCyclicVariationSocket public

record ThreeOutputBoundary : Set where
  constructor three-output-boundary
  field
    oneOutputEquationIsConservativeTriad : Bool
    oneOutputEquationIsConservativeTriadIsFalse :
      oneOutputEquationIsConservativeTriad ≡ false

    cyclicPermutationReceiptsAreRequired : Bool
    cyclicPermutationReceiptsAreRequiredIsTrue :
      cyclicPermutationReceiptsAreRequired ≡ true

    projectionCancellationMayBeDropped : Bool
    projectionCancellationMayBeDroppedIsFalse :
      projectionCancellationMayBeDropped ≡ false

canonicalThreeOutputBoundary : ThreeOutputBoundary
canonicalThreeOutputBoundary =
  three-output-boundary false refl true refl false refl
