module DASHI.Physics.Plasma.MHDElsasserThreeOutputSkewDecompositionBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Physics.Plasma.MHDThreeOutputCyclicElsasserTriadExact as Three
import DASHI.Physics.Plasma.MHDElsasserModalTransferSkewWeldBidiExact as Skew
import DASHI.Physics.Plasma.MHDElsasserCouplingExchangeAntisymmetryExact as A

------------------------------------------------------------------------
-- THREE-OUTPUT ELSASSER SKEW DECOMPOSITION
--
-- A literal E^+ or E^- conservation proof must decompose the k,p,q output
-- variations into pairwise exchanged transfers on the same triad.
------------------------------------------------------------------------

data ElsasserSpecies : Set where
  plusSpecies minusSpecies : ElsasserSpecies

record ThreeOutputSkewDecomposition
    (coupling : A.ElsasserCouplingExchange) : Set₁ where
  constructor three-output-skew-decomposition
  field
    cyclicTriad : Three.ThreeOutputCyclicTriad
    species : ElsasserSpecies
    kp pk pq qp qk kq : Skew.ModalTransferSkewWeld coupling
    kVariationDecompositionReceipt : Set
    pVariationDecompositionReceipt : Set
    qVariationDecompositionReceipt : Set
    kpCancelsPk : Set
    pqCancelsQp : Set
    qkCancelsKq : Set
    sameLiteralTriadReceipt : Set
    projectionCancellationReceipt : Set
    decompositionReference : String

open ThreeOutputSkewDecomposition public

record ThreeOutputSkewBoundary : Set where
  constructor three-output-skew-boundary
  field
    threeOutputCarrierAloneProvesSkewDecomposition : Bool
    threeOutputCarrierAloneProvesSkewDecompositionIsFalse :
      threeOutputCarrierAloneProvesSkewDecomposition ≡ false

    pairwiseSkewWithoutSameTriadWeldProvesPseudoEnergyConservation : Bool
    pairwiseSkewWithoutSameTriadWeldProvesPseudoEnergyConservationIsFalse :
      pairwiseSkewWithoutSameTriadWeldProvesPseudoEnergyConservation ≡ false

    plusAndMinusNeedIndependentDecompositions : Bool
    plusAndMinusNeedIndependentDecompositionsIsTrue :
      plusAndMinusNeedIndependentDecompositions ≡ true

canonicalThreeOutputSkewBoundary : ThreeOutputSkewBoundary
canonicalThreeOutputSkewBoundary =
  three-output-skew-boundary false refl false refl true refl
