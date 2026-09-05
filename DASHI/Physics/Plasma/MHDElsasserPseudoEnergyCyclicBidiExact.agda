module DASHI.Physics.Plasma.MHDElsasserPseudoEnergyCyclicBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Physics.Plasma.MHDElsasserSkewPairCancellationKernelExact as Kernel
import DASHI.Physics.Plasma.MHDThreeOutputCyclicElsasserTriadExact as Cyclic

------------------------------------------------------------------------
-- ELSASSER PSEUDO-ENERGY CYCLIC BIDI
--
-- Source-backed target: the nonlinear ideal-MHD term conserves E+ and E-
-- separately.  This owner does not assume that result from the chart alone.
-- It requires the literal three-output triad to decompose into skew exchange
-- pairs whose signed transfers cancel before norms.
------------------------------------------------------------------------

record SkewExchangeDecomposition : Set₁ where
  constructor skew-exchange-decomposition
  field
    Transfer : Set
    kp pk pq qp qk kq : Transfer
    kpCancelsPk : Set
    pqCancelsQp : Set
    qkCancelsKq : Set
    sameLiteralTriadReceipt : Set
    sameElsasserSpeciesReceipt : Set
    decompositionReference : String

open SkewExchangeDecomposition public

record ElsasserPseudoEnergyBalance : Set₁ where
  constructor elsasser-pseudo-energy-balance
  field
    plusDecomposition : SkewExchangeDecomposition
    minusDecomposition : SkewExchangeDecomposition
    plusCyclicVariationCancels : Set
    minusCyclicVariationCancels : Set
    pressureProjectionCancellation : Set
    sameObjectThreeOutputReceipt : Set
    balanceReference : String

open ElsasserPseudoEnergyBalance public

record ElsasserPseudoEnergyBidiBoundary : Set where
  constructor elsasser-pseudo-energy-bidi-boundary
  field
    couplingAntisymmetryAloneClosesLiteralTriad : Bool
    couplingAntisymmetryAloneClosesLiteralTriadIsFalse :
      couplingAntisymmetryAloneClosesLiteralTriad ≡ false

    skewExchangeDecompositionCanClosePlusMinusBalances : Bool
    skewExchangeDecompositionCanClosePlusMinusBalancesIsTrue :
      skewExchangeDecompositionCanClosePlusMinusBalances ≡ true

    plusBalanceImpliesMinusBalance : Bool
    plusBalanceImpliesMinusBalanceIsFalse :
      plusBalanceImpliesMinusBalance ≡ false

    cancellationMustOccurBeforeNormMajorisation : Bool
    cancellationMustOccurBeforeNormMajorisationIsTrue :
      cancellationMustOccurBeforeNormMajorisation ≡ true

canonicalElsasserPseudoEnergyBidiBoundary : ElsasserPseudoEnergyBidiBoundary
canonicalElsasserPseudoEnergyBidiBoundary =
  elsasser-pseudo-energy-bidi-boundary false refl true refl false refl true refl
