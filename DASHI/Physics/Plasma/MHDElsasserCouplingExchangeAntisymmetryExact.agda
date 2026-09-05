module DASHI.Physics.Plasma.MHDElsasserCouplingExchangeAntisymmetryExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- ELSASSER COUPLING EXCHANGE ANTISYMMETRY
--
-- Source-shaped abstraction of the Fourier-space incompressible-MHD coupling
-- symmetry A_abc(k,p,q) = - A_bac(p,k,q).  The geometry-level exchange law is
-- kept distinct from a full modal-transfer cancellation theorem.
------------------------------------------------------------------------

record ElsasserCouplingExchange : Set₁ where
  constructor elsasser-coupling-exchange
  field
    Mode Polarisation Scalar : Set
    negate : Scalar → Scalar
    coupling :
      Polarisation → Polarisation → Polarisation →
      Mode → Mode → Mode → Scalar
    exchangeAntisymmetry :
      (a b c : Polarisation) (k p q : Mode) →
      coupling a b c k p q ≡ negate (coupling b a c p k q)
    couplingReference : String

open ElsasserCouplingExchange public

record CouplingExchangeBoundary : Set where
  constructor coupling-exchange-boundary
  field
    geometricAntisymmetryAloneProvesModalEnergyTransferCancellation : Bool
    geometricAntisymmetryAloneProvesModalEnergyTransferCancellationIsFalse :
      geometricAntisymmetryAloneProvesModalEnergyTransferCancellation ≡ false

    amplitudesConjugationsAndProjectionStillNeedSameObjectWeld : Bool
    amplitudesConjugationsAndProjectionStillNeedSameObjectWeldIsTrue :
      amplitudesConjugationsAndProjectionStillNeedSameObjectWeld ≡ true

    couplingExchangeLawIsNavierStokesReceipt : Bool
    couplingExchangeLawIsNavierStokesReceiptIsFalse :
      couplingExchangeLawIsNavierStokesReceipt ≡ false

canonicalCouplingExchangeBoundary : CouplingExchangeBoundary
canonicalCouplingExchangeBoundary =
  coupling-exchange-boundary false refl true refl false refl
