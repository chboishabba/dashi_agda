module DASHI.Physics.Plasma.MHDHermitianPairPayloadExchangeExact where

open import DASHI.Core.Prelude

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3HermitianAlgebraProgram as Hermitian
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Plasma.MHDProjectedPayloadReductionReuseExact as Projection
import DASHI.Physics.Plasma.MHDConjugateRealPayloadExchangeExact as Exchange

------------------------------------------------------------------------
-- EXACT HERMlTIAN PAYLOAD EXCHANGE
--
-- Once the scalar nonlinear coefficient is factored away, the residual modal
-- payload for an exchanged Elsasser pair can be the Hermitian pairing of the
-- two same-species target modes.  Hermitian conjugate symmetry then gives the
-- exact conjugate match required by the real-transfer exchange theorem.
------------------------------------------------------------------------

pairingExchangeConjugate :
  ∀ {r} {F : C3.RealField r}
    (u v : C3.Complex3 F) →
  C3.hermitianPairing3 u v
  ≡ C3.complexConjugate (C3.hermitianPairing3 v u)
pairingExchangeConjugate u v =
  sym (Hermitian.hermitianPairingConjugateSymmetric v u)

hermitianPairExchange :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (k p : Z3.FourierMode)
    (zk zp : C3.Complex3 F) →
  Helical.Transverse E k zk →
  Helical.Transverse E p zp →
  Exchange.ConjugatePayloadExchange F E I
hermitianPairExchange {F = F} {E = E} {I = I}
  k p zk zp transverseK transverseP =
  Exchange.conjugate-payload-exchange
    k p zk zp zp zk transverseK transverseP
    (pairingExchangeConjugate zk zp)

realProjectedHermitianPairExchange :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (k p : Z3.FourierMode)
    (zk zp : C3.Complex3 F) →
  (transverseK : Helical.Transverse E k zk) →
  (transverseP : Helical.Transverse E p zp) →
  Projection.realProjectedPayload E I k zk zp
  ≡ Projection.realProjectedPayload E I p zp zk
realProjectedHermitianPairExchange
  {F = F} {E = E} {I = I}
  k p zk zp transverseK transverseP =
  Exchange.realProjectedPayloadExchange
    (hermitianPairExchange
      {F = F} {E = E} {I = I}
      k p zk zp transverseK transverseP)

record HermitianPairPayloadBoundary : Set where
  constructor hermitian-pair-payload-boundary
  field
    hermitianConjugateExchangeOwned : Bool
    hermitianConjugateExchangeOwnedIsTrue :
      hermitianConjugateExchangeOwned ≡ true

    transverseProjectedRealPairExchangeOwned : Bool
    transverseProjectedRealPairExchangeOwnedIsTrue :
      transverseProjectedRealPairExchangeOwned ≡ true

    literalMHDNonlinearFactorisationOwnedHere : Bool
    literalMHDNonlinearFactorisationOwnedHereIsFalse :
      literalMHDNonlinearFactorisationOwnedHere ≡ false

canonicalHermitianPairPayloadBoundary : HermitianPairPayloadBoundary
canonicalHermitianPairPayloadBoundary =
  hermitian-pair-payload-boundary true refl true refl false refl
