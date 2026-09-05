module DASHI.Physics.Plasma.MHDConjugateRealPayloadExchangeExact where

open import DASHI.Core.Prelude

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3HermitianAlgebraProgram as Hermitian
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Plasma.MHDProjectedPayloadReductionReuseExact as Projection

------------------------------------------------------------------------
-- CONJUGATE MATCHING IS ENOUGH FOR THE REAL TRANSFER PAYLOAD
--
-- Energy-like transfers consume the real part of a Hermitian tested
-- interaction.  Therefore exchanged complex payloads need only agree up to
-- conjugation.  Requiring literal complex equality would be unnecessarily
-- strong and would fight the natural Hermitian exchange law.
------------------------------------------------------------------------

record ConjugatePayloadExchange
    {r : _}
    (F : C3.RealField r)
    (E : C3.IntegerEmbedding F)
    (I : C3.ModeInverseSquare F E) : Set r where
  constructor conjugate-payload-exchange
  field
    k p : Z3.FourierMode
    testK testP rawKP rawPK : C3.Complex3 F
    testKTransverse : Helical.Transverse E k testK
    testPTransverse : Helical.Transverse E p testP
    unprojectedConjugateMatch :
      Projection.unprojectedPayload testK rawKP
      ≡ C3.complexConjugate
          (Projection.unprojectedPayload testP rawPK)

open ConjugatePayloadExchange public

realProjectedPayloadExchange :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E} →
  (exchange : ConjugatePayloadExchange F E I) →
  Projection.realProjectedPayload E I
    (k exchange) (testK exchange) (rawKP exchange)
  ≡
  Projection.realProjectedPayload E I
    (p exchange) (testP exchange) (rawPK exchange)
realProjectedPayloadExchange {F = F} {E = E} {I = I} exchange =
  trans
    (Projection.realProjectedPayloadReducesOnTransverseTest
      E I (k exchange) (testK exchange) (rawKP exchange)
      (testKTransverse exchange))
    (trans
      (cong C3.complexRealPart
        (unprojectedConjugateMatch exchange))
      (trans
        (Hermitian.complexRealPartConjugateInvariant
          (Projection.unprojectedPayload
            (testP exchange) (rawPK exchange)))
        (sym
          (Projection.realProjectedPayloadReducesOnTransverseTest
            E I (p exchange) (testP exchange) (rawPK exchange)
            (testPTransverse exchange)))))

record ConjugatePayloadBoundary : Set where
  constructor conjugate-payload-boundary
  field
    literalComplexPayloadEqualityIsRequired : Bool
    literalComplexPayloadEqualityIsRequiredIsFalse :
      literalComplexPayloadEqualityIsRequired ≡ false

    conjugatePayloadMatchingIsEnoughForRealTransfer : Bool
    conjugatePayloadMatchingIsEnoughForRealTransferIsTrue :
      conjugatePayloadMatchingIsEnoughForRealTransfer ≡ true

    conjugateMatchingAloneProvesCouplingSkew : Bool
    conjugateMatchingAloneProvesCouplingSkewIsFalse :
      conjugateMatchingAloneProvesCouplingSkew ≡ false

canonicalConjugatePayloadBoundary : ConjugatePayloadBoundary
canonicalConjugatePayloadBoundary =
  conjugate-payload-boundary false refl true refl false refl
