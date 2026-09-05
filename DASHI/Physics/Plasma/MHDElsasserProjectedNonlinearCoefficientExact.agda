module DASHI.Physics.Plasma.MHDElsasserProjectedNonlinearCoefficientExact where

open import DASHI.Core.Prelude
open import Relation.Binary.PropositionalEquality using (cong; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3FieldAlgebra as Algebra
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNComplex3OrderedRealityCancellation as Ordered

------------------------------------------------------------------------
-- LITERAL PERIODIC FOURIER ELSASSER INTERACTION
--
-- For one ordered triad contribution, with transport = z^{-alpha}_p and
-- target = z^{alpha}_q,
--
--   N_k = -i P_k [ (transport_p . q) target_q ].
--
-- The tested real transfer against transverse target_k reduces exactly to
--
--   Re[-i (transport_p . q) <target_k,target_q>].
--
-- This owner is concrete C3 Fourier algebra.  It does not identify this object
-- with a particular PDE discretisation without a separate same-object weld.
------------------------------------------------------------------------

elsasserOrderedInteraction :
  ∀ {r} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F)
    (I : C3.ModeInverseSquare F E)
    (k q : Z3.FourierMode)
    (transportP targetQ : C3.Complex3 F) →
  C3.Complex3 F
elsasserOrderedInteraction {F = F} E I k q transportP targetQ =
  C3.complex3Scale
    (Ordered.minusI F)
    (C3.lerayProject3 E I k
      (C3.complex3Scale
        (C3.bilinearDot3 transportP (C3.modeVector E q))
        targetQ))

testedElsasserOrderedTransfer :
  ∀ {r} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F)
    (I : C3.ModeInverseSquare F E)
    (k q : Z3.FourierMode)
    (transportP targetQ targetK : C3.Complex3 F) →
  C3.Complex F
testedElsasserOrderedTransfer E I k q transportP targetQ targetK =
  C3.complexRealPart
    (C3.hermitianPairing3 targetK
      (elsasserOrderedInteraction E I k q transportP targetQ))

elsasserOrderedTransferNormalForm :
  ∀ {r} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F)
    (I : C3.ModeInverseSquare F E)
    (k q : Z3.FourierMode)
    (transportP targetQ targetK : C3.Complex3 F) →
  Helical.Transverse E k targetK →
  testedElsasserOrderedTransfer E I k q transportP targetQ targetK
  ≡
  C3.complexRealPart
    (C3.complexMultiply
      (Ordered.minusI F)
      (C3.complexMultiply
        (C3.bilinearDot3 transportP (C3.modeVector E q))
        (C3.hermitianPairing3 targetK targetQ)))
elsasserOrderedTransferNormalForm {F = F}
  E I k q transportP targetQ targetK transverseK =
  cong C3.complexRealPart
    (trans
      (Algebra.hermitianScaleRight
        targetK
        (C3.lerayProject3 E I k
          (C3.complex3Scale waveFactor targetQ))
        (Ordered.minusI F))
      (cong (C3.complexMultiply (Ordered.minusI F))
        (trans
          (Algebra.removeLerayFromTransverseTest
            E I k targetK
            (C3.complex3Scale waveFactor targetQ)
            transverseK)
          (Algebra.hermitianScaleRight
            targetK targetQ waveFactor))))
  where
  waveFactor = C3.bilinearDot3 transportP (C3.modeVector E q)

record ProjectedElsasserBoundary : Set where
  constructor projected-elsasser-boundary
  field
    literalProjectedInteractionOwned : Bool
    literalProjectedInteractionOwnedIsTrue :
      literalProjectedInteractionOwned ≡ true

    testedNormalFormReductionOwned : Bool
    testedNormalFormReductionOwnedIsTrue :
      testedNormalFormReductionOwned ≡ true

    pdeSameObjectIdentificationOwnedHere : Bool
    pdeSameObjectIdentificationOwnedHereIsFalse :
      pdeSameObjectIdentificationOwnedHere ≡ false

canonicalProjectedElsasserBoundary : ProjectedElsasserBoundary
canonicalProjectedElsasserBoundary =
  projected-elsasser-boundary true refl true refl false refl
