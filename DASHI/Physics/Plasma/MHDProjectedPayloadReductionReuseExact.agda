module DASHI.Physics.Plasma.MHDProjectedPayloadReductionReuseExact where

open import DASHI.Core.Prelude

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNLerayAlgebraProgram as LerayFixed
import DASHI.Physics.Closure.NSTriadKNLeraySelfAdjointness as LeraySelfAdjoint

------------------------------------------------------------------------
-- REUSE OF THE LITERAL FOURIER LERAY PROJECTOR
--
-- A tested projected interaction can be reduced to the unprojected Hermitian
-- payload whenever the test mode is transverse.  This is application-neutral
-- Fourier algebra already owned by the repository; MHD still owes the literal
-- identification of its Elsasser test and nonlinear interaction vectors.
------------------------------------------------------------------------

projectedPayload :
  ∀ {r} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F) →
  C3.ModeInverseSquare F E →
  Z3.FourierMode →
  C3.Complex3 F → C3.Complex3 F → C3.Complex F
projectedPayload E I k test value =
  C3.hermitianPairing3 test (C3.lerayProject3 E I k value)

unprojectedPayload :
  ∀ {r} {F : C3.RealField r} →
  C3.Complex3 F → C3.Complex3 F → C3.Complex F
unprojectedPayload = C3.hermitianPairing3

projectedPayloadReducesOnTransverseTest :
  ∀ {r} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F)
    (I : C3.ModeInverseSquare F E)
    (k : Z3.FourierMode)
    (test value : C3.Complex3 F) →
  Helical.Transverse E k test →
  projectedPayload E I k test value
  ≡ unprojectedPayload test value
projectedPayloadReducesOnTransverseTest E I k test value transverseTest =
  trans
    (sym (LeraySelfAdjoint.leraySelfAdjoint E I k test value))
    (cong
      (λ first → C3.hermitianPairing3 first value)
      (LerayFixed.lerayFixesTransverse E I k test transverseTest))

realProjectedPayload :
  ∀ {r} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F) →
  C3.ModeInverseSquare F E →
  Z3.FourierMode →
  C3.Complex3 F → C3.Complex3 F → C3.Complex F
realProjectedPayload E I k test value =
  C3.complexRealPart (projectedPayload E I k test value)

realUnprojectedPayload :
  ∀ {r} {F : C3.RealField r} →
  C3.Complex3 F → C3.Complex3 F → C3.Complex F
realUnprojectedPayload test value =
  C3.complexRealPart (unprojectedPayload test value)

realProjectedPayloadReducesOnTransverseTest :
  ∀ {r} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F)
    (I : C3.ModeInverseSquare F E)
    (k : Z3.FourierMode)
    (test value : C3.Complex3 F) →
  Helical.Transverse E k test →
  realProjectedPayload E I k test value
  ≡ realUnprojectedPayload test value
realProjectedPayloadReducesOnTransverseTest E I k test value transverseTest =
  cong C3.complexRealPart
    (projectedPayloadReducesOnTransverseTest E I k test value transverseTest)

record ProjectedPayloadBoundary : Set where
  constructor projected-payload-boundary
  field
    leraySelfAdjointnessIsReusedRatherThanReproved : Bool
    leraySelfAdjointnessIsReusedRatherThanReprovedIsTrue :
      leraySelfAdjointnessIsReusedRatherThanReproved ≡ true

    transverseTestRemovesOutputProjection : Bool
    transverseTestRemovesOutputProjectionIsTrue :
      transverseTestRemovesOutputProjection ≡ true

    projectionRemovalAloneProvesExchangeSymmetry : Bool
    projectionRemovalAloneProvesExchangeSymmetryIsFalse :
      projectionRemovalAloneProvesExchangeSymmetry ≡ false

canonicalProjectedPayloadBoundary : ProjectedPayloadBoundary
canonicalProjectedPayloadBoundary =
  projected-payload-boundary true refl true refl false refl
