module DASHI.Physics.Plasma.MHDElsasserOrderedRealityPairCancellationExact where

open import DASHI.Core.Prelude
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadOrbitConstruction as Orbit
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3FieldAlgebra as Algebra
import DASHI.Physics.Closure.NSTriadKNComplex3RealityPhaseAudit as Audit
import DASHI.Physics.Closure.NSTriadKNComplex3OrderedRealityCancellation as Ordered

------------------------------------------------------------------------
-- TWO-FIELD ELSASSER ORDERED-PAIR CANCELLATION
--
-- The NS proof separates into a derivative-factor statement about the
-- divergence-free transport field and a Hermitian/reality statement about the
-- target field.  Therefore the same exact Fourier algebra applies with
-- transport = z^{-alpha} and target = z^{alpha}.
------------------------------------------------------------------------

elsasserOrderedNormalForm :
  ∀ {r} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F) →
  Physical.PhysicalTriadIncidence →
  (Z3.FourierMode → C3.Complex3 F) →
  (Z3.FourierMode → C3.Complex3 F) →
  C3.Complex F
elsasserOrderedNormalForm {F = F} E tau transport target =
  C3.complexRealPart
    (C3.complexMultiply
      (Ordered.minusI F)
      (C3.complexMultiply
        (C3.bilinearDot3
          (transport (Physical.p tau))
          (C3.modeVector E (Physical.q tau)))
        (C3.hermitianPairing3
          (target (Physical.k tau))
          (target (Physical.q tau)))))

elsasserMateWaveFactorIsNegative :
  ∀ {r} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F)
    (tau : Physical.PhysicalTriadIncidence)
    (transport : Z3.FourierMode → C3.Complex3 F) →
  Audit.DivergenceFreeCondition E transport →
  C3.bilinearDot3
    (transport (Physical.p (Orbit.orderedRealityMate tau)))
    (C3.modeVector E (Physical.q (Orbit.orderedRealityMate tau)))
  ≡
  C3.complexNegate
    (C3.bilinearDot3
      (transport (Physical.p tau))
      (C3.modeVector E (Physical.q tau)))
elsasserMateWaveFactorIsNegative = Ordered.mateWaveFactorIsNegative

elsasserMatePairingEqualsBasePairing :
  ∀ {r} {F : C3.RealField r}
    (tau : Physical.PhysicalTriadIncidence)
    (target : Z3.FourierMode → C3.Complex3 F) →
  Audit.RealityCondition target →
  C3.hermitianPairing3
    (target (Physical.k (Orbit.orderedRealityMate tau)))
    (target (Physical.q (Orbit.orderedRealityMate tau)))
  ≡
  C3.hermitianPairing3
    (target (Physical.k tau))
    (target (Physical.q tau))
elsasserMatePairingEqualsBasePairing = Ordered.matePairingEqualsBasePairing

elsasserOrderedRealityPairCancellation :
  ∀ {r} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F)
    (tau : Physical.PhysicalTriadIncidence)
    (transport target : Z3.FourierMode → C3.Complex3 F) →
  Audit.DivergenceFreeCondition E transport →
  Audit.RealityCondition target →
  C3.complexAdd
    (elsasserOrderedNormalForm E tau transport target)
    (elsasserOrderedNormalForm E
      (Orbit.orderedRealityMate tau) transport target)
  ≡ C3.complexZero F
elsasserOrderedRealityPairCancellation {F = F}
  E tau transport target transportDivergenceFree targetReality =
  trans
    (cong
      (C3.complexAdd (elsasserOrderedNormalForm E tau transport target))
      (cong C3.complexRealPart
        (cong (C3.complexMultiply (Ordered.minusI F))
          (trans
            (cong₂ C3.complexMultiply
              (elsasserMateWaveFactorIsNegative
                E tau transport transportDivergenceFree)
              (elsasserMatePairingEqualsBasePairing
                tau target targetReality))
            (Algebra.complexNegateMultiplyLeft baseWave basePair)))))
    (Ordered.realMinusITwoTermCancellation baseProduct)
  where
  baseWave =
    C3.bilinearDot3
      (transport (Physical.p tau))
      (C3.modeVector E (Physical.q tau))
  basePair =
    C3.hermitianPairing3
      (target (Physical.k tau))
      (target (Physical.q tau))
  baseProduct = C3.complexMultiply baseWave basePair

record ElsasserOrderedRealityBoundary : Set where
  constructor elsasser-ordered-reality-boundary
  field
    transportAndTargetMustBeSameField : Bool
    transportAndTargetMustBeSameFieldIsFalse :
      transportAndTargetMustBeSameField ≡ false

    transportDivergenceFreeIsRequired : Bool
    transportDivergenceFreeIsRequiredIsTrue :
      transportDivergenceFreeIsRequired ≡ true

    targetRealityIsRequired : Bool
    targetRealityIsRequiredIsTrue : targetRealityIsRequired ≡ true

    twoFieldOrderedPairCancellationOwned : Bool
    twoFieldOrderedPairCancellationOwnedIsTrue :
      twoFieldOrderedPairCancellationOwned ≡ true

canonicalElsasserOrderedRealityBoundary : ElsasserOrderedRealityBoundary
canonicalElsasserOrderedRealityBoundary =
  elsasser-ordered-reality-boundary false refl true refl true refl true refl
