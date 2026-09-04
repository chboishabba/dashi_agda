module DASHI.Physics.Plasma.MHDElsasserThreeLegNormalFormCancellationExact where

open import DASHI.Core.Prelude
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadSymmetry as Symmetry
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadOrbitConstruction as Orbit
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3FieldAlgebra as Algebra
import DASHI.Physics.Closure.NSTriadKNComplex3RealityPhaseAudit as Audit
import DASHI.Physics.Closure.NSTriadKNComplex3OrderedRealityCancellation as Ordered
import DASHI.Physics.Closure.NSTriadKNComplex3EnergyCancellation as Energy
import DASHI.Physics.Closure.NSTriadKNEnergyCancellationAssembly as Assembly
import DASHI.Physics.Plasma.MHDElsasserOrderedRealityPairCancellationExact as Pair

------------------------------------------------------------------------
-- THREE-LEG COMPILATION FOR TWO DISTINCT FOURIER FIELDS
------------------------------------------------------------------------

normalFormConjugateInvariant :
  ∀ {r} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F)
    (tau : Physical.PhysicalTriadIncidence)
    (transport target : Z3.FourierMode → C3.Complex3 F) →
  Audit.RealityCondition transport →
  Audit.RealityCondition target →
  Pair.elsasserOrderedNormalForm E (Symmetry.conjugateTriad tau) transport target
  ≡ Pair.elsasserOrderedNormalForm E tau transport target
normalFormConjugateInvariant {F = F}
  E tau transport target transportReality targetReality =
  trans
    (cong C3.complexRealPart
      (cong (C3.complexMultiply (Ordered.minusI F))
        (cong₂ C3.complexMultiply
          (Energy.conjugateWaveFactor E tau transport transportReality)
          (Energy.conjugatePairing tau target targetReality))))
    (Energy.conjugateNormalFormInvariant baseWave basePair)
  where
  baseWave =
    C3.bilinearDot3
      (transport (Physical.p tau))
      (C3.modeVector E (Physical.q tau))
  basePair =
    C3.hermitianPairing3
      (target (Physical.k tau))
      (target (Physical.q tau))

normalFormRespectsLattice :
  ∀ {r} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F)
    (transport target : Z3.FourierMode → C3.Complex3 F)
    {left right : Physical.PhysicalTriadIncidence} →
  Symmetry.SameLatticeTriad left right →
  Pair.elsasserOrderedNormalForm E left transport target
  ≡ Pair.elsasserOrderedNormalForm E right transport target
normalFormRespectsLattice E transport target
  (Symmetry.same-lattice-triad refl refl refl) = refl

elsasserOrderedTransferLaws :
  ∀ {r} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F)
    (transport target : Z3.FourierMode → C3.Complex3 F) →
  Audit.RealityCondition transport →
  Audit.RealityCondition target →
  Audit.DivergenceFreeCondition E transport →
  Assembly.OrderedTransferCancellationLaws (C3.Complex F)
elsasserOrderedTransferLaws {F = F}
  E transport target transportReality targetReality transportDivergenceFree = record
  { zero = C3.complexZero F
  ; add = C3.complexAdd
  ; addZeroLeft = Algebra.complexAddZeroLeft
  ; addZeroRight = Algebra.complexAddZeroRight
  ; reorderSix = Algebra.complexAddReorderSix
  ; orderedTransfer = λ tau →
      Pair.elsasserOrderedNormalForm E tau transport target
  ; respectsLattice = normalFormRespectsLattice E transport target
  ; conjugateInvariant = λ tau →
      normalFormConjugateInvariant
        E tau transport target transportReality targetReality
  ; orderedRealityMateCancels = λ tau →
      Pair.elsasserOrderedRealityPairCancellation
        E tau transport target transportDivergenceFree targetReality
  }

elsasserThreeLegNormalFormCancellation :
  ∀ {r} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F)
    (tau : Physical.PhysicalTriadIncidence)
    (transport target : Z3.FourierMode → C3.Complex3 F)
    (transportReality : Audit.RealityCondition transport)
    (targetReality : Audit.RealityCondition target)
    (transportDivergenceFree : Audit.DivergenceFreeCondition E transport) →
  let laws =
        elsasserOrderedTransferLaws
          E transport target
          transportReality targetReality transportDivergenceFree
  in
  Assembly.add laws
    (Assembly.add laws
      (Assembly.orderedPairTransfer laws tau)
      (Assembly.orderedPairTransfer laws (Orbit.pEnergyLeg tau)))
    (Assembly.orderedPairTransfer laws (Orbit.qEnergyLeg tau))
  ≡ Assembly.zero laws
elsasserThreeLegNormalFormCancellation
  E tau transport target transportReality targetReality transportDivergenceFree =
  Assembly.orderedRealityCancellationImpliesThreeLegCancellation
    (elsasserOrderedTransferLaws
      E transport target transportReality targetReality transportDivergenceFree)
    tau

record ThreeLegNormalFormBoundary : Set where
  constructor three-leg-normal-form-boundary
  field
    transportAndTargetMayDiffer : Bool
    transportAndTargetMayDifferIsTrue : transportAndTargetMayDiffer ≡ true

    threeLegNormalFormCancellationOwned : Bool
    threeLegNormalFormCancellationOwnedIsTrue :
      threeLegNormalFormCancellationOwned ≡ true

    literalMhdPdeNormalFormIdentificationOwnedHere : Bool
    literalMhdPdeNormalFormIdentificationOwnedHereIsFalse :
      literalMhdPdeNormalFormIdentificationOwnedHere ≡ false

canonicalThreeLegNormalFormBoundary : ThreeLegNormalFormBoundary
canonicalThreeLegNormalFormBoundary =
  three-leg-normal-form-boundary true refl true refl false refl
