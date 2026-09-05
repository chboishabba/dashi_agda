module DASHI.Physics.Plasma.MHDElsasserProjectedThreeLegCancellationExact where

open import DASHI.Core.Prelude
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadSymmetry as Symmetry
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadOrbitConstruction as Orbit
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3FieldAlgebra as Algebra
import DASHI.Physics.Closure.NSTriadKNComplex3RealityPhaseAudit as Audit
import DASHI.Physics.Closure.NSTriadKNEnergyCancellationAssembly as Assembly
import DASHI.Physics.Plasma.MHDElsasserProjectedNonlinearCoefficientExact as Projected
import DASHI.Physics.Plasma.MHDElsasserOrderedRealityPairCancellationExact as Pair
import DASHI.Physics.Plasma.MHDElsasserThreeLegNormalFormCancellationExact as Normal

------------------------------------------------------------------------
-- LITERAL PROJECTED ORDERED TRANSFER
------------------------------------------------------------------------

projectedOrderedTransferAt :
  ∀ {r} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F)
    (I : C3.ModeInverseSquare F E) →
  Physical.PhysicalTriadIncidence →
  (Z3.FourierMode → C3.Complex3 F) →
  (Z3.FourierMode → C3.Complex3 F) →
  C3.Complex F
projectedOrderedTransferAt E I tau transport target =
  Projected.testedElsasserOrderedTransfer E I
    (Physical.k tau) (Physical.q tau)
    (transport (Physical.p tau))
    (target (Physical.q tau))
    (target (Physical.k tau))

projectedTransferIsNormalForm :
  ∀ {r} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F)
    (I : C3.ModeInverseSquare F E)
    (tau : Physical.PhysicalTriadIncidence)
    (transport target : Z3.FourierMode → C3.Complex3 F) →
  Audit.DivergenceFreeCondition E target →
  projectedOrderedTransferAt E I tau transport target
  ≡ Pair.elsasserOrderedNormalForm E tau transport target
projectedTransferIsNormalForm E I tau transport target targetDivergenceFree =
  Projected.elsasserOrderedTransferNormalForm
    E I
    (Physical.k tau) (Physical.q tau)
    (transport (Physical.p tau))
    (target (Physical.q tau))
    (target (Physical.k tau))
    (targetDivergenceFree (Physical.k tau))

projectedTransferRespectsLattice :
  ∀ {r} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F)
    (I : C3.ModeInverseSquare F E)
    (transport target : Z3.FourierMode → C3.Complex3 F)
    {left right : Physical.PhysicalTriadIncidence} →
  Symmetry.SameLatticeTriad left right →
  projectedOrderedTransferAt E I left transport target
  ≡ projectedOrderedTransferAt E I right transport target
projectedTransferRespectsLattice E I transport target
  (Symmetry.same-lattice-triad refl refl refl) = refl

projectedTransferConjugateInvariant :
  ∀ {r} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F)
    (I : C3.ModeInverseSquare F E)
    (tau : Physical.PhysicalTriadIncidence)
    (transport target : Z3.FourierMode → C3.Complex3 F) →
  Audit.RealityCondition transport →
  Audit.RealityCondition target →
  Audit.DivergenceFreeCondition E target →
  projectedOrderedTransferAt E I (Symmetry.conjugateTriad tau) transport target
  ≡ projectedOrderedTransferAt E I tau transport target
projectedTransferConjugateInvariant
  E I tau transport target transportReality targetReality targetDivergenceFree =
  trans
    (projectedTransferIsNormalForm
      E I (Symmetry.conjugateTriad tau) transport target targetDivergenceFree)
    (trans
      (Normal.normalFormConjugateInvariant
        E tau transport target transportReality targetReality)
      (sym
        (projectedTransferIsNormalForm
          E I tau transport target targetDivergenceFree)))

projectedOrderedRealityMateCancels :
  ∀ {r} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F)
    (I : C3.ModeInverseSquare F E)
    (tau : Physical.PhysicalTriadIncidence)
    (transport target : Z3.FourierMode → C3.Complex3 F) →
  Audit.DivergenceFreeCondition E transport →
  Audit.DivergenceFreeCondition E target →
  Audit.RealityCondition target →
  C3.complexAdd
    (projectedOrderedTransferAt E I tau transport target)
    (projectedOrderedTransferAt E I
      (Orbit.orderedRealityMate tau) transport target)
  ≡ C3.complexZero F
projectedOrderedRealityMateCancels {F = F}
  E I tau transport target transportDivergenceFree targetDivergenceFree targetReality =
  trans
    (cong₂ C3.complexAdd
      (projectedTransferIsNormalForm
        E I tau transport target targetDivergenceFree)
      (projectedTransferIsNormalForm
        E I (Orbit.orderedRealityMate tau) transport target targetDivergenceFree))
    (Pair.elsasserOrderedRealityPairCancellation
      E tau transport target transportDivergenceFree targetReality)

projectedElsasserTransferLaws :
  ∀ {r} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F)
    (I : C3.ModeInverseSquare F E)
    (transport target : Z3.FourierMode → C3.Complex3 F) →
  Audit.RealityCondition transport →
  Audit.RealityCondition target →
  Audit.DivergenceFreeCondition E transport →
  Audit.DivergenceFreeCondition E target →
  Assembly.OrderedTransferCancellationLaws (C3.Complex F)
projectedElsasserTransferLaws {F = F}
  E I transport target transportReality targetReality
  transportDivergenceFree targetDivergenceFree = record
  { zero = C3.complexZero F
  ; add = C3.complexAdd
  ; addZeroLeft = Algebra.complexAddZeroLeft
  ; addZeroRight = Algebra.complexAddZeroRight
  ; reorderSix = Algebra.complexAddReorderSix
  ; orderedTransfer = λ tau →
      projectedOrderedTransferAt E I tau transport target
  ; respectsLattice = projectedTransferRespectsLattice E I transport target
  ; conjugateInvariant = λ tau →
      projectedTransferConjugateInvariant
        E I tau transport target
        transportReality targetReality targetDivergenceFree
  ; orderedRealityMateCancels = λ tau →
      projectedOrderedRealityMateCancels
        E I tau transport target
        transportDivergenceFree targetDivergenceFree targetReality
  }

projectedElsasserThreeLegCancellation :
  ∀ {r} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F)
    (I : C3.ModeInverseSquare F E)
    (tau : Physical.PhysicalTriadIncidence)
    (transport target : Z3.FourierMode → C3.Complex3 F)
    (transportReality : Audit.RealityCondition transport)
    (targetReality : Audit.RealityCondition target)
    (transportDivergenceFree : Audit.DivergenceFreeCondition E transport)
    (targetDivergenceFree : Audit.DivergenceFreeCondition E target) →
  let laws =
        projectedElsasserTransferLaws
          E I transport target
          transportReality targetReality
          transportDivergenceFree targetDivergenceFree
  in
  Assembly.add laws
    (Assembly.add laws
      (Assembly.orderedPairTransfer laws tau)
      (Assembly.orderedPairTransfer laws (Orbit.pEnergyLeg tau)))
    (Assembly.orderedPairTransfer laws (Orbit.qEnergyLeg tau))
  ≡ Assembly.zero laws
projectedElsasserThreeLegCancellation
  E I tau transport target transportReality targetReality
  transportDivergenceFree targetDivergenceFree =
  Assembly.orderedRealityCancellationImpliesThreeLegCancellation
    (projectedElsasserTransferLaws
      E I transport target
      transportReality targetReality
      transportDivergenceFree targetDivergenceFree)
    tau

record ProjectedThreeLegBoundary : Set where
  constructor projected-three-leg-boundary
  field
    projectedThreeLegCancellationOwned : Bool
    projectedThreeLegCancellationOwnedIsTrue :
      projectedThreeLegCancellationOwned ≡ true

    plusAndMinusMayInstantiateSameTheoremSeparately : Bool
    plusAndMinusMayInstantiateSameTheoremSeparatelyIsTrue :
      plusAndMinusMayInstantiateSameTheoremSeparately ≡ true

    pdeToProjectedFourierIdentificationStillSeparate : Bool
    pdeToProjectedFourierIdentificationStillSeparateIsTrue :
      pdeToProjectedFourierIdentificationStillSeparate ≡ true

canonicalProjectedThreeLegBoundary : ProjectedThreeLegBoundary
canonicalProjectedThreeLegBoundary =
  projected-three-leg-boundary true refl true refl true refl
