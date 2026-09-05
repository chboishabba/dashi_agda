module DASHI.Physics.Plasma.MHDLiteralMagneticHelicityTriadConservationExact where

open import DASHI.Core.Prelude
open import Agda.Primitive using (Level)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym; trans; _≡_; refl)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadOrbitConstruction as Orbit
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3FieldAlgebra as Field
import DASHI.Physics.Closure.NSTriadKNComplexCommutativeRingExact as Ring
import DASHI.Physics.Closure.NSTriadKNComplex3HermitianAdditiveLaws as Additive
import DASHI.Physics.Closure.NSTriadKNModeInverseSquareRealityRound35Exact as InverseReality
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Plasma.MHDPlusMinusProjectedPseudoEnergyExact as State
import DASHI.Physics.Plasma.MHDDoubledMagneticElsasserFibreExact as Doubled
import DASHI.Physics.Plasma.MHDOrderedPairInductionCurlBidiExact as CurlPair
import DASHI.Physics.Plasma.MHDMagneticHelicityThreeLegBidiExact as ThreeLeg
import DASHI.Physics.Plasma.MHDMagneticHelicityLegTripleAmplitudeExact as Leg
import DASHI.Physics.Plasma.MHDMagneticHelicityTriplePairCancellationExact as Pair

------------------------------------------------------------------------
-- FINAL LITERAL IDEAL-MHD MAGNETIC-HELICITY TRIAD CONSERVATION
------------------------------------------------------------------------

doubledVelocityReality :
  ∀ {r : Level} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    (state : State.IdealElsasserFourierState F E)
    (k : Z3.FourierMode) →
  CurlPair.doubledVelocity state (Z3.negateMode k)
  ≡ C3.complex3Conjugate (CurlPair.doubledVelocity state k)
doubledVelocityReality state k =
  trans
    (cong₂ C3.complex3Add
      (State.plusReality state k)
      (State.minusReality state k))
    (sym
      (Additive.complex3ConjugateAdd
        (State.zPlus state k) (State.zMinus state k)))

pEnergyLegNonzero :
  (tau : Physical.PhysicalTriadIncidence) →
  Physical.NonZeroPhysicalTriad tau →
  Physical.NonZeroPhysicalTriad (Orbit.pEnergyLeg tau)
pEnergyLegNonzero tau nonzero =
  Physical.nonzero-triad
    (Physical.kNonzero nonzero)
    (InverseReality.negateModeNonzero (Physical.qNonzero nonzero))
    (Physical.pNonzero nonzero)

qEnergyLegNonzero :
  (tau : Physical.PhysicalTriadIncidence) →
  Physical.NonZeroPhysicalTriad tau →
  Physical.NonZeroPhysicalTriad (Orbit.qEnergyLeg tau)
qEnergyLegNonzero tau nonzero =
  Physical.nonzero-triad
    (Physical.kNonzero nonzero)
    (InverseReality.negateModeNonzero (Physical.pNonzero nonzero))
    (Physical.qNonzero nonzero)

record SixMagneticAmplitudes
    {r : Level} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    (state : State.IdealElsasserFourierState F E)
    (tau : Physical.PhysicalTriadIncidence) : Set r where
  constructor six-magnetic-amplitudes
  field
    A B C D E₁ F₁ : C3.Complex F

open SixMagneticAmplitudes public

canonicalSixMagneticAmplitudes :
  ∀ {r : Level} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    (state : State.IdealElsasserFourierState F E)
    (tau : Physical.PhysicalTriadIncidence) →
  SixMagneticAmplitudes state tau
canonicalSixMagneticAmplitudes state tau =
  six-magnetic-amplitudes
    (C3.complexRealPart
      (Pair.baseAmplitude
        (CurlPair.doubledVelocity state (Physical.p tau))
        (Doubled.doubledMagnetic state (Physical.q tau))
        (Doubled.doubledMagnetic state (Physical.k tau))))
    (C3.complexRealPart
      (Pair.baseAmplitude
        (CurlPair.doubledVelocity state (Physical.q tau))
        (Doubled.doubledMagnetic state (Physical.p tau))
        (Doubled.doubledMagnetic state (Physical.k tau))))
    (C3.complexRealPart
      (Pair.middleAmplitude
        (Doubled.doubledMagnetic state (Physical.p tau))
        (CurlPair.doubledVelocity state (Physical.k tau))
        (Doubled.doubledMagnetic state (Physical.q tau))))
    (C3.complexRealPart
      (Pair.reversedRealityMateAmplitude
        (CurlPair.doubledVelocity state (Physical.q tau))
        (Doubled.doubledMagnetic state (Physical.p tau))
        (Doubled.doubledMagnetic state (Physical.k tau))))
    (C3.complexRealPart
      (Pair.middleAmplitude
        (Doubled.doubledMagnetic state (Physical.q tau))
        (CurlPair.doubledVelocity state (Physical.k tau))
        (Doubled.doubledMagnetic state (Physical.p tau))))
    (C3.complexRealPart
      (Pair.reversedRealityMateAmplitude
        (CurlPair.doubledVelocity state (Physical.p tau))
        (Doubled.doubledMagnetic state (Physical.q tau))
        (Doubled.doubledMagnetic state (Physical.k tau))))

kLegAmplitudeNormalForm :
  ∀ {r : Level} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    (state : State.IdealElsasserFourierState F E)
    (tau : Physical.PhysicalTriadIncidence) →
  Leg.legTripleAmplitude state tau
  ≡ C3.complexAdd
      (A (canonicalSixMagneticAmplitudes state tau))
      (B (canonicalSixMagneticAmplitudes state tau))
kLegAmplitudeNormalForm state tau = refl

pLegAmplitudeNormalForm :
  ∀ {r : Level} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    (state : State.IdealElsasserFourierState F E)
    (tau : Physical.PhysicalTriadIncidence) →
  Leg.legTripleAmplitude state (Orbit.pEnergyLeg tau)
  ≡ C3.complexAdd
      (C (canonicalSixMagneticAmplitudes state tau))
      (D (canonicalSixMagneticAmplitudes state tau))
pLegAmplitudeNormalForm state tau
  rewrite Doubled.doubledMagneticReality state (Physical.q tau)
        | doubledVelocityReality state (Physical.q tau) = refl

qLegAmplitudeNormalForm :
  ∀ {r : Level} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    (state : State.IdealElsasserFourierState F E)
    (tau : Physical.PhysicalTriadIncidence) →
  Leg.legTripleAmplitude state (Orbit.qEnergyLeg tau)
  ≡ C3.complexAdd
      (E₁ (canonicalSixMagneticAmplitudes state tau))
      (F₁ (canonicalSixMagneticAmplitudes state tau))
qLegAmplitudeNormalForm state tau
  rewrite Doubled.doubledMagneticReality state (Physical.p tau)
        | doubledVelocityReality state (Physical.p tau) = refl

firstRealityPairCancels :
  ∀ {r : Level} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    (state : State.IdealElsasserFourierState F E)
    (tau : Physical.PhysicalTriadIncidence) →
  C3.complexAdd
    (A (canonicalSixMagneticAmplitudes state tau))
    (F₁ (canonicalSixMagneticAmplitudes state tau))
  ≡ C3.complexZero F
firstRealityPairCancels state tau =
  Pair.realityMateRealPairCancels
    (CurlPair.doubledVelocity state (Physical.p tau))
    (Doubled.doubledMagnetic state (Physical.q tau))
    (Doubled.doubledMagnetic state (Physical.k tau))

secondRealityPairCancels :
  ∀ {r : Level} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    (state : State.IdealElsasserFourierState F E)
    (tau : Physical.PhysicalTriadIncidence) →
  C3.complexAdd
    (B (canonicalSixMagneticAmplitudes state tau))
    (D (canonicalSixMagneticAmplitudes state tau))
  ≡ C3.complexZero F
secondRealityPairCancels state tau =
  Pair.realityMateRealPairCancels
    (CurlPair.doubledVelocity state (Physical.q tau))
    (Doubled.doubledMagnetic state (Physical.p tau))
    (Doubled.doubledMagnetic state (Physical.k tau))

middlePairCancels :
  ∀ {r : Level} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    (state : State.IdealElsasserFourierState F E)
    (tau : Physical.PhysicalTriadIncidence) →
  C3.complexAdd
    (C (canonicalSixMagneticAmplitudes state tau))
    (E₁ (canonicalSixMagneticAmplitudes state tau))
  ≡ C3.complexZero F
middlePairCancels state tau =
  Pair.middleRealPairCancels
    (Doubled.doubledMagnetic state (Physical.p tau))
    (CurlPair.doubledVelocity state (Physical.k tau))
    (Doubled.doubledMagnetic state (Physical.q tau))

sixAmplitudeRegroup :
  ∀ {r : Level} {F : C3.RealField r}
    (a b c d e f : C3.Complex F) →
  C3.complexAdd
    (C3.complexAdd a b)
    (C3.complexAdd (C3.complexAdd c d) (C3.complexAdd e f))
  ≡
  C3.complexAdd
    (C3.complexAdd a f)
    (C3.complexAdd (C3.complexAdd b d) (C3.complexAdd c e))
sixAmplitudeRegroup {F = F} a b c d e f =
  R.solve 6
    (λ a b c d e f →
      ((a R.⊕ b) R.⊕ ((c R.⊕ d) R.⊕ (e R.⊕ f)))
      R.⊜
      ((a R.⊕ f) R.⊕ ((b R.⊕ d) R.⊕ (c R.⊕ e))))
    refl a b c d e f
  where module R = Ring.Solver F

zeroNest :
  ∀ {r : Level} {F : C3.RealField r} →
  C3.complexAdd (C3.complexZero F)
    (C3.complexAdd (C3.complexZero F) (C3.complexZero F))
  ≡ C3.complexZero F
zeroNest {F = F} =
  trans
    (Field.complexAddZeroLeft
      (C3.complexAdd (C3.complexZero F) (C3.complexZero F)))
    (Field.complexAddZeroLeft (C3.complexZero F))

threeLegTripleAmplitudeCancels :
  ∀ {r : Level} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    (state : State.IdealElsasserFourierState F E)
    (tau : Physical.PhysicalTriadIncidence) →
  C3.complexAdd
    (Leg.legTripleAmplitude state tau)
    (C3.complexAdd
      (Leg.legTripleAmplitude state (Orbit.pEnergyLeg tau))
      (Leg.legTripleAmplitude state (Orbit.qEnergyLeg tau)))
  ≡ C3.complexZero F
threeLegTripleAmplitudeCancels {F = F} state tau =
  let M = canonicalSixMagneticAmplitudes state tau in
  trans
    (cong₂ C3.complexAdd
      (kLegAmplitudeNormalForm state tau)
      (cong₂ C3.complexAdd
        (pLegAmplitudeNormalForm state tau)
        (qLegAmplitudeNormalForm state tau)))
    (trans
      (sixAmplitudeRegroup
        (A M) (B M) (C M) (D M) (E₁ M) (F₁ M))
      (trans
        (cong₂ C3.complexAdd
          (firstRealityPairCancels state tau)
          (cong₂ C3.complexAdd
            (secondRealityPairCancels state tau)
            (middlePairCancels state tau)))
        zeroNest))

literalMagneticHelicityTriadConservation :
  ∀ {r : Level} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F)
    (I : C3.ModeInverseSquare F E)
    (S : Helical.HelicalModeScalars F)
    (L : Helical.PeriodicHelicalProjectorLaws F E I S)
    (state : State.IdealElsasserFourierState F E)
    (tau : Physical.PhysicalTriadIncidence) →
  Physical.NonZeroPhysicalTriad tau →
  ThreeLeg.magneticHelicityThreeLegVariation E I state tau
  ≡ C3.complexZero F
literalMagneticHelicityTriadConservation
    E I S L state tau nonzero =
  trans
    (cong₂ C3.complexAdd
      (Leg.magneticHelicityLegVariationIsTripleAmplitude
        E I S L state tau nonzero)
      (cong₂ C3.complexAdd
        (Leg.magneticHelicityLegVariationIsTripleAmplitude
          E I S L state (Orbit.pEnergyLeg tau)
          (pEnergyLegNonzero tau nonzero))
        (Leg.magneticHelicityLegVariationIsTripleAmplitude
          E I S L state (Orbit.qEnergyLeg tau)
          (qEnergyLegNonzero tau nonzero))))
    (threeLegTripleAmplitudeCancels state tau)

record LiteralMagneticHelicityConservationBoundary : Set where
  constructor literal-magnetic-helicity-conservation-boundary
  field
    literalNonzeroTriadConservationOwned : Bool
    literalNonzeroTriadConservationOwnedIsTrue :
      literalNonzeroTriadConservationOwned ≡ true

    proofUsesThreePreNormPairCancellations : Bool
    proofUsesThreePreNormPairCancellationsIsTrue :
      proofUsesThreePreNormPairCancellations ≡ true

    proofUsesIllicitHermitianCyclicPermutation : Bool
    proofUsesIllicitHermitianCyclicPermutationIsFalse :
      proofUsesIllicitHermitianCyclicPermutation ≡ false

    divisionByTwoUsed : Bool
    divisionByTwoUsedIsFalse : divisionByTwoUsed ≡ false

canonicalLiteralMagneticHelicityConservationBoundary :
  LiteralMagneticHelicityConservationBoundary
canonicalLiteralMagneticHelicityConservationBoundary =
  literal-magnetic-helicity-conservation-boundary
    true refl true refl false refl false refl
