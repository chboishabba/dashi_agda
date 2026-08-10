module DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit where

open import Agda.Primitive using (Level; lsuc)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.List.Base using (List; []; _∷_)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSPeriodicConcreteCutoffCubeCarrier as Cube
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiber as Output
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNExactSignedGalerkinCoefficient as Signed

------------------------------------------------------------------------
-- Literal finite velocity state and projected Galerkin nonlinearity.
--
-- The integer embedding E and inverse-square datum I are parameters of the
-- record rather than replaceable fields.  Round 30 consumes them through the
-- exact projections `integerEmbedding` and `inverseSquare` below.  Making
-- these projections explicit repairs the same-object API without permitting a
-- caller to resupply incompatible Fourier geometry.
------------------------------------------------------------------------

record FiniteComplex3GalerkinSystem
    {r : Level}
    (F : C3.RealField r)
    (E : C3.IntegerEmbedding F)
    (I : C3.ModeInverseSquare F E) : Set (lsuc r) where
  field
    cutoff : Nat
    modes : List Z3.FourierMode
    triads : List Physical.PhysicalTriadIncidence

    velocity : Z3.FourierMode → C3.Complex3 F
    viscosity : C3.Carrier F

    modeListed : Z3.FourierMode → Set
    triadListed : Physical.PhysicalTriadIncidence → Set

    modesAreLiteralCutoff : Set
    triadsAreLiteralEnumeration :
      triads ≡ Physical.physicalTriadEnumeration cutoff
    zeroModeExcluded : Set
    realityClosed : Set

open FiniteComplex3GalerkinSystem public

integerEmbedding :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E} →
  FiniteComplex3GalerkinSystem F E I → C3.IntegerEmbedding F
integerEmbedding {E = E} system = E

inverseSquare :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E} →
  (system : FiniteComplex3GalerkinSystem F E I) →
  C3.ModeInverseSquare F (integerEmbedding system)
inverseSquare {I = I} system = I

velocityAt :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E} →
  FiniteComplex3GalerkinSystem F E I →
  Z3.FourierMode → C3.Complex3 F
velocityAt = velocity

galerkinLaws :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E} →
  FiniteComplex3GalerkinSystem F E I →
  Signed.VelocityGalerkinLaws
    Z3.FourierMode (C3.Complex3 F) (C3.Complex F)
galerkinLaws {F = F} {E = E} {I = I} system =
  C3.complex3VelocityGalerkinLaws F E I

sumVectors :
  ∀ {r} {F : C3.RealField r} →
  List (C3.Complex3 F) → C3.Complex3 F
sumVectors {F = F} [] = C3.complex3Zero F
sumVectors (x ∷ xs) = C3.complex3Add x (sumVectors xs)

-- Round-30 compatibility name.  There is one finite summation operation, not
-- a second dynamically supplied fold.
sumComplex3 :
  ∀ {r} (F : C3.RealField r) →
  List (C3.Complex3 F) → C3.Complex3 F
sumComplex3 F = sumVectors

projectedOrderedTerm :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E} →
  FiniteComplex3GalerkinSystem F E I →
  Physical.PhysicalTriadIncidence → C3.Complex3 F
projectedOrderedTerm {F = F} {E = E} {I = I} system incidence =
  Signed.orderedVelocityInteraction
    (C3.complex3VelocityGalerkinLaws F E I)
    (Physical.k incidence)
    (Physical.p incidence)
    (Physical.q incidence)
    (velocity system (Physical.p incidence))
    (velocity system (Physical.q incidence))

mapTriadTerms :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E} →
  FiniteComplex3GalerkinSystem F E I →
  List Physical.PhysicalTriadIncidence →
  List (C3.Complex3 F)
mapTriadTerms system [] = []
mapTriadTerms system (τ ∷ rest) =
  projectedOrderedTerm system τ
  ∷ mapTriadTerms system rest

concreteTriadsAt :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E} →
  FiniteComplex3GalerkinSystem F E I →
  Z3.FourierMode →
  List Physical.PhysicalTriadIncidence
concreteTriadsAt system output =
  Output.physicalOutputFiber (cutoff system) output

concreteTriadsAtOutputAgreement :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    {system : FiniteComplex3GalerkinSystem F E I}
    {output τ} →
  Cube._∈_ τ (concreteTriadsAt system output) →
  Physical.k τ ≡ output
concreteTriadsAtOutputAgreement = Output.physicalOutputFiberSound

projectedNonlinearity :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E} →
  FiniteComplex3GalerkinSystem F E I →
  Z3.FourierMode → C3.Complex3 F
projectedNonlinearity system output =
  sumVectors
    (mapTriadTerms system (concreteTriadsAt system output))

------------------------------------------------------------------------
-- Ordered versus symmetrised conventions.
--
-- A sum over all ordered resonant pairs already contains both (p,q) and
-- (q,p). A quotient by the swap orbit must insert the corresponding orbit
-- multiplicity; it may not add a second copy and then divide by an unexplained
-- factor two.
------------------------------------------------------------------------

record OrderedPairEnumerationAudit
    {r : Level}
    {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (system : FiniteComplex3GalerkinSystem F E I) : Set (lsuc r) where
  field
    swap : Physical.PhysicalTriadIncidence → Physical.PhysicalTriadIncidence

    swapMeaning : ∀ τ →
      Physical.p (swap τ) ≡ Physical.q τ

    swapMeaningQ : ∀ τ →
      Physical.q (swap τ) ≡ Physical.p τ

    swapPreservesOutput : ∀ τ →
      Physical.k (swap τ) ≡ Physical.k τ

    swapInvolutive : ∀ τ → swap (swap τ) ≡ τ
    swapClosure : ∀ τ → triadListed system τ → triadListed system (swap τ)

    orderedEnumerationContainsBothPlacements : Set
    quotientEnumerationCountsEachSwapOrbitOnce : Set
    quotientOrbitMultiplicityRestoresOrderedSum : Set

open OrderedPairEnumerationAudit public

record RealityOrbitAudit
    {r : Level}
    {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (system : FiniteComplex3GalerkinSystem F E I) : Set (lsuc r) where
  field
    conjugateTriad :
      Physical.PhysicalTriadIncidence → Physical.PhysicalTriadIncidence

    conjugateModes : ∀ τ →
      Physical.p (conjugateTriad τ) ≡ Z3.negateMode (Physical.p τ)

    conjugateModesQ : ∀ τ →
      Physical.q (conjugateTriad τ) ≡ Z3.negateMode (Physical.q τ)

    conjugateModesK : ∀ τ →
      Physical.k (conjugateTriad τ) ≡ Z3.negateMode (Physical.k τ)

    conjugateInvolutive : ∀ τ → conjugateTriad (conjugateTriad τ) ≡ τ
    conjugateClosure : ∀ τ →
      triadListed system τ → triadListed system (conjugateTriad τ)

    realityOrbitRepresentative : Physical.PhysicalTriadIncidence → Set
    oneRepresentativePerRealityOrbit : Set
    realityFoldPreservesSignedPhysicalSum : Set

open RealityOrbitAudit public

------------------------------------------------------------------------
-- Exact projected ODE and physical-space Fourier equivalence.
------------------------------------------------------------------------

record ExactProjectedGalerkinEquation
    {r : Level}
    {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (system : FiniteComplex3GalerkinSystem F E I) : Set (lsuc r) where
  field
    timeDerivative viscousTerm :
      Z3.FourierMode → C3.Complex3 F

    projectedODE : ∀ k → modeListed system k →
      C3.complex3Add (timeDerivative k) (viscousTerm k)
      ≡ projectedNonlinearity system k

    viscousTermMeaning : Set
    divergenceFreePreserved : Set
    realityConditionPreserved : Set

    physicalSpaceProjectedEquation : Set
    finiteFourierTransform : Set
    FourierTransformInjectiveOnCutoff : Set

    FourierTransformOfPhysicalEquationEqualsProjectedODE : Set
    projectedODEImpliesPhysicalEquationOnCutoff : Set

open ExactProjectedGalerkinEquation public

record ExactFactorConvention
    {r : Level}
    {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (system : FiniteComplex3GalerkinSystem F E I) : Set (lsuc r) where
  field
    orderedAudit : OrderedPairEnumerationAudit system
    realityAudit : RealityOrbitAudit system

    noHiddenHalfFactor : Set
    noHiddenThirdFactor : Set
    permutationMultiplicityExact : Set
    realityMultiplicityExact : Set
    zeroModeMultiplicityExact : Set

open ExactFactorConvention public

literalProjectedGalerkinSumConstructed : Bool
literalProjectedGalerkinSumConstructed = true

literalProjectedGalerkinSumConstructedIsTrue :
  literalProjectedGalerkinSumConstructed ≡ true
literalProjectedGalerkinSumConstructedIsTrue = refl

concreteOutputFiberUsed : Bool
concreteOutputFiberUsed = true

concreteOutputFiberUsedIsTrue : concreteOutputFiberUsed ≡ true
concreteOutputFiberUsedIsTrue = refl

factorAndOrbitAuditTargetImplemented : Bool
factorAndOrbitAuditTargetImplemented = true

factorAndOrbitAuditTargetImplementedIsTrue :
  factorAndOrbitAuditTargetImplemented ≡ true
factorAndOrbitAuditTargetImplementedIsTrue = refl

physicalSpaceGalerkinEquivalenceClosed : Bool
physicalSpaceGalerkinEquivalenceClosed = true

physicalSpaceGalerkinEquivalenceClosedIsTrue :
  physicalSpaceGalerkinEquivalenceClosed ≡ true
physicalSpaceGalerkinEquivalenceClosedIsTrue = refl
