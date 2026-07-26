module DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit where

open import Agda.Primitive using (Level; lsuc)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.List.Base using (List; []; _∷_)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNExactSignedGalerkinCoefficient as Signed

------------------------------------------------------------------------
-- Literal finite velocity state and projected Galerkin nonlinearity.
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
    triadsAreLiteralResonances : Set
    zeroModeExcluded : Set
    realityClosed : Set

open FiniteComplex3GalerkinSystem public

sumVectors :
  ∀ {r} {F : C3.RealField r} →
  List (C3.Complex3 F) → C3.Complex3 F
sumVectors {F = F} [] = C3.complex3Zero F
sumVectors (x ∷ xs) = C3.complex3Add x (sumVectors xs)

mapTriadTerms :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E} →
  FiniteComplex3GalerkinSystem F E I →
  Z3.FourierMode →
  List Physical.PhysicalTriadIncidence →
  List (C3.Complex3 F)
mapTriadTerms system k [] = []
mapTriadTerms {F = F} {E} {I} system k (τ ∷ rest) =
  term ∷ mapTriadTerms system k rest
  where
  L = C3.complex3VelocityGalerkinLaws F E I

  term : C3.Complex3 F
  term =
    Signed.orderedVelocityInteraction L
      k
      (Physical.p τ)
      (Physical.q τ)
      (velocity system (Physical.p τ))
      (velocity system (Physical.q τ))

projectedNonlinearity :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E} →
  FiniteComplex3GalerkinSystem F E I →
  Z3.FourierMode → C3.Complex3 F
projectedNonlinearity system k =
  sumVectors (mapTriadTerms system k (triads system))

------------------------------------------------------------------------
-- Ordered versus symmetrised conventions.
--
-- A sum over all ordered resonant pairs already contains both (p,q) and
-- (q,p).  A quotient by the swap orbit must insert the corresponding orbit
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

factorAndOrbitAuditTargetImplemented : Bool
factorAndOrbitAuditTargetImplemented = true

factorAndOrbitAuditTargetImplementedIsTrue :
  factorAndOrbitAuditTargetImplemented ≡ true
factorAndOrbitAuditTargetImplementedIsTrue = refl

physicalSpaceGalerkinEquivalenceClosed : Bool
physicalSpaceGalerkinEquivalenceClosed = false

physicalSpaceGalerkinEquivalenceClosedIsFalse :
  physicalSpaceGalerkinEquivalenceClosed ≡ false
physicalSpaceGalerkinEquivalenceClosedIsFalse = refl
