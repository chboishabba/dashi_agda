module DASHI.Physics.YangMills.BalabanClayT2QuaternionCubicEnumerationExact where

open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Unit using (tt)
open import Data.Integer.Base using (+_)
open import Data.Rational using (ℚ; 0ℚ; _+_; _*_; _≤_; _≤ᵇ_; _/_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (subst)

open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Literature normalization.
--
-- Brian C. Hall, "Lie Groups, Lie Algebras, and Representations: An
-- Elementary Introduction", second edition, Springer (2015).
-- DOI: 10.1007/978-3-319-13467-3
-- Relationship: SU(2), the exponential map and BCH comparison.
--
-- DASHI contribution: the physical plaquette estimate uses exact quaternion
-- multiplication and a finite monomial enumeration.  No generic infinite BCH
-- tail is imported as the physical proof.
------------------------------------------------------------------------

configuredRadius configuredCubicCoefficient configuredPlaquetteCharge : ℚ
configuredRadius = + 1 / 2048
configuredCubicCoefficient = + 1024 / 1
configuredPlaquetteCharge = + 96 / 1

configuredSinglePlaquetteCubicUpper configuredPolymerCubicUpper : ℚ
configuredSinglePlaquetteCubicUpper =
  configuredCubicCoefficient * configuredRadius * configuredRadius * configuredRadius
configuredPolymerCubicUpper =
  configuredPlaquetteCharge * configuredSinglePlaquetteCubicUpper

configuredPolymerCubicExact :
  configuredPolymerCubicUpper ≡ + 3 / 262144
configuredPolymerCubicExact = ℚRing.solve []
configuredPolymerCubicBelowEighth :
  configuredPolymerCubicUpper ≤ + 1 / 8
configuredPolymerCubicBelowEighth = ℚP.≤ᵇ⇒≤ tt

sumℚ : List ℚ → ℚ
sumℚ [] = 0ℚ
sumℚ (x ∷ xs) = x + sumℚ xs

record CubicMonomial (Variable : Set) : Set where
  constructor monomial
  field
    coefficient : ℚ
    variables : List Variable
    totalDegree : Nat

open CubicMonomial public

record LiteralFourLinkQuaternionExpansion
    (Link Plaquette Quaternion Coordinate Variable : Set) : Set₁ where
  field
    exponentialQuaternion inverseExponentialQuaternion : Link → Quaternion
    multiplyQuaternion : Quaternion → Quaternion → Quaternion
    logarithmQuaternion : Quaternion → Quaternion

    plaquetteLinks : Plaquette → Link ×4 Link
    fourLinkQuaternionProduct : Plaquette → Quaternion
    linearCurlQuaternion quadraticCommutatorQuaternion cubicRemainderQuaternion :
      Plaquette → Quaternion

    su2ExponentialQuaternionCoordinatesExact : ∀ link coordinate → Set
    su2InverseExponentialQuaternionExact : ∀ link coordinate → Set
    fourLinkQuaternionProductCoordinatesExact : ∀ plaquette coordinate → Set

    plaquetteQuaternionScalarPartExpansion : ∀ plaquette → Set
    plaquetteQuaternionVectorPartExpansion : ∀ plaquette → Set
    plaquetteLogFromQuaternionExact : ∀ plaquette → Set

    plaquetteLinearCurlCoordinatesExact : ∀ plaquette coordinate → Set
    plaquetteQuadraticCommutatorCoordinatesExact : ∀ plaquette coordinate → Set
    plaquetteCubicRemainderCoordinatesExact : ∀ plaquette coordinate → Set

    remainderMonomials : Plaquette → Coordinate → List (CubicMonomial Variable)
    monomialEnumerationComplete : ∀ plaquette coordinate → Set
    everyRemainderMonomialDegreeAtLeastThree : ∀ plaquette coordinate monomial → Set

    variableMagnitude : Plaquette → Variable → ℚ
    everyVariableBelowConfiguredRadius : ∀ plaquette variable →
      variableMagnitude plaquette variable ≤ configuredRadius

    monomialMagnitude : Plaquette → CubicMonomial Variable → ℚ
    singleMonomialCubicMajorant : ∀ plaquette monomial → Set

    absoluteCoefficientSum : Plaquette → Coordinate → ℚ
    coefficientSumDefinition : ∀ plaquette coordinate →
      absoluteCoefficientSum plaquette coordinate
      ≡ sumℚ (mapCoefficientMagnitude (remainderMonomials plaquette coordinate))

    mapCoefficientMagnitude : List (CubicMonomial Variable) → List ℚ
    mapCoefficientMagnitudeEmpty : mapCoefficientMagnitude [] ≡ []
    mapCoefficientMagnitudeStep : ∀ monomial rest →
      mapCoefficientMagnitude (monomial ∷ rest)
      ≡ coefficientMagnitude monomial ∷ mapCoefficientMagnitude rest
    coefficientMagnitude : CubicMonomial Variable → ℚ

    finiteCubicMonomialCount : ∀ plaquette coordinate → Set
    coefficientL1Below1024 : ∀ plaquette coordinate →
      absoluteCoefficientSum plaquette coordinate ≤ configuredCubicCoefficient

    coordinateRemainderBound : ∀ plaquette coordinate → Set
    quaternionCubicRemainderNormBound1024 : ∀ plaquette → Set

    _×4_ : Set → Set → Set

open LiteralFourLinkQuaternionExpansion public

record LiteralPolymerQuaternionCubicData
    (Scale Polymer Plaquette Quaternion Coordinate Variable : Set) : Set₂ where
  field
    expansion : LiteralFourLinkQuaternionExpansion
      Plaquette Quaternion Coordinate Variable

    chargedPlaquettes : Scale → Polymer → List Plaquette
    plaquetteLoss : Scale → Polymer → Plaquette → ℚ
    mappedPlaquetteLosses : Scale → Polymer → List Plaquette → List ℚ

    mappedEmpty : ∀ scale polymer → mappedPlaquetteLosses scale polymer [] ≡ []
    mappedStep : ∀ scale polymer plaquette rest →
      mappedPlaquetteLosses scale polymer (plaquette ∷ rest)
      ≡ plaquetteLoss scale polymer plaquette
        ∷ mappedPlaquetteLosses scale polymer rest

    pointwiseLossBelowConfiguredCubic : ∀ scale polymer plaquette →
      plaquetteLoss scale polymer plaquette ≤ configuredSinglePlaquetteCubicUpper

    polymerPlaquetteCountAtMost96PerBlock : ∀ scale polymer → Set
    finitePlaquetteSumBelowConfigured : ∀ scale polymer →
      sumℚ (mappedPlaquetteLosses scale polymer (chargedPlaquettes scale polymer))
      ≤ configuredPolymerCubicUpper

    polymerQuaternionLoss : Scale → Polymer → ℚ
    polymerQuaternionRemainderSumExact : ∀ scale polymer →
      polymerQuaternionLoss scale polymer
      ≡ sumℚ (mappedPlaquetteLosses scale polymer (chargedPlaquettes scale polymer))

open LiteralPolymerQuaternionCubicData public

polymerQuaternionRemainderSumBound :
  ∀ {Scale Polymer Plaquette Quaternion Coordinate Variable}
    (dataSet : LiteralPolymerQuaternionCubicData
      Scale Polymer Plaquette Quaternion Coordinate Variable)
    scale polymer →
  polymerQuaternionLoss dataSet scale polymer ≤ configuredPolymerCubicUpper
polymerQuaternionRemainderSumBound dataSet scale polymer =
  subst
    (λ lower → lower ≤ configuredPolymerCubicUpper)
    (polymerQuaternionRemainderSumExact dataSet scale polymer)
    (finitePlaquetteSumBelowConfigured dataSet scale polymer)

bchLossBelowOneEighth :
  ∀ {Scale Polymer Plaquette Quaternion Coordinate Variable}
    (dataSet : LiteralPolymerQuaternionCubicData
      Scale Polymer Plaquette Quaternion Coordinate Variable)
    scale polymer →
  polymerQuaternionLoss dataSet scale polymer ≤ + 1 / 8
bchLossBelowOneEighth dataSet scale polymer =
  ℚP.≤-trans
    (polymerQuaternionRemainderSumBound dataSet scale polymer)
    configuredPolymerCubicBelowEighth

quaternionCubicArithmeticLevel : ProofLevel
quaternionCubicArithmeticLevel = machineChecked

quaternionFiniteEnumerationReductionLevel : ProofLevel
quaternionFiniteEnumerationReductionLevel = machineChecked

polymerQuaternionSumReductionLevel : ProofLevel
polymerQuaternionSumReductionLevel = machineChecked

literalQuaternionCoordinateAndEnumerationInputsLevel : ProofLevel
literalQuaternionCoordinateAndEnumerationInputsLevel = conditional
