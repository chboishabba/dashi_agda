module DASHI.Physics.YangMills.BalabanClayT4ConfiguredBrillouinBoxReceiptFamilyExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Product using (_×_)
open import Data.Rational using (ℚ; 0ℚ; _+_; _-_; _*_; _≤_; _<_)
open import Relation.Binary.PropositionalEquality using (subst)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayT4ConfiguredBrillouinIntegralCertificateExact as Integral
import DASHI.Physics.YangMills.BalabanClayT4PositiveDenominatorQuotientEndpointsExact as Quotient

------------------------------------------------------------------------
-- Literature normalization.
--
-- Marc Daumas, David Lester and César Muñoz,
-- "Verified Real Number Calculations: A Library for Interval Arithmetic",
-- IEEE Transactions on Computers 58 (2009), 226--237.
-- DOI: 10.1109/TC.2008.213; arXiv:0708.3721
-- Relationship: proof-producing interval arithmetic and elementary-function
-- enclosure architecture.
--
-- Tadeusz Bałaban, "Renormalization Group Approach to Lattice Gauge Field
-- Theories. I", Communications in Mathematical Physics 109 (1987), 249--301.
-- DOI: 10.1007/BF01215223
-- Relationship: Sections 4--5, pp. 281--298, and Eqs. (5.36)--(5.41) are the
-- tensor and coefficient target. Box arithmetic below certifies only the
-- regular scalar integral after the literal diagrams have been reduced.
--
-- IMPORTANT SIGN / DIVISION CORRECTION
--
-- Division by a strictly positive denominator interval cannot use the same
-- denominator endpoint for every numerator sign. Each receipt therefore
-- records the sign case of its numerator enclosure, a TYPED proof that the
-- lower denominator endpoint is positive, and the endpoint order dL<=dU.
-- The rational interval theorem in
-- BalabanClayT4PositiveDenominatorQuotientEndpointsExact proves the resulting
-- quotient enclosure for every point value satisfying the endpoint bounds.
------------------------------------------------------------------------

intervalWidth : Integral.RationalInterval → ℚ
intervalWidth interval = Integral.upper interval - Integral.lower interval

boxVolume : Integral.MomentumBox4 → ℚ
boxVolume box =
  intervalWidth (Integral.k0 box)
  * intervalWidth (Integral.k1 box)
  * intervalWidth (Integral.k2 box)
  * intervalWidth (Integral.k3 box)

record LiteralRegularBoxIntegrandData : Set₁ where
  field
    box : Integral.MomentumBox4

    denominatorLower denominatorUpper : ℚ
    numeratorLower numeratorUpper : ℚ
    integrandLower integrandUpper : ℚ
    quadratureError : ℚ

    denominatorLowerPositive : 0ℚ < denominatorLower
    denominatorBoundsOrdered : denominatorLower ≤ denominatorUpper
    denominatorEnclosureValid : Set
    numeratorTaylorEnclosureOnBox : Set

    numeratorSignCase :
      Quotient.NumeratorSignCase numeratorLower numeratorUpper

    quotientLowerCorrect :
      integrandLower
      ≡ Quotient.quotientLowerEndpoint
          numeratorSignCase denominatorLower denominatorUpper
          denominatorLowerPositive denominatorBoundsOrdered
    quotientUpperCorrect :
      integrandUpper
      ≡ Quotient.quotientUpperEndpoint
          numeratorSignCase denominatorLower denominatorUpper
          denominatorLowerPositive denominatorBoundsOrdered

    integrandEnclosureOnBox : Set
    quadratureRemainderEnclosed : Set

    lowerContribution upperContribution : ℚ
    lowerContributionDefinition :
      lowerContribution
      ≡ boxVolume box * integrandLower - quadratureError
    upperContributionDefinition :
      upperContribution
      ≡ boxVolume box * integrandUpper + quadratureError

    contributionOrdered : lowerContribution ≤ upperContribution

open LiteralRegularBoxIntegrandData public

asBoxIntegralEnclosure :
  LiteralRegularBoxIntegrandData → Integral.BoxIntegralEnclosure
asBoxIntegralEnclosure dataSet = record
  { box = box dataSet
  ; lowerContribution = lowerContribution dataSet
  ; upperContribution = upperContribution dataSet
  ; contributionOrdered = contributionOrdered dataSet
  ; denominatorPositiveOnBox = denominatorLowerPositive dataSet
  ; numeratorTaylorEnclosureOnBox =
      numeratorTaylorEnclosureOnBox dataSet
  ; integrandEnclosureOnBox = integrandEnclosureOnBox dataSet
  ; quadratureRemainderEnclosed = quadratureRemainderEnclosed dataSet
  }

mapReceipts : List LiteralRegularBoxIntegrandData →
  List Integral.BoxIntegralEnclosure
mapReceipts [] = []
mapReceipts (box ∷ boxes) = asBoxIntegralEnclosure box ∷ mapReceipts boxes

record RationalBrillouinBoxPartition : Set₁ where
  field
    infraredBoxes regularBoxData : List LiteralRegularBoxIntegrandData

    infraredNeighbourhoodRemovedExactly : Set
    regularBoxesPairwiseInteriorDisjoint : Set
    regularBoxesCoverComplementExactly : Set
    hypercubicOrbitClosureExact : Set

    everyRegularDenominatorPositive : Set
    everyRegularNumeratorEnclosed : Set
    everyRegularIntegrandEnclosed : Set
    everyRegularQuadratureRemainderEnclosed : Set

open RationalBrillouinBoxPartition public

regularBoxReceipts : RationalBrillouinBoxPartition →
  List Integral.BoxIntegralEnclosure
regularBoxReceipts dataSet = mapReceipts (regularBoxData dataSet)

singularBoxReceipts : RationalBrillouinBoxPartition →
  List Integral.BoxIntegralEnclosure
singularBoxReceipts dataSet = mapReceipts (infraredBoxes dataSet)

record LiteralBrillouinIntegralPhysicalData
    (Scale Scalar : Set) : Set₁ where
  field
    rational : ℚ → Scalar
    add multiply subtract : Scalar → Scalar → Scalar
    LessEqual : Scalar → Scalar → Set

    partition : Scale → RationalBrillouinBoxPartition

    casimirAdjoint inversePiSquared logBlocking : Scale → Scalar
    scalarIntegral regularRemainder coefficient : Scale → Scalar

    colorTensorReductionExact : (scale : Scale) → Set
    wardTransverseProjectorExact : (scale : Scale) → Set
    massAndLongitudinalTermsVanish : (scale : Scale) → Set

    infraredSingularIntegrandExact : (scale : Scale) → Set
    infraredShellIntegralLogLExact : ∀ scale →
      scalarIntegral scale
      ≡ multiply
          (multiply (rational Integral.elevenTwentyFourth)
            (casimirAdjoint scale))
          (multiply (inversePiSquared scale) (logBlocking scale))

    regularRemainderBetweenReceiptSums : ∀ scale →
      LessEqual
        (rational
          (Integral.boxLowerSum
            (regularBoxReceipts (partition scale))))
        (regularRemainder scale)

    regularRemainderBelowReceiptSum : ∀ scale →
      LessEqual (regularRemainder scale)
        (rational
          (Integral.boxUpperSum
            (regularBoxReceipts (partition scale))))

    coefficientDefinition : ∀ scale →
      coefficient scale ≡ add (scalarIntegral scale) (regularRemainder scale)

open LiteralBrillouinIntegralPhysicalData public

regularBoxCoverExact : RationalBrillouinBoxPartition → Set
regularBoxCoverExact = regularBoxesCoverComplementExactly

regularBoxEnclosuresValid :
  ∀ {Scale Scalar}
    (dataSet : LiteralBrillouinIntegralPhysicalData Scale Scalar)
    (scale : Scale) → Set
regularBoxEnclosuresValid dataSet scale =
  everyRegularDenominatorPositive (partition dataSet scale)
  × (everyRegularNumeratorEnclosed (partition dataSet scale)
  × (everyRegularIntegrandEnclosed (partition dataSet scale)
  × everyRegularQuadratureRemainderEnclosed (partition dataSet scale)))

asConfiguredBrillouinIntegralCertificate :
  ∀ {Scale Scalar} →
  LiteralBrillouinIntegralPhysicalData Scale Scalar →
  Integral.ConfiguredBrillouinIntegralCertificate Scale Scalar
asConfiguredBrillouinIntegralCertificate dataSet = record
  { rational = rational dataSet
  ; add = add dataSet
  ; multiply = multiply dataSet
  ; subtract = subtract dataSet
  ; LessEqual = LessEqual dataSet
  ; casimirAdjoint = casimirAdjoint dataSet
  ; inversePiSquared = inversePiSquared dataSet
  ; logBlocking = logBlocking dataSet
  ; scalarIntegral = scalarIntegral dataSet
  ; regularRemainder = regularRemainder dataSet
  ; coefficient = coefficient dataSet
  ; singularBoxes = λ scale → singularBoxReceipts (partition dataSet scale)
  ; regularBoxes = λ scale → regularBoxReceipts (partition dataSet scale)
  ; colorTensorReductionExact = colorTensorReductionExact dataSet
  ; wardTransverseProjectorExact = wardTransverseProjectorExact dataSet
  ; massAndLongitudinalTermsVanish = massAndLongitudinalTermsVanish dataSet
  ; infraredSingularIntegrandExact = infraredSingularIntegrandExact dataSet
  ; infraredShellIntegralLogLExact = infraredShellIntegralLogLExact dataSet
  ; regularBoxCoverExact = λ scale →
      regularBoxesCoverComplementExactly (partition dataSet scale)
  ; regularBoxEnclosuresValid = λ scale →
      regularBoxEnclosuresValid dataSet scale
  ; regularRemainderBetweenBoxSums =
      regularRemainderBetweenReceiptSums dataSet
  ; regularRemainderUpperBound = regularRemainderBelowReceiptSum dataSet
  ; coefficientDefinition = coefficientDefinition dataSet
  }

boxReceiptConstructionLevel : ProofLevel
boxReceiptConstructionLevel = machineChecked

finiteBoxFamilyAssemblyLevel : ProofLevel
finiteBoxFamilyAssemblyLevel = machineChecked

configuredIntegralAdapterLevel : ProofLevel
configuredIntegralAdapterLevel = machineChecked

literalDiagramNumeratorDenominatorAndQuadratureInputsLevel : ProofLevel
literalDiagramNumeratorDenominatorAndQuadratureInputsLevel = conditional
