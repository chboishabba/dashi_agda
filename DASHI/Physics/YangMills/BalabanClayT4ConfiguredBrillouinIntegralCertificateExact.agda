module DASHI.Physics.YangMills.BalabanClayT4ConfiguredBrillouinIntegralCertificateExact where

open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Equality using (_≡_)
open import Data.Integer.Base using (+_)
open import Data.Rational using (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_; _≤_; _/_)
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Literature normalization.
--
-- Tadeusz Bałaban, "Renormalization Group Approach to Lattice Gauge Field
-- Theories. I. Generation of Effective Actions in a Small Field Approximation
-- and a Coupling Constant Renormalization in Four Dimensions",
-- Communications in Mathematical Physics 109 (1987), 249--301.
-- DOI: 10.1007/BF01215223
-- Relationship: Sections 4--5 and Eq. (5.36) are the primary lattice
-- vacuum-polarization tensor and normalization comparison target.
--
-- Roger Dashen and David J. Gross, "Relationship between Lattice and Continuum
-- Definitions of the Gauge-Theory Coupling", Physical Review D 23 (1981),
-- 2340--2344. DOI: 10.1103/PhysRevD.23.2340
-- Relationship: Wilson-action background-field normalization calibration.
--
-- Luis F. Abbott, "The Background Field Method Beyond One Loop", Nuclear
-- Physics B 185 (1981), 189--203. DOI: 10.1016/0550-3213(81)90371-0
-- Relationship: background-field Ward structure and gauge-invariant coupling
-- extraction.
------------------------------------------------------------------------

oneThird elevenThird elevenTwentyFourth : ℚ
oneThird = + 1 / 3
elevenThird = + 11 / 3
elevenTwentyFourth = + 11 / 24

betaZeroToInverseCouplingCoefficient : ∀ casimirAdjoint →
  (elevenThird * casimirAdjoint) * (+ 1 / 8)
  ≡ elevenTwentyFourth * casimirAdjoint
betaZeroToInverseCouplingCoefficient = ℚRing.solve-∀

record RationalInterval : Set where
  constructor interval
  field
    lower upper : ℚ
    ordered : lower ≤ upper

open RationalInterval public

record MomentumBox4 : Set where
  constructor momentumBox4
  field
    k0 k1 k2 k3 : RationalInterval

open MomentumBox4 public

sumℚ : List ℚ → ℚ
sumℚ [] = 0ℚ
sumℚ (value ∷ values) = value + sumℚ values

record BoxIntegralEnclosure : Set₁ where
  field
    box : MomentumBox4
    lowerContribution upperContribution : ℚ
    contributionOrdered : lowerContribution ≤ upperContribution
    denominatorPositiveOnBox : Set
    numeratorTaylorEnclosureOnBox : Set
    integrandEnclosureOnBox : Set
    quadratureRemainderEnclosed : Set

open BoxIntegralEnclosure public

boxLowerSum boxUpperSum : List BoxIntegralEnclosure → ℚ
boxLowerSum [] = 0ℚ
boxLowerSum (certificate ∷ certificates) =
  lowerContribution certificate + boxLowerSum certificates
boxUpperSum [] = 0ℚ
boxUpperSum (certificate ∷ certificates) =
  upperContribution certificate + boxUpperSum certificates

record ConfiguredBrillouinIntegralCertificate
    (Scale Scalar : Set) : Set₁ where
  field
    rational : ℚ → Scalar
    add multiply subtract : Scalar → Scalar → Scalar
    LessEqual : Scalar → Scalar → Set

    casimirAdjoint inversePiSquared logBlocking : Scale → Scalar
    scalarIntegral regularRemainder coefficient : Scale → Scalar

    singularBoxes regularBoxes : Scale → List BoxIntegralEnclosure

    -- Agda 2.9 cannot infer the domain of a binder whose codomain is the
    -- universe `Set` and whose body does not otherwise mention the binder.
    -- Keep the source API unchanged but state the physical scale type
    -- explicitly.  These are propositions indexed by the same RG scale.
    colorTensorReductionExact : (scale : Scale) → Set
    wardTransverseProjectorExact : (scale : Scale) → Set
    massAndLongitudinalTermsVanish : (scale : Scale) → Set

    infraredSingularIntegrandExact : (scale : Scale) → Set
    infraredShellIntegralLogLExact : ∀ scale →
      scalarIntegral scale
      ≡ multiply
          (multiply (rational elevenTwentyFourth)
            (casimirAdjoint scale))
          (multiply (inversePiSquared scale) (logBlocking scale))

    regularBoxCoverExact : (scale : Scale) → Set
    regularBoxEnclosuresValid : (scale : Scale) → Set
    regularRemainderBetweenBoxSums : ∀ scale →
      LessEqual (rational (boxLowerSum (regularBoxes scale)))
        (regularRemainder scale)

    regularRemainderUpperBound : ∀ scale →
      LessEqual (regularRemainder scale)
        (rational (boxUpperSum (regularBoxes scale)))

    coefficientDefinition : ∀ scale →
      coefficient scale
      ≡ add (scalarIntegral scale) (regularRemainder scale)

open ConfiguredBrillouinIntegralCertificate public

vacuumPolarizationPlaquetteCoefficientConfigured :
  ∀ {Scale Scalar}
    (dataSet : ConfiguredBrillouinIntegralCertificate Scale Scalar)
    scale →
  coefficient dataSet scale
  ≡ add dataSet
      (multiply dataSet
        (multiply dataSet
          (rational dataSet elevenTwentyFourth)
          (casimirAdjoint dataSet scale))
        (multiply dataSet
          (inversePiSquared dataSet scale)
          (logBlocking dataSet scale)))
      (regularRemainder dataSet scale)
vacuumPolarizationPlaquetteCoefficientConfigured dataSet scale =
  trans
    (coefficientDefinition dataSet scale)
    (cong
      (λ singular → add dataSet singular (regularRemainder dataSet scale))
      (infraredShellIntegralLogLExact dataSet scale))

record ConfiguredOneLoopRGClosure
    (Scale Scalar : Set) : Set₁ where
  field
    integralCertificate : ConfiguredBrillouinIntegralCertificate Scale Scalar
    inverseCouplingSq nextInverseCouplingSq quarticRemainder : Scale → Scalar

    runningCouplingDefinition : ∀ scale →
      nextInverseCouplingSq scale
      ≡ add integralCertificate
          (inverseCouplingSq scale)
          (add integralCertificate
            (coefficient integralCertificate scale)
            (quarticRemainder scale))

    quarticRemainderSummable : Set

open ConfiguredOneLoopRGClosure public

physicalRunningCouplingRecursionConfigured = runningCouplingDefinition

universalColorCoefficientArithmeticLevel : ProofLevel
universalColorCoefficientArithmeticLevel = machineChecked

brillouinBoxSummationReductionLevel : ProofLevel
brillouinBoxSummationReductionLevel = machineChecked

configuredPlaquetteCoefficientAssemblyLevel : ProofLevel
configuredPlaquetteCoefficientAssemblyLevel = machineChecked

literalDiagramAndBoxCertificateInputsLevel : ProofLevel
literalDiagramAndBoxCertificateInputsLevel = conditional