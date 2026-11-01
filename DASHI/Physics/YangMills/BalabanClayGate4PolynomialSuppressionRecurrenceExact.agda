module DASHI.Physics.YangMills.BalabanClayGate4PolynomialSuppressionRecurrenceExact where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; suc) renaming (zero to zeroNat)
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Primary provenance.
--
-- Tadeusz Bałaban,
-- "Convergent Renormalization Expansions for Lattice Gauge Theories",
-- Communications in Mathematical Physics 119 (1988), 243--285.
-- DOI: 10.1007/BF01217741.
--
-- Tadeusz Bałaban,
-- "Large Field Renormalization. II. Localization, Exponentiation, and Bounds
-- for the R Operation", Communications in Mathematical Physics 122 (1989),
-- 355--392. DOI: 10.1007/BF01238433.
------------------------------------------------------------------------

record PolynomialSuppressionStep (Bound : Set) : Set₁ where
  field
    zero q polynomialRate suppressionRate : Bound
    multiply : Bound → Bound → Bound
    LessEqual : Bound → Bound → Set
    polynomialEnvelope suppression : Nat → Bound

    reflexive : ∀ value → LessEqual value value
    transitive : ∀ {left middle right} →
      LessEqual left middle → LessEqual middle right → LessEqual left right

    multiplyNonnegative : ∀ {left right} →
      LessEqual zero left → LessEqual zero right →
      LessEqual zero (multiply left right)

    multiplyMonotoneNonnegative :
      ∀ {left leftUpper right rightUpper} →
      LessEqual zero left → LessEqual zero leftUpper →
      LessEqual zero right → LessEqual zero rightUpper →
      LessEqual left leftUpper → LessEqual right rightUpper →
      LessEqual (multiply left right) (multiply leftUpper rightUpper)

    polynomialNonnegative : ∀ scale →
      LessEqual zero (polynomialEnvelope scale)
    suppressionNonnegative : ∀ scale →
      LessEqual zero (suppression scale)
    polynomialRateNonnegative : LessEqual zero polynomialRate
    suppressionRateNonnegative : LessEqual zero suppressionRate
    qNonnegative : LessEqual zero q

    polynomialStep : ∀ scale →
      LessEqual
        (polynomialEnvelope (suc scale))
        (multiply polynomialRate (polynomialEnvelope scale))

    suppressionStep : ∀ scale →
      LessEqual
        (suppression (suc scale))
        (multiply suppressionRate (suppression scale))

    rateProductBelowQ :
      LessEqual (multiply polynomialRate suppressionRate) q

    regroupStep : ∀ scale →
      multiply
        (multiply polynomialRate (polynomialEnvelope scale))
        (multiply suppressionRate (suppression scale))
      ≡ multiply
          (multiply polynomialRate suppressionRate)
          (multiply (polynomialEnvelope scale) (suppression scale))

open PolynomialSuppressionStep public

productNonnegativeAt :
  ∀ {Bound} (dataSet : PolynomialSuppressionStep Bound) scale →
  LessEqual dataSet (zero dataSet)
    (multiply dataSet
      (polynomialEnvelope dataSet scale)
      (suppression dataSet scale))
productNonnegativeAt dataSet scale =
  multiplyNonnegative dataSet
    (polynomialNonnegative dataSet scale)
    (suppressionNonnegative dataSet scale)

polynomialTimesSuppressionContracts :
  ∀ {Bound} (dataSet : PolynomialSuppressionStep Bound) scale →
  LessEqual dataSet
    (multiply dataSet
      (polynomialEnvelope dataSet (suc scale))
      (suppression dataSet (suc scale)))
    (multiply dataSet (q dataSet)
      (multiply dataSet
        (polynomialEnvelope dataSet scale)
        (suppression dataSet scale)))
polynomialTimesSuppressionContracts dataSet scale =
  transitive dataSet
    (multiplyMonotoneNonnegative dataSet
      (polynomialNonnegative dataSet (suc scale))
      (multiplyNonnegative dataSet
        (polynomialRateNonnegative dataSet)
        (polynomialNonnegative dataSet scale))
      (suppressionNonnegative dataSet (suc scale))
      (multiplyNonnegative dataSet
        (suppressionRateNonnegative dataSet)
        (suppressionNonnegative dataSet scale))
      (polynomialStep dataSet scale)
      (suppressionStep dataSet scale))
    (subst
      (λ middle → LessEqual dataSet middle
        (multiply dataSet (q dataSet)
          (multiply dataSet
            (polynomialEnvelope dataSet scale)
            (suppression dataSet scale))))
      (sym (regroupStep dataSet scale))
      (multiplyMonotoneNonnegative dataSet
        (multiplyNonnegative dataSet
          (polynomialRateNonnegative dataSet)
          (suppressionRateNonnegative dataSet))
        (qNonnegative dataSet)
        (productNonnegativeAt dataSet scale)
        (productNonnegativeAt dataSet scale)
        (rateProductBelowQ dataSet)
        (reflexive dataSet
          (multiply dataSet
            (polynomialEnvelope dataSet scale)
            (suppression dataSet scale)))))

record GeometricProductIteration
    {Bound : Set} (stepData : PolynomialSuppressionStep Bound) : Set₁ where
  field
    majorant : Nat → Bound

    productAtZeroBelowMajorant :
      LessEqual stepData
        (multiply stepData
          (polynomialEnvelope stepData zeroNat)
          (suppression stepData zeroNat))
        (majorant zeroNat)

    qScaleMonotone : ∀ {left right} →
      LessEqual stepData left right →
      LessEqual stepData
        (multiply stepData (q stepData) left)
        (multiply stepData (q stepData) right)

    majorantStep : ∀ scale →
      LessEqual stepData
        (multiply stepData (q stepData) (majorant scale))
        (majorant (suc scale))

open GeometricProductIteration public

polynomialTimesSuppressionGeometric :
  ∀ {Bound} {stepData : PolynomialSuppressionStep Bound}
    (iteration : GeometricProductIteration stepData) scale →
  LessEqual stepData
    (multiply stepData
      (polynomialEnvelope stepData scale)
      (suppression stepData scale))
    (majorant iteration scale)
polynomialTimesSuppressionGeometric iteration zeroNat =
  productAtZeroBelowMajorant iteration
polynomialTimesSuppressionGeometric {stepData = stepData}
  iteration (suc scale) =
  transitive stepData
    (polynomialTimesSuppressionContracts stepData scale)
    (transitive stepData
      (qScaleMonotone iteration
        (polynomialTimesSuppressionGeometric iteration scale))
      (majorantStep iteration scale))

polynomialSuppressionOneStepAssemblyLevel : ProofLevel
polynomialSuppressionOneStepAssemblyLevel = machineChecked

polynomialSuppressionGeometricInductionLevel : ProofLevel
polynomialSuppressionGeometricInductionLevel = machineChecked

polynomialEnvelopeRatioInputsLevel : ProofLevel
polynomialEnvelopeRatioInputsLevel = conditional

p0SuppressionRatioInputsLevel : ProofLevel
p0SuppressionRatioInputsLevel = conditional

strictGeometricRateInputsLevel : ProofLevel
strictGeometricRateInputsLevel = conditional
