module DASHI.Physics.YangMills.BalabanClayGate4BackgroundGaugeMixedNormExact where

open import Agda.Builtin.Equality using (_≡_)
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Repository realization of Bałaban's mixed gauge-correction norm.
--
-- Tadeusz Bałaban,
-- "Spaces of Regular Gauge Field Configurations on a Lattice and Gauge Fixing
-- Conditions", Communications in Mathematical Physics 99 (1985), 75--102.
-- DOI: 10.1007/BF01466594.
--
-- The source norm combines a site-field size and a negative/derivative norm.
-- The selected repository shape is
--
--   ||lambda-mu||_bg
--     = ||lambda-mu||_infinity
--       + L ||D(lambda-mu)||_infinity.
--
-- The scale factor is retained abstractly, but the complete metric triangle is
-- derived from the two component triangles and one additive interchange law.
------------------------------------------------------------------------

record MixedGaugeNormAlgebra (Parameter Bound : Set) : Set₁ where
  field
    add : Bound → Bound → Bound
    LessEqual : Bound → Bound → Set

    fieldDistance derivativeDistance : Parameter → Parameter → Bound
    scaleDerivative : Bound → Bound

    reflexive : ∀ value → LessEqual value value
    transitive : ∀ {left middle right} →
      LessEqual left middle → LessEqual middle right → LessEqual left right

    addMonotone : ∀ {left leftUpper right rightUpper} →
      LessEqual left leftUpper → LessEqual right rightUpper →
      LessEqual (add left right) (add leftUpper rightUpper)

    fieldTriangle : ∀ left middle right →
      LessEqual
        (fieldDistance left right)
        (add (fieldDistance left middle)
          (fieldDistance middle right))

    scaledDerivativeTriangle : ∀ left middle right →
      LessEqual
        (scaleDerivative (derivativeDistance left right))
        (add
          (scaleDerivative (derivativeDistance left middle))
          (scaleDerivative (derivativeDistance middle right)))

    addInterchange : ∀ a b c d →
      add (add a b) (add c d)
      ≡ add (add a c) (add b d)

open MixedGaugeNormAlgebra public

mixedGaugeDistance :
  ∀ {Parameter Bound} →
  MixedGaugeNormAlgebra Parameter Bound →
  Parameter → Parameter → Bound
mixedGaugeDistance algebra left right =
  add algebra
    (fieldDistance algebra left right)
    (scaleDerivative algebra
      (derivativeDistance algebra left right))

mixedGaugeDistanceTriangle :
  ∀ {Parameter Bound}
    (algebra : MixedGaugeNormAlgebra Parameter Bound)
    left middle right →
  LessEqual algebra
    (mixedGaugeDistance algebra left right)
    (add algebra
      (mixedGaugeDistance algebra left middle)
      (mixedGaugeDistance algebra middle right))
mixedGaugeDistanceTriangle algebra left middle right =
  subst
    (λ upper → LessEqual algebra
      (mixedGaugeDistance algebra left right) upper)
    (sym (addInterchange algebra
      (fieldDistance algebra left middle)
      (fieldDistance algebra middle right)
      (scaleDerivative algebra
        (derivativeDistance algebra left middle))
      (scaleDerivative algebra
        (derivativeDistance algebra middle right))))
    (addMonotone algebra
      (fieldTriangle algebra left middle right)
      (scaledDerivativeTriangle algebra left middle right))

record GaugeFixingForcingIdentification
    {Configuration Parameter Bound : Set}
    (algebra : MixedGaugeNormAlgebra Parameter Bound) : Set₁ where
  field
    configuration : Configuration
    zeroCorrection fixedPointAtZero : Parameter

    alpha0 alpha1 B0Prime B1 eight : Bound
    multiply addBound : Bound → Bound → Bound

    forcingSize : Bound
    forcingSizeMeaning :
      forcingSize
      ≡ mixedGaugeDistance algebra fixedPointAtZero zeroCorrection

    sourceForcingUpper : Bound
    sourceForcingUpperMeaning :
      sourceForcingUpper
      ≡ multiply eight
          (multiply B0Prime
            (multiply B1 (addBound alpha0 alpha1)))

    LessEqualBound : Bound → Bound → Set
    forcingBelowSourceUpper :
      LessEqualBound forcingSize sourceForcingUpper

open GaugeFixingForcingIdentification public

backgroundGaugeMixedNormTriangleLevel : ProofLevel
backgroundGaugeMixedNormTriangleLevel = machineChecked

physicalBackgroundGaugeComponentNormInputsLevel : ProofLevel
physicalBackgroundGaugeComponentNormInputsLevel = conditional

physicalBackgroundGaugeForcingIdentificationInputsLevel : ProofLevel
physicalBackgroundGaugeForcingIdentificationInputsLevel = conditional
