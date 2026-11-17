module DASHI.Physics.YangMills.BalabanPath13NativeIntegerPoincareBridgeExact where

------------------------------------------------------------------------
-- Native integer Path13 certificate -> ordinary rational Poincare floor.
--
-- Provenance:
--   Balaban, T. (1985), "Propagators and Renormalization Group",
--   Communications in Mathematical Physics 99, 75-102.
--   DOI: 10.1007/BF01212359.
--
-- Formal reconstruction:
--   The huge closed certificate never enters normalized Data.Rational arithmetic.
--   It is interpreted in ℚᵘ, where denominators are carried without gcd/division.
--   Only the final order statement is transported back through toℚᵘ-cancel-≤.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Integer using (ℤ; +_; +0; +[1+_]; -[1+_]; -_)
import Data.Integer as ℤ
open import Data.Product using (_×_; _,_)
open import Data.Rational using (ℚ; 0ℚ; _+_; _*_; _-_; -_; _≤_; toℚᵘ)
import Data.Rational.Properties as RP
import Data.Rational.Unnormalised.Base as U
open import Data.Rational.Unnormalised.Base
  using (ℚᵘ; 0ℚᵘ; 1ℚᵘ; _≃_; *≡*; NonNegative; Positive; mkℚᵘ)
  renaming (_+_ to _+ᵘ_; _*_ to _*ᵘ_; -_ to -ᵘ_; _/_ to _/ᵘ_; _≤_ to _≤ᵘ_)
import Data.Rational.Unnormalised.Properties as UP
import Data.Rational.Unnormalised.Tactic.RingSolver as URing
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanPath13GeneratedLDLDataExact public
open import DASHI.Physics.YangMills.BalabanPath13NativeIntegerCoefficientDataExact
open import DASHI.Physics.YangMills.BalabanPath13NativeIntegerCoefficientCertificateExact
import DASHI.Physics.YangMills.BalabanIntegerTriangularUnnormalisedCompilerExact as C
open import DASHI.Physics.YangMills.BalabanPath13NativeIntegerAttachmentExact

------------------------------------------------------------------------
-- Nonnegative integer-weight SOS residual.
------------------------------------------------------------------------

squareNonnegativeU : ∀ x → 0ℚᵘ ≤ᵘ (x *ᵘ x)
squareNonnegativeU (mkℚᵘ +0 d) =
  let instance
      productNonnegative : NonNegative (mkℚᵘ +0 d *ᵘ mkℚᵘ +0 d)
      productNonnegative = U.nonNeg
  in UP.nonNegative⁻¹ (mkℚᵘ +0 d *ᵘ mkℚᵘ +0 d)
squareNonnegativeU (mkℚᵘ +[1+ n ] d) =
  let instance
      productNonnegative : NonNegative (mkℚᵘ +[1+ n ] d *ᵘ mkℚᵘ +[1+ n ] d)
      productNonnegative = U.nonNeg
  in UP.nonNegative⁻¹ (mkℚᵘ +[1+ n ] d *ᵘ mkℚᵘ +[1+ n ] d)
squareNonnegativeU (mkℚᵘ -[1+ n ] d) =
  let instance
      productNonnegative : NonNegative (mkℚᵘ -[1+ n ] d *ᵘ mkℚᵘ -[1+ n ] d)
      productNonnegative = U.nonNeg
  in UP.nonNegative⁻¹ (mkℚᵘ -[1+ n ] d *ᵘ mkℚᵘ -[1+ n ] d)

weightedSquareNonnegativeU : ∀ weight coefficients coordinates →
  NonNegative (C.embedZ weight) →
  0ℚᵘ ≤ᵘ
    C.embedZ weight *ᵘ
      (C.dotZU coefficients coordinates *ᵘ C.dotZU coefficients coordinates)
weightedSquareNonnegativeU weight coefficients coordinates weightNonnegative =
  let
    dot = C.dotZU coefficients coordinates
    instance
      weightNN : NonNegative (C.embedZ weight)
      weightNN = weightNonnegative
      squareNN : NonNegative (dot *ᵘ dot)
      squareNN = U.nonNegative (squareNonnegativeU dot)
      productNN : NonNegative (C.embedZ weight *ᵘ (dot *ᵘ dot))
      productNN = UP.nonNeg*nonNeg⇒nonNeg (C.embedZ weight) (dot *ᵘ dot)
  in UP.nonNegative⁻¹ (C.embedZ weight *ᵘ (dot *ᵘ dot))

data AllWeightsNonnegative : List (ℤ × List ℤ) → Set where
  all[] : AllWeightsNonnegative []
  all∷ : ∀ {weight coefficients rest} →
    NonNegative (C.embedZ weight) →
    AllWeightsNonnegative rest →
    AllWeightsNonnegative ((weight , coefficients) ∷ rest)

sumWeightedNonnegativeU : ∀ {families} →
  AllWeightsNonnegative families →
  ∀ coordinates →
  0ℚᵘ ≤ᵘ C.sumWeightedSquareValuesZU families coordinates
sumWeightedNonnegativeU all[] coordinates = UP.≤-refl
sumWeightedNonnegativeU (all∷ {weight} {coefficients} {rest} weightNN restNN) coordinates =
  let
    term = C.embedZ weight *ᵘ
      (C.dotZU coefficients coordinates *ᵘ C.dotZU coefficients coordinates)
    tail = C.sumWeightedSquareValuesZU rest coordinates
    instance
      termNN : NonNegative term
      termNN = U.nonNegative (weightedSquareNonnegativeU weight coefficients coordinates weightNN)
      tailNN : NonNegative tail
      tailNN = U.nonNegative (sumWeightedNonnegativeU restNN coordinates)
      totalNN : NonNegative (term +ᵘ tail)
      totalNN = UP.nonNeg+nonNeg⇒nonNeg term tail
  in UP.nonNegative⁻¹ (term +ᵘ tail)

scaledLDLWeightsNonnegative : AllWeightsNonnegative scaledLDLFamiliesZ
scaledLDLWeightsNonnegative =
  all∷ U.nonNeg (
  all∷ U.nonNeg (
  all∷ U.nonNeg (
  all∷ U.nonNeg (
  all∷ U.nonNeg (
  all∷ U.nonNeg (
  all∷ U.nonNeg (
  all∷ U.nonNeg (
  all∷ U.nonNeg (
  all∷ U.nonNeg (
  all∷ U.nonNeg (
  all∷ U.nonNeg all[])))))))))))

------------------------------------------------------------------------
-- Certificate equality and order extraction in ℚᵘ.
------------------------------------------------------------------------

scaleKU scaleMU eighteenU oneEighteenthU : ℚᵘ
scaleKU = C.embedZ scaleKZ
scaleMU = C.embedZ scaleMZ
eighteenU = (+ 18) /ᵘ 1
oneEighteenthU = (+ 1) /ᵘ 18

instance
  scaleKUPositive : Positive scaleKU
  scaleKUPositive = U.pos
  eighteenUPositive : Positive eighteenU
  eighteenUPositive = U.pos

negativeScaleKEmbedding :
  C.embedZ (neg 70100214151882488833120838983750438907686861074695467566355130758678976489785281281004080)
  ≃ -ᵘ scaleKU
negativeScaleKEmbedding = UP.≃-reflexive refl

scaledGapEval : ∀ c →
  C.evalTriZU scaledGapTriZ (coordinatesU c)
  ≃ scaleMU *ᵘ toℚᵘ (path13Energy c)
    +ᵘ (-ᵘ scaleKU) *ᵘ toℚᵘ (path13NormSq c)
scaledGapEval c =
  UP.≃-trans
    (C.evalAddZU
      (QuadZ.scaleTriZ scaleMZ energyTriZ)
      (QuadZ.scaleTriZ
        (neg 70100214151882488833120838983750438907686861074695467566355130758678976489785281281004080)
        normTriZ)
      (coordinatesU c))
    (UP.+-cong
      (UP.≃-trans
        (C.evalScaleZU scaleMZ energyTriZ (coordinatesU c))
        (UP.*-cong (UP.≃-refl {scaleMU}) (energyEvalToQ c)))
      (UP.≃-trans
        (C.evalScaleZU
          (neg 70100214151882488833120838983750438907686861074695467566355130758678976489785281281004080)
          normTriZ
          (coordinatesU c))
        (UP.*-cong negativeScaleKEmbedding (normEvalToQ c))))
  where
  import DASHI.Physics.YangMills.BalabanIntegerTriangularQuadraticCertificateExact as QuadZ

scaledLDLEval : ∀ c →
  C.evalTriZU scaledLDLTriZ (coordinatesU c)
  ≃ C.sumWeightedSquareValuesZU scaledLDLFamiliesZ (coordinatesU c)
scaledLDLEval c = C.sumWeightedSquareCompilerZU scaledLDLFamiliesZ (coordinatesU c)

scaledGapToResidual : ∀ c →
  scaleMU *ᵘ toℚᵘ (path13Energy c)
    +ᵘ (-ᵘ scaleKU) *ᵘ toℚᵘ (path13NormSq c)
  ≃ C.sumWeightedSquareValuesZU scaledLDLFamiliesZ (coordinatesU c)
scaledGapToResidual c =
  UP.≃-trans
    (UP.≃-sym (scaledGapEval c))
    (UP.≃-trans
      (UP.≃-reflexive
        (cong (λ quadratic → C.evalTriZU quadratic (coordinatesU c))
          scaledIntegerCoefficientCertificate))
      (scaledLDLEval c))

scaledGapNonnegative : ∀ c →
  0ℚᵘ ≤ᵘ
    scaleMU *ᵘ toℚᵘ (path13Energy c)
      +ᵘ (-ᵘ scaleKU) *ᵘ toℚᵘ (path13NormSq c)
scaledGapNonnegative c =
  UP.≤-respʳ-≃
    (UP.≃-sym (scaledGapToResidual c))
    (sumWeightedNonnegativeU scaledLDLWeightsNonnegative (coordinatesU c))

gapAsDifference : ∀ energyValue normValue →
  scaleMU *ᵘ energyValue +ᵘ (-ᵘ scaleKU) *ᵘ normValue
  ≃ scaleMU *ᵘ energyValue +ᵘ (-ᵘ (scaleKU *ᵘ normValue))
gapAsDifference = URing.solve-∀

scaleKTimesNormBelowScaleMTimesEnergy : ∀ c →
  scaleKU *ᵘ toℚᵘ (path13NormSq c)
  ≤ᵘ scaleMU *ᵘ toℚᵘ (path13Energy c)
scaleKTimesNormBelowScaleMTimesEnergy c =
  UP.0≤q-p⇒p≤q
    (UP.≤-respʳ-≃
      (gapAsDifference
        (toℚᵘ (path13Energy c))
        (toℚᵘ (path13NormSq c)))
      (scaledGapNonnegative c))

scaleMFactorZ : scaleMZ ≡ ℤ._*_ scaleKZ (+ 18)
scaleMFactorZ = refl

scaleMFactorU : scaleMU ≃ scaleKU *ᵘ eighteenU
scaleMFactorU =
  UP.≃-reflexive
    (trans
      (cong C.embedZ scaleMFactorZ)
      (C.embedZ-* scaleKZ (+ 18)))

factorScaleM : ∀ energyValue →
  scaleMU *ᵘ energyValue
  ≃ scaleKU *ᵘ (eighteenU *ᵘ energyValue)
factorScaleM energyValue =
  UP.≃-trans
    (UP.*-cong scaleMFactorU (UP.≃-refl {energyValue}))
    (UP.*-assoc scaleKU eighteenU energyValue)

normBelowEighteenEnergy : ∀ c →
  toℚᵘ (path13NormSq c)
  ≤ᵘ eighteenU *ᵘ toℚᵘ (path13Energy c)
normBelowEighteenEnergy c =
  UP.*-cancelˡ-≤-pos scaleKU
    (UP.≤-respʳ-≃
      (factorScaleM (toℚᵘ (path13Energy c)))
      (scaleKTimesNormBelowScaleMTimesEnergy c))

eighteenTimesOneEighteenth : eighteenU *ᵘ oneEighteenthU ≃ 1ℚᵘ
eighteenTimesOneEighteenth = *≡* refl

eighteenUndo : ∀ x →
  eighteenU *ᵘ (oneEighteenthU *ᵘ x) ≃ x
eighteenUndo x =
  UP.≃-trans
    (UP.≃-sym (UP.*-assoc eighteenU oneEighteenthU x))
    (UP.≃-trans
      (UP.*-cong eighteenTimesOneEighteenth (UP.≃-refl {x}))
      (UP.*-identityˡ x))

oneEighteenthNormBelowEnergyU : ∀ c →
  oneEighteenthU *ᵘ toℚᵘ (path13NormSq c)
  ≤ᵘ toℚᵘ (path13Energy c)
oneEighteenthNormBelowEnergyU c =
  UP.*-cancelˡ-≤-pos eighteenU
    (UP.≤-respˡ-≃
      (UP.≃-sym (eighteenUndo (toℚᵘ (path13NormSq c))))
      (normBelowEighteenEnergy c))

oneEighteenthToU : toℚᵘ oneEighteenth ≃ oneEighteenthU
oneEighteenthToU = UP.≃-reflexive refl

normalizedLeftToU : ∀ c →
  toℚᵘ (oneEighteenth * path13NormSq c)
  ≃ oneEighteenthU *ᵘ toℚᵘ (path13NormSq c)
normalizedLeftToU c =
  UP.≃-trans
    (RP.toℚᵘ-homo-* oneEighteenth (path13NormSq c))
    (UP.*-cong oneEighteenthToU (UP.≃-refl {toℚᵘ (path13NormSq c)}))

path13Poincare : ∀ c → oneEighteenth * path13NormSq c ≤ path13Energy c
path13Poincare c =
  RP.toℚᵘ-cancel-≤
    (UP.≤-respˡ-≃
      (UP.≃-sym (normalizedLeftToU c))
      (oneEighteenthNormBelowEnergyU c))

path13NativeIntegerCertificateLevel : ProofLevel
path13NativeIntegerCertificateLevel = machineChecked

path13CoefficientCertificateLevel : ProofLevel
path13CoefficientCertificateLevel = machineChecked
