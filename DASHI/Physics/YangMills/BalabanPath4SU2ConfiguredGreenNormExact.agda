module DASHI.Physics.YangMills.BalabanPath4SU2ConfiguredGreenNormExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Integer.Base using (+_)
open import Data.List.Base using (map; length)
open import Data.Rational using
  (ℚ; 0ℚ; _+_; _-_; _*_; _≤_; _/_; NonNegative; nonNegative)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
import Relation.Nullary.Decidable.Core as StdDec
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier
open import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreCarrier using
  (physicalBlockSites)
open import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact using
  (natAsRational; sumRational; sumRationalCong; sumRationalScale)
open import DASHI.Physics.YangMills.BalabanFiniteSumFubiniExact using (sumSwap)
open import DASHI.Physics.YangMills.BalabanBoolean4BlockPoincareExact using
  (sq; squareNonnegative; baseBelowBasePlusRemainder)
open import DASHI.Physics.YangMills.BalabanPath4AxisAverageExact using (side4)
open import DASHI.Physics.YangMills.BalabanPath4PhysicalVarianceDecompositionExact
  using (globalNormSq)
open import DASHI.Physics.YangMills.BalabanPath4DirectionalEnergyContractionExact
  using (sumRationalMonotone)
open import DASHI.Physics.YangMills.BalabanPath4BondHodgeCoercivityExact
  using (bondComponent; bondNormSq)
open import DASHI.Physics.YangMills.BalabanPath4SU2PhysicalTangentExact
open import DASHI.Physics.YangMills.BalabanPath4SU2RationalMatrixDimensionExact
  using (lengthMapExact; siteCountExact)
open import DASHI.Physics.YangMills.BalabanFiniteRationalCauchyExact
  using (sumSquares; sumNonnegative; finiteRationalCauchy)
open import DASHI.Physics.YangMills.BalabanSide4ScalarGreenKernelComputed
open import DASHI.Physics.YangMills.BalabanSide4TranslationDifferenceExact
  using (subtractSite4; siteSumSubtractInvariant)
open import DASHI.Physics.YangMills.BalabanSide4ScalarGreenConvolutionExact
  using (scalarGreen)
open import DASHI.Physics.YangMills.BalabanPath4SU2ConfiguredGreenExact
  using (configuredPhysicalGreen)
open import DASHI.Physics.YangMills.BalabanConstructiveRationalMatrixInverseExact
  using (sumRationalRightScale)

------------------------------------------------------------------------
-- Closed exact square-sum of the side-four Green kernel.
------------------------------------------------------------------------

twoFiftySix sixteen oneSixteenth : ℚ
twoFiftySix = + 256 / 1
sixteen = + 16 / 1
oneSixteenth = + 1 / 16

kernelSquareSum kernelSquareValue kernelSquareGap : ℚ
kernelSquareSum = siteSum4 (λ offset → sq (scalarGreenKernel offset))
kernelSquareValue = + 2571041 / 80281600
kernelSquareGap = + 2446559 / 80281600

KernelSquareValueExact : Set
KernelSquareValueExact = kernelSquareSum ≡ kernelSquareValue

kernelSquareValueDecision : StdDec.Dec KernelSquareValueExact
kernelSquareValueDecision = ℚP._≟_ kernelSquareSum kernelSquareValue

kernelSquareValueDecisionIsYes : IsYes kernelSquareValueDecision
kernelSquareValueDecisionIsYes = isYes

kernelSquareSumExact : KernelSquareValueExact
kernelSquareSumExact =
  extractYes kernelSquareValueDecision kernelSquareValueDecisionIsYes

kernelSquareGapNonnegative : 0ℚ ≤ kernelSquareGap
kernelSquareGapNonnegative =
  let
    instance
      gapNonnegative : NonNegative kernelSquareGap
      gapNonnegative = ℚP.normalize-nonNeg 2446559 80281600
  in
  ℚP.nonNegative⁻¹ kernelSquareGap

kernelSquareValuePlusGap :
  kernelSquareValue + kernelSquareGap ≡ oneSixteenth
kernelSquareValuePlusGap = ℚRing.solve-∀

kernelSquareSumBelowOneSixteenth : kernelSquareSum ≤ oneSixteenth
kernelSquareSumBelowOneSixteenth =
  subst
    (λ left → left ≤ oneSixteenth)
    (sym kernelSquareSumExact)
    (subst
      (λ right → kernelSquareValue ≤ right)
      kernelSquareValuePlusGap
      (baseBelowBasePlusRemainder
        kernelSquareValue kernelSquareGap kernelSquareGapNonnegative))

translatedKernelSquareTotal : ∀ center →
  siteSum4 (λ row → sq (scalarGreenKernel (subtractSite4 row center)))
  ≡ kernelSquareSum
translatedKernelSquareTotal center =
  siteSumSubtractInvariant center (λ offset → sq (scalarGreenKernel offset))

------------------------------------------------------------------------
-- Pointwise finite Cauchy bound.
------------------------------------------------------------------------

greenTerms : SiteField side4 → PhysicalBlockL side4 → List ℚ
greenTerms source row =
  map (λ column →
    scalarGreenKernel (subtractSite4 row column) * source column)
    (physicalBlockSites side4)

sumMappedExact : ∀ {A : Set} (values : List A) (term : A → ℚ) →
  sumRational (map term values) (λ value → value)
  ≡ sumRational values term
sumMappedExact [] term = refl
sumMappedExact (value ∷ values) term
  rewrite sumMappedExact values term = refl

sumMappedSquaresExact : ∀ {A : Set} (values : List A) (term : A → ℚ) →
  sumSquares (map term values)
  ≡ sumRational values (λ value → sq (term value))
sumMappedSquaresExact [] term = refl
sumMappedSquaresExact (value ∷ values) term
  rewrite sumMappedSquaresExact values term = refl

greenTermsSumExact : ∀ source row →
  sumRational (greenTerms source row) (λ value → value)
  ≡ scalarGreen source row
greenTermsSumExact source row =
  sumMappedExact (physicalBlockSites side4)
    (λ column → scalarGreenKernel (subtractSite4 row column) * source column)

greenTermsSquaresExact : ∀ source row →
  sumSquares (greenTerms source row)
  ≡ siteSum4 (λ column →
      sq (scalarGreenKernel (subtractSite4 row column) * source column))
greenTermsSquaresExact source row =
  sumMappedSquaresExact (physicalBlockSites side4)
    (λ column → scalarGreenKernel (subtractSite4 row column) * source column)

greenTermsCountExact : ∀ source row →
  natAsRational (length (greenTerms source row)) ≡ twoFiftySix
greenTermsCountExact source row =
  trans
    (cong natAsRational
      (lengthMapExact
        (λ column → scalarGreenKernel (subtractSite4 row column) * source column)
        (physicalBlockSites side4)))
    (trans (cong natAsRational siteCountExact) refl)

greenPointwiseCauchy : ∀ source row →
  sq (scalarGreen source row)
  ≤ twoFiftySix * siteSum4 (λ column →
      sq (scalarGreenKernel (subtractSite4 row column) * source column))
greenPointwiseCauchy source row =
  subst
    (λ left → left ≤
      natAsRational (length (greenTerms source row))
        * sumSquares (greenTerms source row))
    (cong sq (greenTermsSumExact source row))
    (subst
      (λ right → sq (scalarGreen source row) ≤ right)
      (trans
        (cong₂ _*_
          (greenTermsCountExact source row)
          (greenTermsSquaresExact source row))
        refl)
      (finiteRationalCauchy (greenTerms source row)))

------------------------------------------------------------------------
-- Sum the pointwise estimate and collapse the translated kernel square.
------------------------------------------------------------------------

doubleKernelSquareExact : ∀ source →
  siteSum4 (λ row →
    siteSum4 (λ column →
      sq (scalarGreenKernel (subtractSite4 row column) * source column)))
  ≡ kernelSquareSum * globalNormSq source
doubleKernelSquareExact source =
  trans
    (siteSum4Cong _ _ (λ row →
      siteSum4Cong _ _ (λ column → ℚRing.solve-∀
        (scalarGreenKernel (subtractSite4 row column))
        (source column))))
    (trans
      (sumSwap (physicalBlockSites side4) (physicalBlockSites side4)
        (λ row column →
          sq (scalarGreenKernel (subtractSite4 row column))
          * sq (source column)))
      (trans
        (siteSum4Cong _ _ (λ column →
          trans
            (sumRationalRightScale
              (physicalBlockSites side4)
              (λ row → sq (scalarGreenKernel (subtractSite4 row column)))
              (sq (source column)))
            (cong (λ coefficient → coefficient * sq (source column))
              (translatedKernelSquareTotal column))))
        (sumRationalScale kernelSquareSum
          (physicalBlockSites side4) (λ column → sq (source column)))))

globalNormNonnegative : ∀ source → 0ℚ ≤ globalNormSq source
globalNormNonnegative source =
  sumNonnegative (physicalBlockSites side4) (λ site → sq (source site))
    (λ site → squareNonnegative (source site))

scalarGreenNormFirstBound : ∀ source →
  globalNormSq (scalarGreen source)
  ≤ twoFiftySix * (kernelSquareSum * globalNormSq source)
scalarGreenNormFirstBound source =
  trans
    (sumRationalMonotone
      (physicalBlockSites side4)
      (λ row → sq (scalarGreen source row))
      (λ row → twoFiftySix * siteSum4 (λ column →
        sq (scalarGreenKernel (subtractSite4 row column) * source column)))
      (greenPointwiseCauchy source))
    (trans
      (sumRationalScale twoFiftySix (physicalBlockSites side4)
        (λ row → siteSum4 (λ column →
          sq (scalarGreenKernel (subtractSite4 row column) * source column))))
      (cong (twoFiftySix *_) (doubleKernelSquareExact source)))

scalarGreenCoefficientBound : ∀ source →
  twoFiftySix * (kernelSquareSum * globalNormSq source)
  ≤ sixteen * globalNormSq source
scalarGreenCoefficientBound source =
  let
    instance
      normNonnegative : NonNegative (globalNormSq source)
      normNonnegative = nonNegative (globalNormNonnegative source)

      coefficientNonnegative : NonNegative twoFiftySix
      coefficientNonnegative = ℚP.normalize-nonNeg 256 1
  in
  trans
    (ℚP.*-monoˡ-≤-nonNeg twoFiftySix
      (ℚP.*-monoʳ-≤-nonNeg (globalNormSq source)
        kernelSquareSumBelowOneSixteenth))
    (ℚRing.solve-∀ (globalNormSq source))

scalarGreenNormBound : ∀ source →
  globalNormSq (scalarGreen source) ≤ sixteen * globalNormSq source
scalarGreenNormBound source =
  trans (scalarGreenNormFirstBound source) (scalarGreenCoefficientBound source)

------------------------------------------------------------------------
-- Four bond axes and three Lie-algebra components.
------------------------------------------------------------------------

configuredGreenBondNormBound : ∀ source component →
  bondNormSq (configuredPhysicalGreen source component)
  ≤ sixteen * bondNormSq (source component)
configuredGreenBondNormBound source component =
  trans
    (sumRationalMonotone
      (allCyclicIndices four)
      (λ axis → globalNormSq
        (bondComponent (configuredPhysicalGreen source component) axis))
      (λ axis → sixteen * globalNormSq
        (bondComponent (source component) axis))
      (λ axis → scalarGreenNormBound
        (bondComponent (source component) axis)))
    (sumRationalScale sixteen (allCyclicIndices four)
      (λ axis → globalNormSq (bondComponent (source component) axis)))

configuredPhysicalGreenNormBound : ∀ source →
  physicalUnweightedNormSq (configuredPhysicalGreen source)
  ≤ sixteen * physicalUnweightedNormSq source
configuredPhysicalGreenNormBound source =
  trans
    (ℚP.+-mono-≤
      (configuredGreenBondNormBound source component1)
      (ℚP.+-mono-≤
        (configuredGreenBondNormBound source component2)
        (configuredGreenBondNormBound source component3)))
    (ℚRing.solve-∀
      (bondNormSq (source component1))
      (bondNormSq (source component2))
      (bondNormSq (source component3)))

side4GreenKernelSquareBoundLevel : ProofLevel
side4GreenKernelSquareBoundLevel = machineChecked

side4ScalarGreenNormLevel : ProofLevel
side4ScalarGreenNormLevel = machineChecked

configuredPhysicalGreenNormLevel : ProofLevel
configuredPhysicalGreenNormLevel = machineChecked
