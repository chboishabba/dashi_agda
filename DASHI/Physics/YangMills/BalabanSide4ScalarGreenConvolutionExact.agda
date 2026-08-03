module DASHI.Physics.YangMills.BalabanSide4ScalarGreenConvolutionExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational using (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_; -_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
import Relation.Nullary.Decidable.Core as StdDec
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier
open import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreCarrier using
  (PhysicalBlockL; physicalBlockSites)
open import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact using
  (SiteField; sumRational; sumRationalCong; sumRationalScale)
open import DASHI.Physics.YangMills.BalabanFiniteSumFubiniExact using
  (sumRationalAdd; sumSwap)
open import DASHI.Physics.YangMills.BalabanPath4AxisAverageExact using
  (side4; average0123)
open import DASHI.Physics.YangMills.BalabanConfiguredSide4PeriodicReindexingExact
  using
    ( shiftForward4
    ; shiftBackward4
    ; forwardAfterBackward4
    ; backwardAfterForward4
    ; siteSum4
    ; periodicForwardReindexing
    ; periodicBackwardReindexing
    )
open import DASHI.Physics.YangMills.BalabanConfiguredSide4PeriodicVectorCalculusExact
  using (axis0; axis1; axis2; axis3; siteSum4Cong)
open import DASHI.Physics.YangMills.BalabanConstructiveRationalMatrixInverseExact
  using (sumRationalRightScale; kroneckerDelta)
open import DASHI.Physics.YangMills.BalabanPath4SU2RationalMatrixCoordinatesExact
  using (deltaSumIdentity; siteElementsDuplicateFree)
open import DASHI.Physics.YangMills.BalabanPath4GlobalAverageExact
  using (average0123EqualsGlobalMean)
open import DASHI.Physics.YangMills.BalabanSide4ScalarGreenKernelComputed
open import DASHI.Physics.YangMills.BalabanSide4TranslationDifferenceExact
open import DASHI.Physics.YangMills.BalabanSide4TranslationConvolutionExact
open import DASHI.Physics.YangMills.BalabanSide4TranslationSymmetryExact

------------------------------------------------------------------------
-- Evenness and symmetry of the exact Fourier kernel.
------------------------------------------------------------------------

KernelEven : PhysicalBlockL side4 → Set
KernelEven offset = scalarGreenKernel (negateSite4 offset) ≡ scalarGreenKernel offset

kernelEvenDecision : ∀ offset → StdDec.Dec (KernelEven offset)
kernelEvenDecision offset =
  ℚP._≟_ (scalarGreenKernel (negateSite4 offset)) (scalarGreenKernel offset)

allKernelEvenDecision :
  StdDec.Dec (All KernelEven (physicalBlockSites side4))
allKernelEvenDecision = decideAll kernelEvenDecision (physicalBlockSites side4)

allKernelEvenDecisionIsYes : IsYes allKernelEvenDecision
allKernelEvenDecisionIsYes = isYes

allKernelEven : All KernelEven (physicalBlockSites side4)
allKernelEven = extractYes allKernelEvenDecision allKernelEvenDecisionIsYes

scalarGreenKernelEven : ∀ offset → KernelEven offset
scalarGreenKernelEven offset =
  lookupAll (complete (periodicTorus4Finite four) offset) allKernelEven

kernelColumn : PhysicalBlockL side4 → SiteField side4
kernelColumn center site = scalarGreenKernel (subtractSite4 site center)

kernelColumnSymmetry : ∀ left right →
  kernelColumn right left ≡ kernelColumn left right
kernelColumnSymmetry left right =
  trans
    (cong scalarGreenKernel (subtractSiteSwapNegate left right))
    (scalarGreenKernelEven (subtractSite4 right left))

translatedKernelTotal : ∀ center → siteSum4 (kernelColumn center) ≡ 1ℚ
translatedKernelTotal center =
  trans
    (siteSumSubtractInvariant center scalarGreenKernel)
    scalarGreenKernelTotalExact

kernelRowTotal : ∀ row →
  siteSum4 (λ column → scalarGreenKernel (subtractSite4 row column)) ≡ 1ℚ
kernelRowTotal row =
  trans
    (siteSum4Cong _ _ (λ column → kernelColumnSymmetry row column))
    (translatedKernelTotal row)

------------------------------------------------------------------------
-- Translation of the checked local kernel equation.
------------------------------------------------------------------------

kernelAxisLaplacian :
  Axis4 → PhysicalBlockL side4 → ℚ
kernelAxisLaplacian axis offset =
  (scalarGreenKernel offset + scalarGreenKernel offset)
  - (scalarGreenKernel (shiftForward4 axis offset)
    + scalarGreenKernel (shiftBackward4 axis offset))

kernelLaplacianFold : PhysicalBlockL side4 → ℚ
kernelLaplacianFold offset =
  sumRational (allCyclicIndices four)
    (λ axis → kernelAxisLaplacian axis offset)

kernelLaplacianFoldExact : ∀ offset →
  kernelLaplacianFold offset ≡ scalarKernelLaplacian offset
kernelLaplacianFoldExact offset =
  ℚRing.solve-∀

siteLocalLaplacian : SiteField side4 → SiteField side4
siteLocalLaplacian field site =
  sumRational (allCyclicIndices four) (λ axis →
    (field site + field site)
    - (field (shiftForward4 axis site)
      + field (shiftBackward4 axis site)))

kernelColumnAxisLaplacianExact : ∀ axis center site →
  (kernelColumn center site + kernelColumn center site)
    - (kernelColumn center (shiftForward4 axis site)
      + kernelColumn center (shiftBackward4 axis site))
  ≡ kernelAxisLaplacian axis (subtractSite4 site center)
kernelColumnAxisLaplacianExact axis center site =
  cong₂ _-_
    refl
    (cong₂ _+_
      (cong scalarGreenKernel (subtractSiteForward axis site center))
      (cong scalarGreenKernel (subtractSiteBackward axis site center)))

kernelColumnLocalLaplacianExact : ∀ center site →
  siteLocalLaplacian (kernelColumn center) site
  ≡ scalarKernelLaplacian (subtractSite4 site center)
kernelColumnLocalLaplacianExact center site =
  trans
    (sumRationalCong (allCyclicIndices four) _ _
      (λ axis → kernelColumnAxisLaplacianExact axis center site))
    (kernelLaplacianFoldExact (subtractSite4 site center))

translatedKernelEquation : ∀ center site →
  siteLocalLaplacian (kernelColumn center) site + oneTwoFiftySix
  ≡ siteDelta4 site center
translatedKernelEquation center site =
  trans
    (cong (λ value → value + oneTwoFiftySix)
      (kernelColumnLocalLaplacianExact center site))
    (trans
      (scalarGreenKernelEquation (subtractSite4 site center))
      (scalarDeltaAtZeroSubtract site center))

------------------------------------------------------------------------
-- Exact convolution and right inverse.
------------------------------------------------------------------------

scalarGreen : SiteField side4 → SiteField side4
scalarGreen source row =
  siteSum4 (λ column →
    scalarGreenKernel (subtractSite4 row column) * source column)

sumStencilDistribute :
  ∀ {A : Set} (values : List A)
    (center forward backward weight : A → ℚ) →
  sumRational values (λ value →
    ((center value + center value)
      - (forward value + backward value)) * weight value)
  ≡ (sumRational values (λ value → center value * weight value)
      + sumRational values (λ value → center value * weight value))
    - (sumRational values (λ value → forward value * weight value)
      + sumRational values (λ value → backward value * weight value))
sumStencilDistribute [] center forward backward weight = ℚRing.solve-∀
sumStencilDistribute (value ∷ values) center forward backward weight
  rewrite sumStencilDistribute values center forward backward weight =
  ℚRing.solve-∀

kernelAxisStencilAtDifference : ∀ axis row column →
  ((scalarGreenKernel (subtractSite4 row column)
      + scalarGreenKernel (subtractSite4 row column))
    - (scalarGreenKernel
        (subtractSite4 (shiftForward4 axis row) column)
      + scalarGreenKernel
        (subtractSite4 (shiftBackward4 axis row) column)))
  ≡ kernelAxisLaplacian axis (subtractSite4 row column)
kernelAxisStencilAtDifference axis row column =
  cong₂ _-_
    refl
    (cong₂ _+_
      (cong scalarGreenKernel (subtractSiteForward axis row column))
      (cong scalarGreenKernel (subtractSiteBackward axis row column)))

axisLaplacianGreenExact : ∀ axis source row →
  ((scalarGreen source row + scalarGreen source row)
    - (scalarGreen source (shiftForward4 axis row)
      + scalarGreen source (shiftBackward4 axis row)))
  ≡ siteSum4 (λ column →
      kernelAxisLaplacian axis (subtractSite4 row column) * source column)
axisLaplacianGreenExact axis source row =
  trans
    (sym
      (sumStencilDistribute
        (physicalBlockSites side4)
        (λ column → scalarGreenKernel (subtractSite4 row column))
        (λ column → scalarGreenKernel
          (subtractSite4 (shiftForward4 axis row) column))
        (λ column → scalarGreenKernel
          (subtractSite4 (shiftBackward4 axis row) column))
        source))
    (siteSum4Cong _ _ (λ column →
      cong (λ coefficient → coefficient * source column)
        (kernelAxisStencilAtDifference axis row column)))

siteGreenLaplacianExact : ∀ source row →
  siteLocalLaplacian (scalarGreen source) row
  ≡ siteSum4 (λ column →
      scalarKernelLaplacian (subtractSite4 row column) * source column)
siteGreenLaplacianExact source row =
  trans
    (sumRationalCong (allCyclicIndices four) _ _
      (λ axis → axisLaplacianGreenExact axis source row))
    (trans
      (sumSwap (allCyclicIndices four) (physicalBlockSites side4)
        (λ axis column →
          kernelAxisLaplacian axis (subtractSite4 row column)
          * source column))
      (siteSum4Cong _ _ (λ column →
        trans
          (sumRationalRightScale
            (allCyclicIndices four)
            (λ axis → kernelAxisLaplacian axis
              (subtractSite4 row column))
            (source column))
          (cong (λ value → value * source column)
            (kernelLaplacianFoldExact (subtractSite4 row column))))))

kernelLaplacianTimesExact : ∀ offset value →
  scalarKernelLaplacian offset * value
  ≡ (scalarDeltaAtZero offset - oneTwoFiftySix) * value
kernelLaplacianTimesExact offset value =
  trans
    (ℚRing.solve-∀)
    (cong (λ equationLeft → (equationLeft - oneTwoFiftySix) * value)
      (scalarGreenKernelEquation offset))

sumDeltaMinusConstant :
  ∀ {A : Set} (values : List A) (delta source : A → ℚ) constant →
  sumRational values (λ value →
    (delta value - constant) * source value)
  ≡ sumRational values (λ value → delta value * source value)
    - constant * sumRational values source
sumDeltaMinusConstant [] delta source constant = ℚRing.solve-∀
sumDeltaMinusConstant (value ∷ values) delta source constant
  rewrite sumDeltaMinusConstant values delta source constant =
  ℚRing.solve-∀

siteDeltaEqualsKronecker : ∀ left right →
  siteDelta4 left right
  ≡ kroneckerDelta (periodicTorus4DecidableEquality four) left right
siteDeltaEqualsKronecker left right
  with periodicTorus4DecidableEquality four left right
... | yes equality = refl
... | no inequality = refl

siteDeltaConvolutionExact : ∀ row source →
  siteSum4 (λ column → siteDelta4 row column * source column)
  ≡ source row
siteDeltaConvolutionExact row source =
  trans
    (siteSum4Cong _ _ (λ column →
      cong (λ coefficient → coefficient * source column)
        (siteDeltaEqualsKronecker row column)))
    (deltaSumIdentity
      (periodicTorus4DecidableEquality four)
      siteElementsDuplicateFree
      row
      (complete (periodicTorus4Finite four) row)
      source)

siteGreenLaplacianIdentity : ∀ source row →
  siteLocalLaplacian (scalarGreen source) row
  ≡ source row - oneTwoFiftySix * siteSum4 source
siteGreenLaplacianIdentity source row =
  trans
    (siteGreenLaplacianExact source row)
    (trans
      (siteSum4Cong _ _ (λ column →
        trans
          (kernelLaplacianTimesExact
            (subtractSite4 row column) (source column))
          (cong (λ delta → (delta - oneTwoFiftySix) * source column)
            (scalarDeltaAtZeroSubtract row column))))
      (trans
        (sumDeltaMinusConstant
          (physicalBlockSites side4)
          (siteDelta4 row)
          source
          oneTwoFiftySix)
        (cong (λ value → value - oneTwoFiftySix * siteSum4 source)
          (siteDeltaConvolutionExact row source))))

siteSumGreenExact : ∀ source → siteSum4 (scalarGreen source) ≡ siteSum4 source
siteSumGreenExact source =
  trans
    (sumSwap (physicalBlockSites side4) (physicalBlockSites side4)
      (λ row column →
        scalarGreenKernel (subtractSite4 row column) * source column))
    (siteSum4Cong _ _ (λ column →
      trans
        (sumRationalRightScale
          (physicalBlockSites side4)
          (λ row → scalarGreenKernel (subtractSite4 row column))
          (source column))
        (trans
          (cong (λ value → value * source column)
            (translatedKernelTotal column))
          (ℚRing.solve-∀))))

averageScalarGreenExact : ∀ source row →
  average0123 (scalarGreen source) row
  ≡ oneTwoFiftySix * siteSum4 source
averageScalarGreenExact source row =
  trans
    (average0123EqualsGlobalMean (scalarGreen source) row)
    (cong (oneTwoFiftySix *_) (siteSumGreenExact source))

configuredSiteOperator : SiteField side4 → SiteField side4
configuredSiteOperator field row =
  siteLocalLaplacian field row + average0123 field row

configuredSiteGreenRightInverse : ∀ source row →
  configuredSiteOperator (scalarGreen source) row ≡ source row
configuredSiteGreenRightInverse source row =
  trans
    (cong₂ _+_
      (siteGreenLaplacianIdentity source row)
      (averageScalarGreenExact source row))
    (ℚRing.solve-∀)

------------------------------------------------------------------------
-- Input-side shifts and commutation, giving the left inverse as well.
------------------------------------------------------------------------

scalarGreenRespectsPointwise : ∀ {left right} →
  (∀ site → left site ≡ right site) →
  ∀ row → scalarGreen left row ≡ scalarGreen right row
scalarGreenRespectsPointwise pointwise row =
  siteSum4Cong _ _ (λ column →
    cong (λ value → scalarGreenKernel (subtractSite4 row column) * value)
      (pointwise column))

scalarGreenAdd : ∀ left right row →
  scalarGreen (λ site → left site + right site) row
  ≡ scalarGreen left row + scalarGreen right row
scalarGreenAdd left right row =
  trans
    (siteSum4Cong _ _ (λ column → ℚRing.solve-∀))
    (sumRationalAdd (physicalBlockSites side4)
      (λ column → scalarGreenKernel (subtractSite4 row column) * left column)
      (λ column → scalarGreenKernel (subtractSite4 row column) * right column))

scalarGreenConstantExact : ∀ constant row →
  scalarGreen (λ _ → constant) row ≡ constant
scalarGreenConstantExact constant row =
  trans
    (sumRationalRightScale
      (physicalBlockSites side4)
      (λ column → scalarGreenKernel (subtractSite4 row column))
      constant)
    (trans
      (cong (λ value → value * constant) (kernelRowTotal row))
      (ℚRing.solve-∀))

shiftedInputForwardSum : ∀ axis source row →
  scalarGreen (λ site → source (shiftForward4 axis site)) row
  ≡ siteSum4 (λ column →
      scalarGreenKernel
        (shiftForward4 axis (subtractSite4 row column))
      * source column)
shiftedInputForwardSum axis source row =
  trans
    (sym
      (periodicForwardReindexing axis (λ column →
        scalarGreenKernel
          (subtractSite4 row (shiftBackward4 axis column))
        * source column)))
    (siteSum4Cong _ _ (λ column →
      cong (λ offset → scalarGreenKernel offset * source column)
        (subtractSiteRightBackward axis row column)))

shiftedInputBackwardSum : ∀ axis source row →
  scalarGreen (λ site → source (shiftBackward4 axis site)) row
  ≡ siteSum4 (λ column →
      scalarGreenKernel
        (shiftBackward4 axis (subtractSite4 row column))
      * source column)
shiftedInputBackwardSum axis source row =
  trans
    (sym
      (periodicBackwardReindexing axis (λ column →
        scalarGreenKernel
          (subtractSite4 row (shiftForward4 axis column))
        * source column)))
    (siteSum4Cong _ _ (λ column →
      cong (λ offset → scalarGreenKernel offset * source column)
        (subtractSiteRightForward axis row column)))

sumStencilWeightLeft :
  ∀ {A : Set} (values : List A)
    (weight center forward backward : A → ℚ) →
  sumRational values (λ value →
    weight value * ((center value + center value)
      - (forward value + backward value)))
  ≡ (sumRational values (λ value → weight value * center value)
      + sumRational values (λ value → weight value * center value))
    - (sumRational values (λ value → weight value * forward value)
      + sumRational values (λ value → weight value * backward value))
sumStencilWeightLeft [] weight center forward backward = ℚRing.solve-∀
sumStencilWeightLeft (value ∷ values) weight center forward backward
  rewrite sumStencilWeightLeft values weight center forward backward =
  ℚRing.solve-∀

axisInputLaplacianGreenExact : ∀ axis source row →
  scalarGreen (λ site →
    (source site + source site)
    - (source (shiftForward4 axis site)
      + source (shiftBackward4 axis site))) row
  ≡ siteSum4 (λ column →
      kernelAxisLaplacian axis (subtractSite4 row column) * source column)
axisInputLaplacianGreenExact axis source row =
  trans
    (sumStencilWeightLeft
      (physicalBlockSites side4)
      (λ column → scalarGreenKernel (subtractSite4 row column))
      source
      (λ column → source (shiftForward4 axis column))
      (λ column → source (shiftBackward4 axis column)))
    (trans
      (cong₂ _-_
        (cong₂ _+_ refl refl)
        (cong₂ _+_
          (shiftedInputForwardSum axis source row)
          (shiftedInputBackwardSum axis source row)))
      (trans
        (sym
          (sumStencilDistribute
            (physicalBlockSites side4)
            (λ column → scalarGreenKernel (subtractSite4 row column))
            (λ column → scalarGreenKernel
              (shiftForward4 axis (subtractSite4 row column)))
            (λ column → scalarGreenKernel
              (shiftBackward4 axis (subtractSite4 row column)))
            source))
        refl))

scalarGreenFiniteSum :
  ∀ {A : Set} (values : List A) (terms : A → SiteField side4) row →
  scalarGreen (λ site → sumRational values (λ value → terms value site)) row
  ≡ sumRational values (λ value → scalarGreen (terms value) row)
scalarGreenFiniteSum values terms row =
  trans
    (siteSum4Cong _ _ (λ column →
      sym (sumRationalScale
        (scalarGreenKernel (subtractSite4 row column))
        values
        (λ value → terms value column))))
    (sumSwap (physicalBlockSites side4) values
      (λ column value →
        scalarGreenKernel (subtractSite4 row column) * terms value column))

siteGreenLaplacianCommutes : ∀ source row →
  scalarGreen (siteLocalLaplacian source) row
  ≡ siteLocalLaplacian (scalarGreen source) row
siteGreenLaplacianCommutes source row =
  trans
    (scalarGreenFiniteSum
      (allCyclicIndices four)
      (λ axis site →
        (source site + source site)
        - (source (shiftForward4 axis site)
          + source (shiftBackward4 axis site)))
      row)
    (trans
      (sumRationalCong (allCyclicIndices four) _ _
        (λ axis → axisInputLaplacianGreenExact axis source row))
      (sym
        (trans
          (sumRationalCong (allCyclicIndices four) _ _
            (λ axis → axisLaplacianGreenExact axis source row))
          refl))

scalarGreenAverageExact : ∀ source row →
  scalarGreen (average0123 source) row
  ≡ average0123 (scalarGreen source) row
scalarGreenAverageExact source row =
  trans
    (scalarGreenRespectsPointwise
      (average0123EqualsGlobalMean source) row)
    (trans
      (scalarGreenConstantExact
        (oneTwoFiftySix * siteSum4 source) row)
      (sym (averageScalarGreenExact source row)))

configuredSiteGreenCommutes : ∀ source row →
  scalarGreen (configuredSiteOperator source) row
  ≡ configuredSiteOperator (scalarGreen source) row
configuredSiteGreenCommutes source row =
  trans
    (scalarGreenAdd
      (siteLocalLaplacian source)
      (average0123 source)
      row)
    (cong₂ _+_
      (siteGreenLaplacianCommutes source row)
      (scalarGreenAverageExact source row))

configuredSiteGreenLeftInverse : ∀ source row →
  scalarGreen (configuredSiteOperator source) row ≡ source row
configuredSiteGreenLeftInverse source row =
  trans
    (configuredSiteGreenCommutes source row)
    (configuredSiteGreenRightInverse source row)

side4ScalarGreenRightInverseLevel : ProofLevel
side4ScalarGreenRightInverseLevel = machineChecked

side4ScalarGreenCommutationLevel : ProofLevel
side4ScalarGreenCommutationLevel = machineChecked

side4ScalarGreenLeftInverseLevel : ProofLevel
side4ScalarGreenLeftInverseLevel = machineChecked
