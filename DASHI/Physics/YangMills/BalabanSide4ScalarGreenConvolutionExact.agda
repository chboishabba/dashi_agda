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
  using (sumRationalRightScale)
open import DASHI.Physics.YangMills.BalabanPath4SU2RationalMatrixCoordinatesExact
  using (deltaSumIdentity; siteElementsDuplicateFree; kroneckerDelta)
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
    (siteSum4Cong
      (λ column → scalarGreenKernel (subtractSite4 row column))
      (kernelColumn row)
      (λ column → kernelColumnSymmetry row column))
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

laplacianFourFoldRaw : ∀ a0 a1 a2 a3 →
  a0 + (a1 + (a2 + (a3 + 0ℚ))) ≡ a0 + a1 + a2 + a3
laplacianFourFoldRaw = ℚRing.solve-∀

kernelLaplacianFoldExact : ∀ offset →
  kernelLaplacianFold offset ≡ scalarKernelLaplacian offset
kernelLaplacianFoldExact offset =
  laplacianFourFoldRaw
    (kernelAxisLaplacian axis0 offset)
    (kernelAxisLaplacian axis1 offset)
    (kernelAxisLaplacian axis2 offset)
    (kernelAxisLaplacian axis3 offset)

siteLocalLaplacian : SiteField side4 → SiteField side4
siteLocalLaplacian fld site =
  sumRational (allCyclicIndices four) (λ axis →
    (fld site + fld site)
    - (fld (shiftForward4 axis site)
      + fld (shiftBackward4 axis site)))

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
    (sumRationalCong (allCyclicIndices four)
      (λ axis →
        (kernelColumn center site + kernelColumn center site)
        - (kernelColumn center (shiftForward4 axis site)
          + kernelColumn center (shiftBackward4 axis site)))
      (λ axis → kernelAxisLaplacian axis (subtractSite4 site center))
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

stencilEmptyRaw : 0ℚ ≡ (0ℚ + 0ℚ) - (0ℚ + 0ℚ)
stencilEmptyRaw = ℚRing.solve-∀

stencilStepRaw : ∀ c f b w sc sf sb →
  ((c + c) - (f + b)) * w + ((sc + sc) - (sf + sb))
  ≡ ((c * w + sc) + (c * w + sc)) - ((f * w + sf) + (b * w + sb))
stencilStepRaw = ℚRing.solve-∀

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
sumStencilDistribute [] center forward backward weight = stencilEmptyRaw
sumStencilDistribute (value ∷ values) center forward backward weight
  rewrite sumStencilDistribute values center forward backward weight =
  stencilStepRaw
    (center value) (forward value) (backward value) (weight value)
    (sumRational values (λ v → center v * weight v))
    (sumRational values (λ v → forward v * weight v))
    (sumRational values (λ v → backward v * weight v))

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

axisLaplacianGreenExact : (axis : Axis4) (source : SiteField side4) (row : PhysicalBlockL side4) →
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
    (siteSum4Cong
      (λ column →
        ((scalarGreenKernel (subtractSite4 row column)
            + scalarGreenKernel (subtractSite4 row column))
          - (scalarGreenKernel (subtractSite4 (shiftForward4 axis row) column)
            + scalarGreenKernel (subtractSite4 (shiftBackward4 axis row) column)))
        * source column)
      (λ column →
        kernelAxisLaplacian axis (subtractSite4 row column) * source column)
      (λ column →
        cong (λ coefficient → coefficient * source column)
          (kernelAxisStencilAtDifference axis row column)))

siteGreenLaplacianExact : (source : SiteField side4) (row : PhysicalBlockL side4) →
  siteLocalLaplacian (scalarGreen source) row
  ≡ siteSum4 (λ column →
      scalarKernelLaplacian (subtractSite4 row column) * source column)
siteGreenLaplacianExact source row =
  trans
    (sumRationalCong (allCyclicIndices four)
      (λ axis →
        (scalarGreen source row + scalarGreen source row)
        - (scalarGreen source (shiftForward4 axis row)
          + scalarGreen source (shiftBackward4 axis row)))
      (λ axis →
        siteSum4 (λ column →
          kernelAxisLaplacian axis (subtractSite4 row column) * source column))
      (λ axis → axisLaplacianGreenExact axis source row))
    (trans
      (sumSwap (allCyclicIndices four) (physicalBlockSites side4)
        (λ axis column →
          kernelAxisLaplacian axis (subtractSite4 row column)
          * source column))
      (siteSum4Cong
        (λ column →
          sumRational (allCyclicIndices four) (λ axis →
            kernelAxisLaplacian axis (subtractSite4 row column) * source column))
        (λ column →
          scalarKernelLaplacian (subtractSite4 row column) * source column)
        (λ column →
          trans
            (sumRationalRightScale
              (allCyclicIndices four)
              (λ axis → kernelAxisLaplacian axis
                (subtractSite4 row column))
              (source column))
            (cong (λ value → value * source column)
              (kernelLaplacianFoldExact (subtractSite4 row column))))))

addSubCancelMulRaw : ∀ a b v → a * v ≡ ((a + b) - b) * v
addSubCancelMulRaw = ℚRing.solve-∀

kernelLaplacianTimesExact : ∀ offset value →
  scalarKernelLaplacian offset * value
  ≡ (scalarDeltaAtZero offset - oneTwoFiftySix) * value
kernelLaplacianTimesExact offset value =
  trans
    (addSubCancelMulRaw (scalarKernelLaplacian offset) oneTwoFiftySix value)
    (cong (λ equationLeft → (equationLeft - oneTwoFiftySix) * value)
      (scalarGreenKernelEquation offset))

deltaEmptyRaw : ∀ k → 0ℚ ≡ 0ℚ - k * 0ℚ
deltaEmptyRaw = ℚRing.solve-∀

deltaStepRaw : ∀ d k s sd ss →
  (d - k) * s + (sd - k * ss) ≡ (d * s + sd) - k * (s + ss)
deltaStepRaw = ℚRing.solve-∀

sumDeltaMinusConstant :
  ∀ {A : Set} (values : List A) (delta source : A → ℚ) constant →
  sumRational values (λ value →
    (delta value - constant) * source value)
  ≡ sumRational values (λ value → delta value * source value)
    - constant * sumRational values source
sumDeltaMinusConstant [] delta source constant = deltaEmptyRaw constant
sumDeltaMinusConstant (value ∷ values) delta source constant
  rewrite sumDeltaMinusConstant values delta source constant =
  deltaStepRaw
    (delta value) constant (source value)
    (sumRational values (λ v → delta v * source v))
    (sumRational values source)

siteDeltaEqualsKronecker : ∀ left right →
  siteDelta4 left right
  ≡ kroneckerDelta (periodicTorus4DecidableEquality four) left right
siteDeltaEqualsKronecker left right
  with periodicTorus4DecidableEquality four left right
... | yes equality = refl
... | no inequality = refl

siteDeltaConvolutionExact : (row : PhysicalBlockL side4) (source : SiteField side4) →
  siteSum4 (λ column → siteDelta4 row column * source column)
  ≡ source row
siteDeltaConvolutionExact row source =
  trans
    (siteSum4Cong
      (λ column → siteDelta4 row column * source column)
      (λ column →
        kroneckerDelta (periodicTorus4DecidableEquality four) row column
        * source column)
      (λ column →
        cong (λ coefficient → coefficient * source column)
          (siteDeltaEqualsKronecker row column)))
    (deltaSumIdentity
      (periodicTorus4DecidableEquality four)
      siteElementsDuplicateFree
      row
      (complete (periodicTorus4Finite four) row)
      source)

siteGreenLaplacianIdentity : (source : SiteField side4) (row : PhysicalBlockL side4) →
  siteLocalLaplacian (scalarGreen source) row
  ≡ source row - oneTwoFiftySix * siteSum4 source
siteGreenLaplacianIdentity source row =
  trans
    (siteGreenLaplacianExact source row)
    (trans
      (siteSum4Cong
        (λ column →
          scalarKernelLaplacian (subtractSite4 row column) * source column)
        (λ column →
          (siteDelta4 row column - oneTwoFiftySix) * source column)
        (λ column →
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

oneMulLeftRaw : ∀ x → 1ℚ * x ≡ x
oneMulLeftRaw = ℚRing.solve-∀

siteSumGreenExact : (source : SiteField side4) → siteSum4 (scalarGreen source) ≡ siteSum4 source
siteSumGreenExact source =
  trans
    (sumSwap (physicalBlockSites side4) (physicalBlockSites side4)
      (λ row column →
        scalarGreenKernel (subtractSite4 row column) * source column))
    (siteSum4Cong
      (λ column →
        siteSum4 (λ row →
          scalarGreenKernel (subtractSite4 row column) * source column))
      source
      (λ column →
        trans
          (sumRationalRightScale
            (physicalBlockSites side4)
            (λ row → scalarGreenKernel (subtractSite4 row column))
            (source column))
          (trans
            (cong (λ value → value * source column)
              (translatedKernelTotal column))
            (oneMulLeftRaw (source column)))))

averageScalarGreenExact : (source : SiteField side4) (row : PhysicalBlockL side4) →
  average0123 (scalarGreen source) row
  ≡ oneTwoFiftySix * siteSum4 source
averageScalarGreenExact source row =
  trans
    (average0123EqualsGlobalMean (scalarGreen source) row)
    (cong (oneTwoFiftySix *_) (siteSumGreenExact source))

configuredSiteOperator : SiteField side4 → SiteField side4
configuredSiteOperator fld row =
  siteLocalLaplacian fld row + average0123 fld row

subAddCancelRaw : ∀ a b → (a - b) + b ≡ a
subAddCancelRaw = ℚRing.solve-∀

configuredSiteGreenRightInverse : (source : SiteField side4) (row : PhysicalBlockL side4) →
  configuredSiteOperator (scalarGreen source) row ≡ source row
configuredSiteGreenRightInverse source row =
  trans
    (cong₂ _+_
      (siteGreenLaplacianIdentity source row)
      (averageScalarGreenExact source row))
    (subAddCancelRaw (source row) (oneTwoFiftySix * siteSum4 source))

------------------------------------------------------------------------
-- Input-side shifts and commutation, giving the left inverse as well.
------------------------------------------------------------------------

scalarGreenRespectsPointwise : ∀ {left right : SiteField side4} →
  (∀ site → left site ≡ right site) →
  ∀ row → scalarGreen left row ≡ scalarGreen right row
scalarGreenRespectsPointwise {left} {right} pointwise row =
  siteSum4Cong
    (λ column → scalarGreenKernel (subtractSite4 row column) * left column)
    (λ column → scalarGreenKernel (subtractSite4 row column) * right column)
    (λ column →
      cong (λ value → scalarGreenKernel (subtractSite4 row column) * value)
        (pointwise column))

distribLeftRaw : ∀ a b c → a * (b + c) ≡ a * b + a * c
distribLeftRaw = ℚRing.solve-∀

scalarGreenAdd : (left right : SiteField side4) (row : PhysicalBlockL side4) →
  scalarGreen (λ site → left site + right site) row
  ≡ scalarGreen left row + scalarGreen right row
scalarGreenAdd left right row =
  trans
    (siteSum4Cong
      (λ column → scalarGreenKernel (subtractSite4 row column) * (left column + right column))
      (λ column →
        scalarGreenKernel (subtractSite4 row column) * left column
        + scalarGreenKernel (subtractSite4 row column) * right column)
      (λ column →
        distribLeftRaw
          (scalarGreenKernel (subtractSite4 row column))
          (left column)
          (right column)))
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
      (oneMulLeftRaw constant))

shiftedInputForwardSum : (axis : Axis4) (source : SiteField side4) (row : PhysicalBlockL side4) →
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
    (siteSum4Cong
      (λ column →
        scalarGreenKernel (subtractSite4 row (shiftBackward4 axis column))
        * source column)
      (λ column →
        scalarGreenKernel (shiftForward4 axis (subtractSite4 row column))
        * source column)
      (λ column →
        cong (λ offset → scalarGreenKernel offset * source column)
          (subtractSiteRightBackward axis row column)))

shiftedInputBackwardSum : (axis : Axis4) (source : SiteField side4) (row : PhysicalBlockL side4) →
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
    (siteSum4Cong
      (λ column →
        scalarGreenKernel (subtractSite4 row (shiftForward4 axis column))
        * source column)
      (λ column →
        scalarGreenKernel (shiftBackward4 axis (subtractSite4 row column))
        * source column)
      (λ column →
        cong (λ offset → scalarGreenKernel offset * source column)
          (subtractSiteRightForward axis row column)))

stencilLeftStepRaw : ∀ w c f b sc sf sb →
  w * ((c + c) - (f + b)) + ((sc + sc) - (sf + sb))
  ≡ ((w * c + sc) + (w * c + sc)) - ((w * f + sf) + (w * b + sb))
stencilLeftStepRaw = ℚRing.solve-∀

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
sumStencilWeightLeft [] weight center forward backward = stencilEmptyRaw
sumStencilWeightLeft (value ∷ values) weight center forward backward
  rewrite sumStencilWeightLeft values weight center forward backward =
  stencilLeftStepRaw
    (weight value) (center value) (forward value) (backward value)
    (sumRational values (λ v → weight v * center v))
    (sumRational values (λ v → weight v * forward v))
    (sumRational values (λ v → weight v * backward v))

axisInputLaplacianGreenExact : (axis : Axis4) (source : SiteField side4) (row : PhysicalBlockL side4) →
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
    (siteSum4Cong
      (λ column →
        scalarGreenKernel (subtractSite4 row column)
        * sumRational values (λ value → terms value column))
      (λ column →
        sumRational values (λ value →
          scalarGreenKernel (subtractSite4 row column) * terms value column))
      (λ column →
        sym (sumRationalScale
          (scalarGreenKernel (subtractSite4 row column))
          values
          (λ value → terms value column))))
    (sumSwap (physicalBlockSites side4) values
      (λ column value →
        scalarGreenKernel (subtractSite4 row column) * terms value column))

siteGreenLaplacianCommutes : (source : SiteField side4) (row : PhysicalBlockL side4) →
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
      (sumRationalCong (allCyclicIndices four)
        (λ axis →
          scalarGreen
            (λ site →
              (source site + source site)
              - (source (shiftForward4 axis site)
                + source (shiftBackward4 axis site)))
            row)
        (λ axis →
          siteSum4 (λ column →
            kernelAxisLaplacian axis (subtractSite4 row column) * source column))
        (λ axis → axisInputLaplacianGreenExact axis source row))
      (sym
        (sumRationalCong (allCyclicIndices four)
          (λ axis →
            (scalarGreen source row + scalarGreen source row)
            - (scalarGreen source (shiftForward4 axis row)
              + scalarGreen source (shiftBackward4 axis row)))
          (λ axis →
            siteSum4 (λ column →
              kernelAxisLaplacian axis (subtractSite4 row column) * source column))
          (λ axis → axisLaplacianGreenExact axis source row))))

scalarGreenAverageExact : (source : SiteField side4) (row : PhysicalBlockL side4) →
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

configuredSiteGreenCommutes : (source : SiteField side4) (row : PhysicalBlockL side4) →
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

configuredSiteGreenLeftInverse : (source : SiteField side4) (row : PhysicalBlockL side4) →
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
