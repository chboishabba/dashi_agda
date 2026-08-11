module DASHI.Physics.YangMills.BalabanSelectedBackgroundGaugeGreenDecayExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- J. M. Combes and L. Thomas,
-- "Asymptotic Behaviour of Eigenfunctions for Multiparticle Schrödinger
-- Operators", Communications in Mathematical Physics 34 (1973), 251--270.
-- DOI: 10.1007/BF01646473.
--
-- Tadeusz Bałaban,
-- "Propagators for Lattice Gauge Theories in a Background Field",
-- Communications in Mathematical Physics 99 (1985), 389--434.
-- DOI: 10.1007/BF01240355.
--
-- Roger A. Horn and Charles R. Johnson,
-- "Matrix Analysis", second edition, Cambridge University Press, 2012.
-- DOI: 10.1017/CBO9781139020411.
--
-- DASHI CONTRIBUTION
--
-- Turn the finite weighted reopening estimate into an actual kernel-decay
-- theorem for the exact selected-background regularized gauge Green.
--
-- For a root-dependent rational diagonal weight D, the already-proved
-- residual satisfies
--
--       ||D R_A D^-1||_1 <= 1/6.
--
-- The flat Green column has weighted l1 mass < 2.  Therefore the weighted
-- background Green column solves the tilted reopening equation and obeys
--
--       ||D G_A D^-1 e_y||_1 <= (6/5) * 2 < 3.
--
-- Coordinate extraction and exact untwisting give
--
--       |G_A(root,target)|
--          <= 3 * w_root(target),
--
-- where on the configured side-four torus
--
--       w_root(target) = product_mu (64/65)^{d_C4(root_mu,target_mu)}.
--
-- Thus the local Gate-I Green has literal rational exponential decay.  This is
-- intentionally a fixed side-four theorem, not the still-open scale-uniform RG
-- estimate required for the continuum construction.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; _+_; _*_; _≤_; _/_; ∣_∣)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using
  (cong; subst; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact as Sums
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionNormSquaredExact as Norm
import DASHI.Physics.YangMills.BalabanP33FiniteCombesThomasConjugationExact as CT
import DASHI.Physics.YangMills.BalabanFiniteRectangularAbsoluteColumnMassExact as ColumnMass
import DASHI.Physics.YangMills.BalabanFiniteMatrixL1ContractionExact as L1
import DASHI.Physics.YangMills.BalabanFiniteStrictContractionReopeningExact as Strict
import DASHI.Physics.YangMills.BalabanFiniteRationalInjectiveInverseExact as FiniteInverse
import DASHI.Physics.YangMills.BalabanConstructiveRationalMatrixInverseExact as Matrix
import DASHI.Physics.YangMills.BalabanSelectedFlatGaugeGreenAbsoluteMassExact as GreenMass
import DASHI.Physics.YangMills.BalabanSelectedBackgroundFlatGreenPerturbationContractionExact as Contraction
import DASHI.Physics.YangMills.BalabanSelectedBackgroundFlatGreenPerturbationTwoSidedContractionExact as TwoSided
import DASHI.Physics.YangMills.BalabanSelectedBackgroundRationalCombesThomasWeightExact as Weight
import DASHI.Physics.YangMills.BalabanSelectedBackgroundRationalWeightedPowerDecayExact as Weighted
import DASHI.Physics.YangMills.BalabanSelectedBackgroundResidualPowerDecayExact as Residual
import DASHI.Physics.YangMills.BalabanSelectedBackgroundResidualReopeningExact as Reopening
import DASHI.Physics.YangMills.BalabanSelectedBackgroundFiniteRationalReopeningExact as FiniteReopen
import DASHI.Physics.YangMills.BalabanP33PhysicalRationalWilsonPlaquetteJetExact as Physical
import DASHI.Physics.YangMills.BalabanP33PhysicalBackgroundGaugeParameterizedYoungExact as Relaxed

GaugeRow : Set
GaugeRow = Contraction.GaugeRow

GaugeVector : Set
GaugeVector = GaugeRow → ℚ

scaleWeight : GaugeRow → GaugeVector → GaugeVector
scaleWeight root vector row = Weight.gaugeWeight root row * vector row

scaleInverseWeight : GaugeRow → GaugeVector → GaugeVector
scaleInverseWeight root vector row = Weight.gaugeInverseWeight root row * vector row

scaleInverseAfterWeightExact : ∀ root vector row →
  scaleInverseWeight root (scaleWeight root vector) row ≡ vector row
scaleInverseAfterWeightExact root vector row =
  trans
    (ℚRing.solve-∀
      (Weight.gaugeInverseWeight root row)
      (Weight.gaugeWeight root row)
      (vector row) :
      Weight.gaugeInverseWeight root row
        * (Weight.gaugeWeight root row * vector row)
      ≡ (Weight.gaugeInverseWeight root row
          * Weight.gaugeWeight root row) * vector row)
    (trans
      (cong (_* vector row) (Weight.gaugeWeightInverseExact root row))
      (ℚRing.solve-∀ (vector row)))

scaleWeightAfterInverseExact : ∀ root vector row →
  scaleWeight root (scaleInverseWeight root vector) row ≡ vector row
scaleWeightAfterInverseExact root vector row =
  trans
    (ℚRing.solve-∀
      (Weight.gaugeWeight root row)
      (Weight.gaugeInverseWeight root row)
      (vector row) :
      Weight.gaugeWeight root row
        * (Weight.gaugeInverseWeight root row * vector row)
      ≡ (Weight.gaugeInverseWeight root row
          * Weight.gaugeWeight root row) * vector row)
    (trans
      (cong (_* vector row) (Weight.gaugeWeightInverseExact root row))
      (ℚRing.solve-∀ (vector row)))

weightedResidualOnScaledVectorExact :
  ∀ root background vector row →
  Weighted.weightedResidualApply root background
      (scaleWeight root vector) row
  ≡ scaleWeight root (Residual.residualApply background vector) row
weightedResidualOnScaledVectorExact root background vector row =
  let
    rawKernel = Contraction.flatGreenTimesPerturbationKernel background
    wRow = Weight.gaugeWeight root row

    termExact : ∀ column →
      Weight.weightedSelectedBackgroundResidual root background row column
        * scaleWeight root vector column
      ≡ wRow * (rawKernel row column * vector column)
    termExact column =
      let
        iw = Weight.gaugeInverseWeight root column
        w = Weight.gaugeWeight root column
        k = rawKernel row column
        v = vector column

        rearrange :
          (wRow * (k * iw)) * (w * v)
          ≡ wRow * (k * ((iw * w) * v))
        rearrange = ℚRing.solve-∀ wRow k iw w v
      in
      trans rearrange
        (trans
          (cong
            (λ selected → wRow * (k * (selected * v)))
            (Weight.gaugeWeightInverseExact root column))
          (ℚRing.solve-∀ wRow k v))

    rewriteTerms = Sums.sumRationalCong Contraction.gaugeRows _ _ termExact

    factor = Sums.sumRationalScale wRow Contraction.gaugeRows
      (λ column → rawKernel row column * vector column)
  in
  trans rewriteTerms factor

weightedIdentityPlusOnScaledVectorExact :
  ∀ root background vector row →
  Reopening.weightedIdentityPlusResidualApply root background
      (scaleWeight root vector) row
  ≡ scaleWeight root
      (Reopening.unweightedIdentityPlusResidualApply background vector) row
weightedIdentityPlusOnScaledVectorExact root background vector row =
  trans
    (cong
      (scaleWeight root vector row +_)
      (weightedResidualOnScaledVectorExact root background vector row))
    (ℚRing.solve-∀
      (Weight.gaugeWeight root row)
      (vector row)
      (Residual.residualApply background vector row))

------------------------------------------------------------------------
-- Kernel columns for G_A and their weighted versions.
------------------------------------------------------------------------

selectedBackgroundGaugeGreenKernel :
  ∀ background →
  Matrix.RationalMatrixInverseCertificate
    FiniteReopen.gaugeFiniteCoordinates
    (FiniteReopen.selectedResidualIdentityPlusMatrix background) →
  GaugeRow → GaugeRow → ℚ
selectedBackgroundGaugeGreenKernel background certificate row target =
  Matrix.applyMatrix FiniteReopen.gaugeFiniteCoordinates
    (Matrix.inverseMatrix certificate)
    (λ middle → Contraction.flatGreenKernelMatrix middle target)
    row

rawScaledFlatColumn : GaugeRow → GaugeRow → GaugeVector
rawScaledFlatColumn root target row =
  Contraction.flatGreenKernelMatrix row target
    * Weight.gaugeInverseWeight root target

rawScaledGreenColumn :
  ∀ background →
  Matrix.RationalMatrixInverseCertificate
    FiniteReopen.gaugeFiniteCoordinates
    (FiniteReopen.selectedResidualIdentityPlusMatrix background) →
  GaugeRow → GaugeRow → GaugeVector
rawScaledGreenColumn background certificate root target =
  Matrix.applyMatrix FiniteReopen.gaugeFiniteCoordinates
    (Matrix.inverseMatrix certificate)
    (rawScaledFlatColumn root target)

tiltedFlatColumn : GaugeRow → GaugeRow → GaugeVector
tiltedFlatColumn root target row =
  Weight.weightedKernel root Contraction.flatGreenKernelMatrix row target

tiltedGreenColumn :
  ∀ background →
  Matrix.RationalMatrixInverseCertificate
    FiniteReopen.gaugeFiniteCoordinates
    (FiniteReopen.selectedResidualIdentityPlusMatrix background) →
  GaugeRow → GaugeRow → GaugeVector
tiltedGreenColumn background certificate root target =
  scaleWeight root (rawScaledGreenColumn background certificate root target)

rawScaledGreenColumnEntryExact :
  ∀ background certificate root target row →
  rawScaledGreenColumn background certificate root target row
  ≡ selectedBackgroundGaugeGreenKernel background certificate row target
      * Weight.gaugeInverseWeight root target
rawScaledGreenColumnEntryExact background certificate root target row =
  let
    inverse = Matrix.inverseMatrix certificate
    coefficient = Weight.gaugeInverseWeight root target
    term = λ middle →
      inverse row middle * Contraction.flatGreenKernelMatrix middle target
  in
  trans
    (Sums.sumRationalCong Contraction.gaugeRows _ _
      (λ middle → ℚRing.solve-∀
        (inverse row middle)
        (Contraction.flatGreenKernelMatrix middle target)
        coefficient))
    (DASHI.Physics.YangMills.BalabanConstructiveRationalMatrixInverseExact.sumRationalRightScale
      Contraction.gaugeRows term coefficient)

tiltedGreenColumnEntryExact :
  ∀ background certificate root target row →
  tiltedGreenColumn background certificate root target row
  ≡ Weight.weightedKernel root
      (selectedBackgroundGaugeGreenKernel background certificate)
      row target
tiltedGreenColumnEntryExact background certificate root target row =
  trans
    (cong
      (Weight.gaugeWeight root row *_)
      (rawScaledGreenColumnEntryExact
        background certificate root target row))
    refl

tiltedFlatColumnAsScaledExact : ∀ root target row →
  tiltedFlatColumn root target row
  ≡ scaleWeight root (rawScaledFlatColumn root target) row
tiltedFlatColumnAsScaledExact root target row = refl

rawScaledGreenSolvesUnweightedReopening :
  ∀ background certificate root target row →
  Reopening.unweightedIdentityPlusResidualApply background
      (rawScaledGreenColumn background certificate root target) row
  ≡ rawScaledFlatColumn root target row
rawScaledGreenSolvesUnweightedReopening background certificate root target row =
  trans
    (sym
      (FiniteReopen.selectedResidualIdentityPlusMatrixActionExact
        background
        (rawScaledGreenColumn background certificate root target)
        row))
    (Matrix.matrixInverseRightExact certificate
      (rawScaledFlatColumn root target) row)

tiltedGreenSolvesWeightedReopening :
  ∀ background certificate root target →
  Reopening.WeightedReopeningEquation root background
    (tiltedGreenColumn background certificate root target)
    (tiltedFlatColumn root target)
tiltedGreenSolvesWeightedReopening background certificate root target row =
  trans
    (weightedIdentityPlusOnScaledVectorExact root background
      (rawScaledGreenColumn background certificate root target) row)
    (trans
      (cong
        (Weight.gaugeWeight root row *_)
        (rawScaledGreenSolvesUnweightedReopening
          background certificate root target row))
      (sym (tiltedFlatColumnAsScaledExact root target row)))

------------------------------------------------------------------------
-- Weighted flat source is uniformly below 2 in l1.
------------------------------------------------------------------------

weightedFlatGreenColumnBound : ℚ
weightedFlatGreenColumnBound = + 111537 / 65536

weightedFlatGreenColumnBoundExact :
  GreenMass.seventeenSixteenths * Weight.siteGrowthEnvelope
  ≡ weightedFlatGreenColumnBound
weightedFlatGreenColumnBoundExact = ℚRing.solve []

weightedFlatGreenColumnBoundBelowTwo :
  weightedFlatGreenColumnBound ≤ + 2 / 1
weightedFlatGreenColumnBoundBelowTwo =
  Weight.belowFromDifference
    weightedFlatGreenColumnBound (+ 2 / 1) (+ 19535 / 65536)
    (ℚRing.solve []) (ℚP.nonNegative⁻¹ (+ 19535 / 65536))

tiltedFlatColumnL1BelowTwo : ∀ root target →
  L1.vectorL1 Contraction.gaugeRows (tiltedFlatColumn root target)
  ≤ + 2 / 1
tiltedFlatColumnL1BelowTwo root target =
  let
    weightedMass = Weighted.weightedColumnMassUpper
      root Contraction.flatGreenKernelMatrix target

    rawScaled =
      DASHI.Physics.YangMills.BalabanSelectedBackgroundGaugeGramPerturbationAbsoluteMassExact.rightScaleMonotone
        Weight.siteGrowthEnvelope
        (ColumnMass.squareColumnMass Contraction.gaugeRows
          Contraction.flatGreenKernelMatrix target)
        GreenMass.seventeenSixteenths
        (ℚP.nonNegative⁻¹ Weight.siteGrowthEnvelope)
        (TwoSided.selectedFlatGaugeGreenAbsoluteColumnMassBound target)

    toNamed :
      ColumnMass.squareColumnMass Contraction.gaugeRows
        Contraction.flatGreenKernelMatrix target
        * Weight.siteGrowthEnvelope
      ≤ weightedFlatGreenColumnBound
    toNamed = subst
      (λ upper →
        ColumnMass.squareColumnMass Contraction.gaugeRows
          Contraction.flatGreenKernelMatrix target
          * Weight.siteGrowthEnvelope ≤ upper)
      weightedFlatGreenColumnBoundExact rawScaled
  in
  ℚP.≤-trans weightedMass
    (ℚP.≤-trans toNamed weightedFlatGreenColumnBoundBelowTwo)

------------------------------------------------------------------------
-- The tilted background Green column is below 3; untwist for decay.
------------------------------------------------------------------------

three : ℚ
three = + 3 / 1

tiltedGreenColumnL1BelowThree :
  ∀ background → Relaxed.RelaxedInverseLinkRadius background →
  ∀ certificate root target →
  L1.vectorL1 Contraction.gaugeRows
    (tiltedGreenColumn background certificate root target)
  ≤ three
tiltedGreenColumnL1BelowThree background radius certificate root target =
  let
    reopening = Reopening.selectedBackgroundWeightedResidualReopeningSixFifths
      background radius root
      (tiltedGreenColumn background certificate root target)
      (tiltedFlatColumn root target)
      (tiltedGreenSolvesWeightedReopening background certificate root target)

    scaledTwo = Norm.scaleNonnegative Strict.sixFifths
      (ℚP.nonNegative⁻¹ Strict.sixFifths)
      (tiltedFlatColumnL1BelowTwo root target)

    twelveFifths :
      Strict.sixFifths * (+ 2 / 1) ≤ three
    twelveFifths = Weight.belowFromDifference
      (Strict.sixFifths * (+ 2 / 1)) three (+ 3 / 5)
      (ℚRing.solve []) (ℚP.nonNegative⁻¹ (+ 3 / 5))
  in
  ℚP.≤-trans reopening
    (ℚP.≤-trans scaledTwo twelveFifths)

tiltedGreenEntryBelowThree :
  ∀ background → Relaxed.RelaxedInverseLinkRadius background →
  ∀ certificate root target row →
  ∣ Weight.weightedKernel root
      (selectedBackgroundGaugeGreenKernel background certificate)
      row target ∣
  ≤ three
tiltedGreenEntryBelowThree background radius certificate root target row =
  let
    coordinateBelow =
      Strict.finiteSelectorCoordinateBelowL1
        FiniteReopen.gaugeRowSelector
        (tiltedGreenColumn background certificate root target)
        row

    normBelow = tiltedGreenColumnL1BelowThree
      background radius certificate root target
  in
  subst
    (λ lower → lower ≤ three)
    (cong ∣_∣
      (tiltedGreenColumnEntryExact
        background certificate root target row))
    (ℚP.≤-trans coordinateBelow normBelow)

selectedBackgroundGaugeGreenRationalExponentialDecayWithCertificate :
  ∀ background → Relaxed.RelaxedInverseLinkRadius background →
  ∀ certificate root target →
  ∣ selectedBackgroundGaugeGreenKernel background certificate root target ∣
  ≤ three * Weight.gaugeWeight root target
selectedBackgroundGaugeGreenRationalExponentialDecayWithCertificate
    background radius certificate root target =
  CT.combesThomasKernelDecayFromTiltedEntry
    (Weight.gaugeWeight root)
    (Weight.gaugeInverseWeight root)
    (Weight.gaugeWeightInverseExact root)
    (selectedBackgroundGaugeGreenKernel background certificate)
    root target three
    (Weight.gaugeRootInverseWeightOne root)
    (Weight.gaugeWeightNonnegative root target)
    (Weight.gaugeWeightAbsoluteExact root target)
    (tiltedGreenEntryBelowThree
      background radius certificate root target root)

selectedBackgroundGaugeGreenExponentialDecay :
  FiniteInverse.FiniteRationalInjectiveInverseAuthority →
  ∀ background → Relaxed.RelaxedInverseLinkRadius background →
  ∀ root target →
  let certificate =
        FiniteReopen.selectedResidualIdentityPlusRationalInverse
          _ background _
  in
  ∣ selectedBackgroundGaugeGreenKernel background certificate root target ∣
  ≤ three * Weight.gaugeWeight root target
selectedBackgroundGaugeGreenExponentialDecay authority background radius root target =
  selectedBackgroundGaugeGreenRationalExponentialDecayWithCertificate
    background radius
    (FiniteReopen.selectedResidualIdentityPlusRationalInverse
      authority background radius)
    root target

selectedBackgroundGaugeGreenWeightedColumnLevel : ProofLevel
selectedBackgroundGaugeGreenWeightedColumnLevel = machineChecked

selectedBackgroundGaugeGreenRationalDecayLevel : ProofLevel
selectedBackgroundGaugeGreenRationalDecayLevel = machineChecked

selectedBackgroundGaugeGreenExponentialDecayLevel : ProofLevel
selectedBackgroundGaugeGreenExponentialDecayLevel = machineChecked
