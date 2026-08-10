module DASHI.Physics.YangMills.BalabanSelectedBackgroundFlatGreenPerturbationContractionExact where

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
-- Tosio Kato,
-- "Perturbation Theory for Linear Operators", Springer Classics in
-- Mathematics. DOI: 10.1007/978-3-642-66282-9.
--
-- DASHI CONTRIBUTION
--
-- On the literal 768-row multiplier carrier,
--
--   K_A^reg = K_0^reg + E_A,   G_0 = (K_0^reg)^-1.
--
-- The exact side-four Fourier Green has absolute row mass below 17/16 and the
-- actual selected Gram perturbation has absolute row mass below 6153/65536.
-- Finite Schur/Fubini algebra therefore gives
--
--   sup_i sum_j |(G_0 E_A)(i,j)|
--     <= (17/16)(6153/65536)
--      = 104601/1048576
--      < 1/10 < 1/2.
--
-- `flatGreenKernelActsExactly` proves that the matrix called G_0 below is the
-- repository's existing exact componentwise Fourier Green, not an unrelated
-- comparison kernel.  E_A is the literal selected Gram difference.  The next
-- analytic step is weighted/conjugated smallness for exponential decay.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; _+_; _-_; _*_; _≤_; _/_; ∣_∣)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using
  (cong; subst; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier using (pair)
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreCarrier as Block
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact as Sums
import DASHI.Physics.YangMills.BalabanFiniteSumFubiniExact as Fubini
import DASHI.Physics.YangMills.BalabanP33FiniteWeightedSchurSquaredExact as Schur
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionNormSquaredExact as Norm
import DASHI.Physics.YangMills.BalabanP33PhysicalCoordinateBasisExact as Basis
import DASHI.Physics.YangMills.BalabanP33PhysicalSU2FiniteCoordinatesExact as Coordinates
import DASHI.Physics.YangMills.BalabanP33PhysicalFlatGaugeDivergenceIdentificationExact as FlatGauge
import DASHI.Physics.YangMills.BalabanPath4AxisAverageExact as Path4
import DASHI.Physics.YangMills.BalabanSide4ScalarGreenKernelComputed as Kernel
import DASHI.Physics.YangMills.BalabanSide4ScalarGreenConvolutionExact as Green
import DASHI.Physics.YangMills.BalabanSide4TranslationDifferenceExact as Difference
import DASHI.Physics.YangMills.BalabanSelectedFlatGaugeRegularizedGreenExact as FlatGreen
import DASHI.Physics.YangMills.BalabanSelectedFlatGaugeAdjointGramFloorExact as Flat
import DASHI.Physics.YangMills.BalabanSelectedFlatGaugeConstraintAbsoluteMassExact as FlatMass
import DASHI.Physics.YangMills.BalabanSelectedFlatGaugeGreenAbsoluteMassExact as GreenMass
import DASHI.Physics.YangMills.BalabanSelectedBackgroundGaugePerturbationFiniteRangeExact as Perturbation
import DASHI.Physics.YangMills.BalabanSelectedBackgroundGaugeGramPerturbationAbsoluteMassExact as PerturbationMass
import DASHI.Physics.YangMills.BalabanP33PhysicalRationalWilsonPlaquetteJetExact as Physical
import DASHI.Physics.YangMills.BalabanP33PhysicalBackgroundGaugeParameterizedYoungExact as Relaxed
import DASHI.Physics.YangMills.BalabanFiniteRectangularAbsoluteMassExact as Mass

GaugeRow : Set
GaugeRow = FlatGauge.GaugeCoordinate4

gaugeRows = FlatMass.flatRows
lieKronecker = FlatMass.lieKronecker

flatGreenKernelMatrix : GaugeRow → GaugeRow → ℚ
flatGreenKernelMatrix
    (pair outputCoordinate outputSite)
    (pair inputCoordinate inputSite) =
  lieKronecker inputCoordinate outputCoordinate
    * Kernel.scalarGreenKernel
        (Difference.subtractSite4 outputSite inputSite)

flatGreenKernelApply : Flat.GaugeMultiplier → Flat.GaugeMultiplier
flatGreenKernelApply source output =
  Sums.sumRational gaugeRows
    (λ input → flatGreenKernelMatrix output input * source input)

flatGreenKernelCoordinateActionExact :
  ∀ source outputCoordinate outputSite inputCoordinate →
  Sums.sumRational (Block.physicalBlockSites Path4.side4)
    (λ inputSite →
      flatGreenKernelMatrix (pair outputCoordinate outputSite)
        (pair inputCoordinate inputSite)
      * source (pair inputCoordinate inputSite))
  ≡ lieKronecker inputCoordinate outputCoordinate
      * Green.scalarGreen
          (Flat.multiplierField source inputCoordinate) outputSite
flatGreenKernelCoordinateActionExact
    source outputCoordinate outputSite inputCoordinate =
  let
    lie = lieKronecker inputCoordinate outputCoordinate
  in
  trans
    (Sums.sumRationalCong
      (Block.physicalBlockSites Path4.side4) _ _
      (λ inputSite → ℚRing.solve-∀ lie
        (Kernel.scalarGreenKernel
          (Difference.subtractSite4 outputSite inputSite))
        (source (pair inputCoordinate inputSite))))
    (Sums.sumRationalScale lie
      (Block.physicalBlockSites Path4.side4)
      (λ inputSite →
        Kernel.scalarGreenKernel
          (Difference.subtractSite4 outputSite inputSite)
        * source (pair inputCoordinate inputSite)))

flatGreenKernelActsExactly : ∀ source outputCoordinate outputSite →
  flatGreenKernelApply source (pair outputCoordinate outputSite)
  ≡ FlatGreen.regularizedFlatGaugeGreen source
      (pair outputCoordinate outputSite)
flatGreenKernelActsExactly source outputCoordinate outputSite =
  let
    value = λ inputCoordinate →
      Green.scalarGreen (Flat.multiplierField source inputCoordinate) outputSite
  in
  trans
    (Fubini.sumCartesian Coordinates.lieCoordinates3
      (Block.physicalBlockSites Path4.side4)
      (λ input →
        flatGreenKernelMatrix (pair outputCoordinate outputSite) input
          * source input))
    (trans
      (Sums.sumRationalCong Coordinates.lieCoordinates3 _
        (λ inputCoordinate →
          lieKronecker inputCoordinate outputCoordinate * value inputCoordinate)
        (flatGreenKernelCoordinateActionExact
          source outputCoordinate outputSite))
      (trans
        (Sums.sumRationalCong Coordinates.lieCoordinates3 _ _
          (λ inputCoordinate →
            ℚP.*-comm
              (lieKronecker inputCoordinate outputCoordinate)
              (value inputCoordinate)))
        (Basis.selectorExact Basis.lieCoordinateFiniteSelector
          value outputCoordinate)))

lieKroneckerAbsoluteExact : ∀ left right →
  ∣ lieKronecker left right ∣ ≡ lieKronecker left right
lieKroneckerAbsoluteExact left right
  with Basis.decide Basis.lieCoordinateFiniteSelector left right
... | yes refl = refl
... | no _ = refl

translatedGreenAbsoluteMassExact : ∀ rowSite →
  Sums.sumRational (Block.physicalBlockSites Path4.side4)
    (λ inputSite →
      ∣ Kernel.scalarGreenKernel
          (Difference.subtractSite4 rowSite inputSite) ∣)
  ≡ GreenMass.scalarGreenAbsoluteMass
translatedGreenAbsoluteMassExact rowSite =
  let
    absoluteKernel = λ offset → ∣ Kernel.scalarGreenKernel offset ∣

    symmetric :
      Sums.sumRational (Block.physicalBlockSites Path4.side4)
        (λ inputSite →
          ∣ Kernel.scalarGreenKernel
              (Difference.subtractSite4 rowSite inputSite) ∣)
      ≡ Sums.sumRational (Block.physicalBlockSites Path4.side4)
        (λ inputSite →
          absoluteKernel (Difference.subtractSite4 inputSite rowSite))
    symmetric =
      Sums.sumRationalCong
        (Block.physicalBlockSites Path4.side4) _ _
        (λ inputSite →
          cong ∣_∣ (Green.kernelColumnSymmetry rowSite inputSite))
  in
  trans symmetric
    (Difference.siteSumSubtractInvariant rowSite absoluteKernel)

flatGreenKernelCoordinateMassExact : ∀ outputCoordinate outputSite inputCoordinate →
  Sums.sumRational (Block.physicalBlockSites Path4.side4)
    (λ inputSite →
      ∣ flatGreenKernelMatrix
          (pair outputCoordinate outputSite)
          (pair inputCoordinate inputSite) ∣)
  ≡ lieKronecker inputCoordinate outputCoordinate
      * GreenMass.scalarGreenAbsoluteMass
flatGreenKernelCoordinateMassExact outputCoordinate outputSite inputCoordinate =
  let
    lie = lieKronecker inputCoordinate outputCoordinate
  in
  trans
    (Sums.sumRationalCong
      (Block.physicalBlockSites Path4.side4) _ _
      (λ inputSite →
        trans
          (Schur.absoluteProductExact lie
            (Kernel.scalarGreenKernel
              (Difference.subtractSite4 outputSite inputSite)))
          (cong
            (_* ∣ Kernel.scalarGreenKernel
                  (Difference.subtractSite4 outputSite inputSite) ∣)
            (lieKroneckerAbsoluteExact inputCoordinate outputCoordinate))))
    (trans
      (Sums.sumRationalScale lie
        (Block.physicalBlockSites Path4.side4)
        (λ inputSite →
          ∣ Kernel.scalarGreenKernel
              (Difference.subtractSite4 outputSite inputSite) ∣))
      (cong (lie *_)
        (translatedGreenAbsoluteMassExact outputSite)))

flatGreenKernelRowMassExact : ∀ row →
  Mass.squareRowMass gaugeRows flatGreenKernelMatrix row
  ≡ GreenMass.scalarGreenAbsoluteMass
flatGreenKernelRowMassExact (pair outputCoordinate outputSite) =
  trans
    (Fubini.sumCartesian Coordinates.lieCoordinates3
      (Block.physicalBlockSites Path4.side4)
      (λ input → ∣ flatGreenKernelMatrix
        (pair outputCoordinate outputSite) input ∣))
    (trans
      (Sums.sumRationalCong Coordinates.lieCoordinates3 _
        (λ inputCoordinate →
          lieKronecker inputCoordinate outputCoordinate
            * GreenMass.scalarGreenAbsoluteMass)
        (flatGreenKernelCoordinateMassExact outputCoordinate outputSite))
      (trans
        (Sums.sumRationalCong Coordinates.lieCoordinates3 _ _
          (λ inputCoordinate →
            ℚP.*-comm
              (lieKronecker inputCoordinate outputCoordinate)
              GreenMass.scalarGreenAbsoluteMass))
        (FlatMass.lieSelectorScaledExact
          GreenMass.scalarGreenAbsoluteMass outputCoordinate)))

selectedFlatGaugeGreenAbsoluteRowMassBound : ∀ row →
  Mass.squareRowMass gaugeRows flatGreenKernelMatrix row
  ≤ GreenMass.seventeenSixteenths
selectedFlatGaugeGreenAbsoluteRowMassBound row =
  subst
    (λ mass → mass ≤ GreenMass.seventeenSixteenths)
    (sym (flatGreenKernelRowMassExact row))
    GreenMass.scalarGreenAbsoluteMassBelowSeventeenSixteenths

transposePerturbationKernel :
  Physical.RationalSU2Background4 → GaugeRow → GaugeRow → ℚ
transposePerturbationKernel background output middle =
  Perturbation.gaugeGramPerturbationMatrix background middle output

flatGreenTimesPerturbationKernel :
  Physical.RationalSU2Background4 → GaugeRow → GaugeRow → ℚ
flatGreenTimesPerturbationKernel background =
  Mass.transposeProduct gaugeRows flatGreenKernelMatrix
    (transposePerturbationKernel background)

greenPerturbationContractionBound : ℚ
greenPerturbationContractionBound = + 104601 / 1048576

oneTenth : ℚ
oneTenth = + 1 / 10

contractionSlackToOneTenth : ℚ
contractionSlackToOneTenth = + 1283 / 5242880

contractionBoundExactProduct :
  GreenMass.seventeenSixteenths
    * PerturbationMass.perturbationRowMassBound
  ≡ greenPerturbationContractionBound
contractionBoundExactProduct = ℚRing.solve []

contractionBoundBelowOneTenth :
  greenPerturbationContractionBound ≤ oneTenth
contractionBoundBelowOneTenth =
  Norm.nonnegativeDifferenceImpliesBelow
    (subst
      (λ difference → 0ℚ ≤ difference)
      (sym (ℚRing.solve [] :
        oneTenth - greenPerturbationContractionBound
        ≡ contractionSlackToOneTenth))
      (ℚP.nonNegative⁻¹ contractionSlackToOneTenth))

oneTenthBelowOneHalf : oneTenth ≤ + 1 / 2
oneTenthBelowOneHalf =
  Norm.nonnegativeDifferenceImpliesBelow
    (subst
      (λ difference → 0ℚ ≤ difference)
      (sym (ℚRing.solve [] : (+ 1 / 2) - oneTenth ≡ + 2 / 5))
      (ℚP.nonNegative⁻¹ (+ 2 / 5)))

selectedBackgroundFlatGreenPerturbationAbsoluteRowMassBound :
  ∀ background → Relaxed.RelaxedInverseLinkRadius background →
  ∀ row →
  Mass.squareRowMass gaugeRows
    (flatGreenTimesPerturbationKernel background) row
  ≤ greenPerturbationContractionBound
selectedBackgroundFlatGreenPerturbationAbsoluteRowMassBound
    background radius row =
  let
    raw = Mass.transposeProductRowMassBound
      gaugeRows gaugeRows flatGreenKernelMatrix
      (transposePerturbationKernel background)
      PerturbationMass.perturbationRowMassBound row
      (ℚP.nonNegative⁻¹ PerturbationMass.perturbationRowMassBound)
      (PerturbationMass.selectedGaugeGramPerturbationAbsoluteRowMassBound
        background radius)

    scaled = PerturbationMass.rightScaleMonotone
      PerturbationMass.perturbationRowMassBound
      (Mass.squareRowMass gaugeRows flatGreenKernelMatrix row)
      GreenMass.seventeenSixteenths
      (ℚP.nonNegative⁻¹ PerturbationMass.perturbationRowMassBound)
      (selectedFlatGaugeGreenAbsoluteRowMassBound row)
  in
  ℚP.≤-trans raw
    (subst
      (λ upper →
        Mass.squareRowMass gaugeRows flatGreenKernelMatrix row
          * PerturbationMass.perturbationRowMassBound
        ≤ upper)
      contractionBoundExactProduct scaled)

selectedBackgroundFlatGreenPerturbationOneTenthContraction :
  ∀ background → Relaxed.RelaxedInverseLinkRadius background →
  ∀ row →
  Mass.squareRowMass gaugeRows
    (flatGreenTimesPerturbationKernel background) row
  ≤ oneTenth
selectedBackgroundFlatGreenPerturbationOneTenthContraction
    background radius row =
  ℚP.≤-trans
    (selectedBackgroundFlatGreenPerturbationAbsoluteRowMassBound
      background radius row)
    contractionBoundBelowOneTenth

selectedBackgroundFlatGreenPerturbationHalfContraction :
  ∀ background → Relaxed.RelaxedInverseLinkRadius background →
  ∀ row →
  Mass.squareRowMass gaugeRows
    (flatGreenTimesPerturbationKernel background) row
  ≤ + 1 / 2
selectedBackgroundFlatGreenPerturbationHalfContraction
    background radius row =
  ℚP.≤-trans
    (selectedBackgroundFlatGreenPerturbationOneTenthContraction
      background radius row)
    oneTenthBelowOneHalf

selectedFlatGaugeGreenKernelIdentificationLevel : ProofLevel
selectedFlatGaugeGreenKernelIdentificationLevel = machineChecked

selectedBackgroundFlatGreenPerturbationContractionLevel : ProofLevel
selectedBackgroundFlatGreenPerturbationContractionLevel = machineChecked

weightedSelectedBackgroundGreenStillRequiredLevel : ProofLevel
weightedSelectedBackgroundGreenStillRequiredLevel = conditional
