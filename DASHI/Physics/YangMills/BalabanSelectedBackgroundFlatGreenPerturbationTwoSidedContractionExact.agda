module DASHI.Physics.YangMills.BalabanSelectedBackgroundFlatGreenPerturbationTwoSidedContractionExact where

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
-- DASHI CONTRIBUTION
--
-- Complement the previously proved row contraction for the literal residual
-- R_A = G_0 E_A by the corresponding column contraction.  The exact flat
-- Fourier Green is symmetric, so its column mass is the same 74077/71680 and
-- hence is below 17/16.  The previous tranche proves both row and column mass
-- of E_A below 6153/65536.  Therefore
--
--   sup_j sum_i |R_A(i,j)|
--     <= (17/16)(6153/65536)
--      = 104601/1048576 < 1/10.
--
-- Thus R_A is small simultaneously in the finite l1 and l-infinity Schur
-- senses.  This is the input needed for a literal vector Neumann contraction,
-- not merely a quadratic-form comparison.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base as ℚ using (ℚ; _*_; _≤_; ∣_∣)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier using (pair)
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact as Sums
import DASHI.Physics.YangMills.BalabanP33PhysicalCoordinateBasisExact as Basis
import DASHI.Physics.YangMills.BalabanSide4ScalarGreenConvolutionExact as Green
import DASHI.Physics.YangMills.BalabanFiniteRectangularAbsoluteMassExact as RowMass
import DASHI.Physics.YangMills.BalabanFiniteRectangularAbsoluteColumnMassExact as ColumnMass
import DASHI.Physics.YangMills.BalabanSelectedFlatGaugeConstraintAbsoluteMassExact as FlatMass
import DASHI.Physics.YangMills.BalabanSelectedFlatGaugeGreenAbsoluteMassExact as GreenMass
import DASHI.Physics.YangMills.BalabanSelectedBackgroundGaugePerturbationFiniteRangeExact as Perturbation
import DASHI.Physics.YangMills.BalabanSelectedBackgroundGaugeGramPerturbationAbsoluteMassExact as PerturbationMass
import DASHI.Physics.YangMills.BalabanSelectedBackgroundGaugeGramPerturbationTwoSidedMassExact as TwoSidedE
import DASHI.Physics.YangMills.BalabanSelectedBackgroundFlatGreenPerturbationContractionExact as Contraction
import DASHI.Physics.YangMills.BalabanP33PhysicalRationalWilsonPlaquetteJetExact as Physical
import DASHI.Physics.YangMills.BalabanP33PhysicalBackgroundGaugeParameterizedYoungExact as Relaxed

GaugeRow = Contraction.GaugeRow
gaugeRows = Contraction.gaugeRows

lieKroneckerSymmetric : ∀ left right →
  Contraction.lieKronecker left right ≡ Contraction.lieKronecker right left
lieKroneckerSymmetric left right
  with Basis.decide Basis.lieCoordinateFiniteSelector left right
... | Relation.Nullary.Decidable.Core.yes refl
    with Basis.decide Basis.lieCoordinateFiniteSelector right right
...   | Relation.Nullary.Decidable.Core.yes _ = refl
...   | Relation.Nullary.Decidable.Core.no different =
      Data.Empty.⊥-elim (different refl)
... | Relation.Nullary.Decidable.Core.no different
    with Basis.decide Basis.lieCoordinateFiniteSelector right left
...   | Relation.Nullary.Decidable.Core.yes equality =
      Data.Empty.⊥-elim (different (sym equality))
...   | Relation.Nullary.Decidable.Core.no _ = refl

flatGreenKernelSymmetric : ∀ left right →
  Contraction.flatGreenKernelMatrix left right
  ≡ Contraction.flatGreenKernelMatrix right left
flatGreenKernelSymmetric
    (pair leftCoordinate leftSite)
    (pair rightCoordinate rightSite) =
  let
    lieSym = lieKroneckerSymmetric rightCoordinate leftCoordinate
    kernelSym = Green.kernelColumnSymmetry leftSite rightSite
  in
  trans
    (cong
      (_* Green.scalarGreenKernel
          (DASHI.Physics.YangMills.BalabanSide4TranslationDifferenceExact.subtractSite4
            leftSite rightSite))
      lieSym)
    (cong
      (Contraction.lieKronecker leftCoordinate rightCoordinate *_)
      kernelSym)

flatGreenColumnMassAsRowMass : ∀ column →
  ColumnMass.squareColumnMass gaugeRows Contraction.flatGreenKernelMatrix column
  ≡ RowMass.squareRowMass gaugeRows Contraction.flatGreenKernelMatrix column
flatGreenColumnMassAsRowMass column =
  Sums.sumRationalCong gaugeRows _ _
    (λ row → cong ∣_∣ (flatGreenKernelSymmetric row column))

selectedFlatGaugeGreenAbsoluteColumnMassBound : ∀ column →
  ColumnMass.squareColumnMass gaugeRows Contraction.flatGreenKernelMatrix column
  ≤ GreenMass.seventeenSixteenths
selectedFlatGaugeGreenAbsoluteColumnMassBound column =
  subst
    (λ lower → lower ≤ GreenMass.seventeenSixteenths)
    (sym (flatGreenColumnMassAsRowMass column))
    (Contraction.selectedFlatGaugeGreenAbsoluteRowMassBound column)

transposePerturbationRowMassIsPerturbationColumnMass : ∀ background row →
  RowMass.absoluteRectRowMass gaugeRows
    (Contraction.transposePerturbationKernel background) row
  ≡ ColumnMass.squareColumnMass gaugeRows
      (Perturbation.gaugeGramPerturbationMatrix background) row
transposePerturbationRowMassIsPerturbationColumnMass background row = refl

selectedTransposePerturbationRowMassBound :
  ∀ background → Relaxed.RelaxedInverseLinkRadius background →
  ∀ row →
  RowMass.absoluteRectRowMass gaugeRows
    (Contraction.transposePerturbationKernel background) row
  ≤ PerturbationMass.perturbationRowMassBound
selectedTransposePerturbationRowMassBound background radius row =
  subst
    (λ lower → lower ≤ PerturbationMass.perturbationRowMassBound)
    (sym (transposePerturbationRowMassIsPerturbationColumnMass background row))
    (TwoSidedE.selectedGaugeGramPerturbationAbsoluteColumnMassBound
      background radius row)

selectedBackgroundFlatGreenPerturbationAbsoluteColumnMassBound :
  ∀ background → Relaxed.RelaxedInverseLinkRadius background →
  ∀ column →
  ColumnMass.squareColumnMass gaugeRows
    (Contraction.flatGreenTimesPerturbationKernel background) column
  ≤ Contraction.greenPerturbationContractionBound
selectedBackgroundFlatGreenPerturbationAbsoluteColumnMassBound
    background radius column =
  let
    raw = ColumnMass.transposeProductColumnMassBound
      gaugeRows gaugeRows
      Contraction.flatGreenKernelMatrix
      (Contraction.transposePerturbationKernel background)
      GreenMass.seventeenSixteenths column
      (ℚP.nonNegative⁻¹ GreenMass.seventeenSixteenths)
      selectedFlatGaugeGreenAbsoluteColumnMassBound

    scaled = PerturbationMass.rightScaleMonotone
      GreenMass.seventeenSixteenths
      (RowMass.absoluteRectRowMass gaugeRows
        (Contraction.transposePerturbationKernel background) column)
      PerturbationMass.perturbationRowMassBound
      (ℚP.nonNegative⁻¹ GreenMass.seventeenSixteenths)
      (selectedTransposePerturbationRowMassBound background radius column)

    coefficientExact :
      PerturbationMass.perturbationRowMassBound * GreenMass.seventeenSixteenths
      ≡ Contraction.greenPerturbationContractionBound
    coefficientExact = ℚRing.solve []
  in
  ℚP.≤-trans raw
    (subst
      (λ upper →
        RowMass.absoluteRectRowMass gaugeRows
          (Contraction.transposePerturbationKernel background) column
          * GreenMass.seventeenSixteenths
        ≤ upper)
      coefficientExact scaled)

selectedBackgroundFlatGreenPerturbationColumnOneTenthContraction :
  ∀ background → Relaxed.RelaxedInverseLinkRadius background →
  ∀ column →
  ColumnMass.squareColumnMass gaugeRows
    (Contraction.flatGreenTimesPerturbationKernel background) column
  ≤ Contraction.oneTenth
selectedBackgroundFlatGreenPerturbationColumnOneTenthContraction
    background radius column =
  ℚP.≤-trans
    (selectedBackgroundFlatGreenPerturbationAbsoluteColumnMassBound
      background radius column)
    Contraction.contractionBoundBelowOneTenth

selectedBackgroundFlatGreenPerturbationTwoSidedContractionLevel : ProofLevel
selectedBackgroundFlatGreenPerturbationTwoSidedContractionLevel = machineChecked
