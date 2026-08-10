module DASHI.Physics.YangMills.BalabanSelectedBackgroundGaugeDefectAbsoluteMassExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Tadeusz Bałaban,
-- "Spaces of Regular Gauge Field Configurations on a Lattice and Gauge
-- Fixing Conditions", Communications in Mathematical Physics 99 (1985),
-- 75--102. DOI: 10.1007/BF01466594.
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
-- Convert the selected-radius squared column estimate for D_A=L_A-L_0 into
-- a literal entrywise absolute bound.  At rho=1/8192,
--
--   D_A(row,column)^2 <= (1/1024)^2,
--   |D_A(row,column)| <= 1/1024.
--
-- The already-proved two-site spatial stencil then gives the conservative
-- exact masses
--
--   rowMass(D_A)    <= 24/1024 = 3/128,
--   columnMass(D_A) <=  6/1024 = 3/512.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_; _≤_; _<_; _/_; ∣_∣; NonNegative; Positive)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Data.Sum.Base using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using
  (cong; cong₂; subst; sym; trans)
open import Relation.Nullary.Decidable.Core using (yes; no)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier using (pair)
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as FiniteL2
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreCarrier as Block
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact as Sums
import DASHI.Physics.YangMills.BalabanFiniteSumFubiniExact as Fubini
import DASHI.Physics.YangMills.BalabanP33FiniteWeightedSchurSquaredExact as Schur
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionNormSquaredExact as Norm
import DASHI.Physics.YangMills.BalabanP33PhysicalCoordinateBasisExact as Basis
import DASHI.Physics.YangMills.BalabanP33PhysicalSU2FiniteCoordinatesExact as Coordinates
import DASHI.Physics.YangMills.BalabanP33PeriodicFourDimensionalHodgeIdentityExact as Periodic
import DASHI.Physics.YangMills.BalabanP33PhysicalPeriodicOpenReferenceBridgeExact as Bridge
import DASHI.Physics.YangMills.BalabanP33PhysicalRationalWilsonPlaquetteJetExact as Physical
import DASHI.Physics.YangMills.BalabanP33PhysicalBackgroundGaugeParameterizedYoungExact as Relaxed
import DASHI.Physics.YangMills.BalabanP33LiteralBondCellIncidenceExact as Incidence
import DASHI.Physics.YangMills.BalabanPath4AxisAverageExact as Path4
import DASHI.Physics.YangMills.BalabanSelectedCombinedConstraintRowCarrierExact as RowCarrier
import DASHI.Physics.YangMills.BalabanSelectedBackgroundGaugeConstraintMatrixExact as GaugeMatrix
import DASHI.Physics.YangMills.BalabanSelectedBackgroundGaugeConstraintStencilExact as Stencil
import DASHI.Physics.YangMills.BalabanSelectedBackgroundGaugeAdjointDefectExact as Defect
import DASHI.Physics.YangMills.BalabanFiniteRectangularAbsoluteMassExact as Mass

entryMagnitude entryMagnitudeSquare : ℚ
entryMagnitude = + 1 / 1024
entryMagnitudeSquare = + 1 / 1048576

defectRowMassBound defectColumnMassBound : ℚ
defectRowMassBound = + 3 / 128
defectColumnMassBound = + 3 / 512

gaugeRows : List Defect.GaugeRow
gaugeRows = Defect.gaugeRows

physicalColumns : List Coordinates.PhysicalSU2Coordinate4
physicalColumns = Coordinates.physicalSU2Coordinates4

gaugeDefectEntrySquareBelowColumnNorm :
  ∀ background row column →
  Defect.gaugeDefectMatrix background row column
    * Defect.gaugeDefectMatrix background row column
  ≤ Defect.gaugeDefectColumnNormSq background column
gaugeDefectEntrySquareBelowColumnNorm background row column =
  let
    selector = RowCarrier.selectedGaugeRowFiniteSelector
    value = λ candidate →
      Defect.gaugeDefectMatrix background candidate column
      * Defect.gaugeDefectMatrix background candidate column

    pointwise : ∀ candidate →
      value candidate
        * Basis.kronecker (Basis.decide selector) candidate row
      ≤ value candidate
    pointwise candidate with Basis.decide selector candidate row
    ... | yes refl = ℚP.≤-refl
    ... | no _ =
      subst
        (λ lower → lower ≤ value candidate)
        (ℚRing.solve [])
        (FiniteL2.squareNonnegative
          (Defect.gaugeDefectMatrix background candidate column))

    selectedBelow = Schur.sumPointwiseBelow
      (Basis.elements selector) _ _ pointwise
    selectedExact = Basis.selectorExact selector value row
  in
  subst
    (λ lower → lower ≤ Defect.gaugeDefectColumnNormSq background column)
    selectedExact selectedBelow

selectedColumnSquareCoefficientExact :
  Defect.sixteenDelta Relaxed.fourRhoSquare ≡ entryMagnitudeSquare
selectedColumnSquareCoefficientExact = ℚRing.solve []

selectedGaugeDefectEntrySquareBound :
  ∀ background → Relaxed.RelaxedInverseLinkRadius background →
  ∀ row column →
  Defect.gaugeDefectMatrix background row column
    * Defect.gaugeDefectMatrix background row column
  ≤ entryMagnitudeSquare
selectedGaugeDefectEntrySquareBound background radius row column =
  ℚP.≤-trans
    (gaugeDefectEntrySquareBelowColumnNorm background row column)
    (subst
      (λ upper → Defect.gaugeDefectColumnNormSq background column ≤ upper)
      selectedColumnSquareCoefficientExact
      (Defect.gaugeDefectColumnBound
        background Relaxed.fourRhoSquare
        (Relaxed.deltaNonnegative Relaxed.relaxedGaugeParameters)
        radius column))

entryMagnitudeSquareExact :
  entryMagnitudeSquare ≡ entryMagnitude * entryMagnitude
entryMagnitudeSquareExact = ℚRing.solve []

squareBoundImpliesEntryAbsoluteBound : ∀ value →
  value * value ≤ entryMagnitudeSquare →
  ∣ value ∣ ≤ entryMagnitude
squareBoundImpliesEntryAbsoluteBound value squareBound
  with ℚP.≤-total ∣ value ∣ entryMagnitude
... | inj₁ alreadyBelow = alreadyBelow
... | inj₂ magnitudeBelow =
  let
    magnitudeNonnegative : 0ℚ ≤ entryMagnitude
    magnitudeNonnegative = ℚP.nonNegative⁻¹ entryMagnitude

    instance
      magnitudeNN : NonNegative entryMagnitude
      magnitudeNN = ℚ.nonNegative magnitudeNonnegative

    absoluteSquareBound :
      ∣ value ∣ * ∣ value ∣ ≤ entryMagnitude * entryMagnitude
    absoluteSquareBound =
      subst
        (λ lower → lower ≤ entryMagnitude * entryMagnitude)
        (sym (Schur.absoluteSquareExact value))
        (subst
          (λ upper → value * value ≤ upper)
          entryMagnitudeSquareExact squareBound)

    lowerProduct :
      entryMagnitude * entryMagnitude ≤ entryMagnitude * ∣ value ∣
    lowerProduct = ℚP.*-monoˡ-≤-nonNeg entryMagnitude magnitudeBelow

    absoluteSquareBelowMixed :
      ∣ value ∣ * ∣ value ∣ ≤ ∣ value ∣ * entryMagnitude
    absoluteSquareBelowMixed =
      subst
        (λ upper → ∣ value ∣ * ∣ value ∣ ≤ upper)
        (ℚP.*-comm entryMagnitude ∣ value ∣)
        (ℚP.≤-trans absoluteSquareBound lowerProduct)

    magnitudePositive : 0ℚ < entryMagnitude
    magnitudePositive = ℚP.positive⁻¹ entryMagnitude

    absolutePositive : 0ℚ < ∣ value ∣
    absolutePositive = ℚP.<-≤-trans magnitudePositive magnitudeBelow

    instance
      absolutePositiveInstance : Positive ∣ value ∣
      absolutePositiveInstance = ℚ.positive absolutePositive
  in
  ℚP.*-cancelˡ-≤-pos ∣ value ∣ absoluteSquareBelowMixed

selectedGaugeDefectEntryAbsoluteBound :
  ∀ background → Relaxed.RelaxedInverseLinkRadius background →
  ∀ row column →
  ∣ Defect.gaugeDefectMatrix background row column ∣ ≤ entryMagnitude
selectedGaugeDefectEntryAbsoluteBound background radius row column =
  squareBoundImpliesEntryAbsoluteBound
    (Defect.gaugeDefectMatrix background row column)
    (selectedGaugeDefectEntrySquareBound background radius row column)

siteKronecker : Periodic.Site4 → Periodic.Site4 → ℚ
siteKronecker = Basis.kronecker (Basis.decide Basis.site4FiniteSelector)

siteKroneckerSymmetric : ∀ left right →
  siteKronecker left right ≡ siteKronecker right left
siteKroneckerSymmetric left right
  with Basis.decide Basis.site4FiniteSelector left right
... | yes refl with Basis.decide Basis.site4FiniteSelector right right
...   | yes _ = refl
...   | no different = ⊥-elim (different refl)
... | no different with Basis.decide Basis.site4FiniteSelector right left
...   | yes equality = ⊥-elim (different (sym equality))
...   | no _ = refl

siteSelectorScaledExact : ∀ coefficient target →
  Sums.sumRational (Block.physicalBlockSites Path4.side4)
    (λ candidate → coefficient * siteKronecker candidate target)
  ≡ coefficient
siteSelectorScaledExact coefficient target =
  Basis.selectorExact Basis.site4FiniteSelector (λ _ → coefficient) target

sumRationalAddExact : ∀ {A : Set} values (left right : A → ℚ) →
  Sums.sumRational values (λ value → left value + right value)
  ≡ Sums.sumRational values left + Sums.sumRational values right
sumRationalAddExact [] left right = ℚRing.solve []
sumRationalAddExact (value ∷ values) left right
  rewrite sumRationalAddExact values left right =
  ℚRing.solve-∀
    (left value) (right value)
    (Sums.sumRational values left) (Sums.sumRational values right)

defectStencilMajorant : Defect.GaugeRow → Coordinates.PhysicalSU2Coordinate4 → ℚ
defectStencilMajorant
    (pair rowCoordinate rowSite)
    (pair columnCoordinate (pair columnAxis columnSite)) =
  entryMagnitude
    * (siteKronecker columnSite rowSite
      + siteKronecker columnSite
          (Periodic.shiftBackward columnAxis rowSite))

entryMagnitudeBelowTwice : entryMagnitude ≤ entryMagnitude + entryMagnitude
entryMagnitudeBelowTwice =
  Norm.nonnegativeDifferenceImpliesBelow
    (subst
      (λ difference → 0ℚ ≤ difference)
      (sym (ℚRing.solve [] :
        (entryMagnitude + entryMagnitude) - entryMagnitude ≡ entryMagnitude))
      (ℚP.nonNegative⁻¹ entryMagnitude))

selectedGaugeDefectEntryBelowStencilMajorant :
  ∀ background → Relaxed.RelaxedInverseLinkRadius background →
  ∀ row column →
  ∣ Defect.gaugeDefectMatrix background row column ∣
  ≤ defectStencilMajorant row column
selectedGaugeDefectEntryBelowStencilMajorant
    background radius
    (pair rowCoordinate rowSite)
    (pair columnCoordinate (pair columnAxis columnSite))
  with Basis.decide Basis.site4FiniteSelector columnSite rowSite
     | Basis.decide Basis.site4FiniteSelector
         columnSite (Periodic.shiftBackward columnAxis rowSite)
... | yes refl | yes _ =
  ℚP.≤-trans
    (selectedGaugeDefectEntryAbsoluteBound background radius
      (pair rowCoordinate rowSite)
      (pair columnCoordinate (pair columnAxis rowSite)))
    (subst
      (λ upper → entryMagnitude ≤ upper)
      (sym (ℚRing.solve [] :
        entryMagnitude * (1ℚ + 1ℚ)
        ≡ entryMagnitude + entryMagnitude))
      entryMagnitudeBelowTwice)
... | yes refl | no _ =
  selectedGaugeDefectEntryAbsoluteBound background radius
    (pair rowCoordinate rowSite)
    (pair columnCoordinate (pair columnAxis rowSite))
... | no _ | yes _ =
  selectedGaugeDefectEntryAbsoluteBound background radius
    (pair rowCoordinate rowSite)
    (pair columnCoordinate (pair columnAxis columnSite))
... | no currentDifferent | no backwardDifferent =
  let
    row = pair rowCoordinate rowSite
    column = pair columnCoordinate (pair columnAxis columnSite)

    outside : Stencil.GaugeConstraintSpatialSupport row column → ⊥
    outside (Stencil.currentSiteSupport equality) = currentDifferent equality
    outside (Stencil.backwardSiteSupport equality) = backwardDifferent equality

    backgroundZero =
      Stencil.selectedBackgroundGaugeConstraintMatrixOutsideStencilZero
        background row column outside
    flatZero =
      Stencil.selectedBackgroundGaugeConstraintMatrixOutsideStencilZero
        Physical.identityBackground row column outside

    flatEntry = GaugeMatrix.selectedBackgroundGaugeConstraintMatrix
      Physical.identityBackground row column

    defectZero : Defect.gaugeDefectMatrix background row column ≡ 0ℚ
    defectZero =
      trans
        (cong (_- flatEntry) backgroundZero)
        (trans
          (cong (0ℚ -_) flatZero)
          (ℚRing.solve []))
  in
  subst
    (λ entry → ∣ entry ∣ ≤ 0ℚ)
    (sym defectZero)
    ℚP.≤-refl

rowSiteMajorantSumExact : ∀ axis rowSite →
  Sums.sumRational (Block.physicalBlockSites Path4.side4)
    (λ columnSite →
      entryMagnitude
        * (siteKronecker columnSite rowSite
          + siteKronecker columnSite
              (Periodic.shiftBackward axis rowSite)))
  ≡ entryMagnitude + entryMagnitude
rowSiteMajorantSumExact axis rowSite =
  trans
    (Sums.sumRationalCong
      (Block.physicalBlockSites Path4.side4) _ _
      (λ columnSite → ℚRing.solve-∀
        (siteKronecker columnSite rowSite)
        (siteKronecker columnSite (Periodic.shiftBackward axis rowSite))))
    (trans
      (sumRationalAddExact
        (Block.physicalBlockSites Path4.side4)
        (λ columnSite → entryMagnitude * siteKronecker columnSite rowSite)
        (λ columnSite → entryMagnitude
          * siteKronecker columnSite (Periodic.shiftBackward axis rowSite)))
      (cong₂ _+_
        (siteSelectorScaledExact entryMagnitude rowSite)
        (siteSelectorScaledExact entryMagnitude
          (Periodic.shiftBackward axis rowSite))))

columnShiftedSiteMajorantSumExact : ∀ axis columnSite →
  Sums.sumRational (Block.physicalBlockSites Path4.side4)
    (λ rowSite →
      entryMagnitude
        * siteKronecker columnSite (Periodic.shiftBackward axis rowSite))
  ≡ entryMagnitude
columnShiftedSiteMajorantSumExact axis columnSite =
  let
    term : Periodic.Site4 → ℚ
    term site = entryMagnitude * siteKronecker site columnSite

    symmetric :
      Sums.sumRational (Block.physicalBlockSites Path4.side4)
        (λ rowSite → entryMagnitude
          * siteKronecker columnSite (Periodic.shiftBackward axis rowSite))
      ≡ Sums.sumRational (Block.physicalBlockSites Path4.side4)
        (λ rowSite → term (Periodic.shiftBackward axis rowSite))
    symmetric =
      Sums.sumRationalCong
        (Block.physicalBlockSites Path4.side4) _ _
        (λ rowSite → cong (entryMagnitude *_)
          (siteKroneckerSymmetric columnSite
            (Periodic.shiftBackward axis rowSite)))

    toPeriodic = sym
      (Bridge.sumSitesMatchesGlobalSiteSum
        (λ rowSite → term (Periodic.shiftBackward axis rowSite)))
    invariant = Periodic.sumSitesBackwardInvariant term axis
    fromPeriodic = Bridge.sumSitesMatchesGlobalSiteSum term
  in
  trans symmetric
    (trans toPeriodic
      (trans invariant
        (trans fromPeriodic
          (siteSelectorScaledExact entryMagnitude columnSite))))

columnSiteMajorantSumExact : ∀ axis columnSite →
  Sums.sumRational (Block.physicalBlockSites Path4.side4)
    (λ rowSite → entryMagnitude
      * (siteKronecker columnSite rowSite
        + siteKronecker columnSite (Periodic.shiftBackward axis rowSite)))
  ≡ entryMagnitude + entryMagnitude
columnSiteMajorantSumExact axis columnSite =
  trans
    (Sums.sumRationalCong
      (Block.physicalBlockSites Path4.side4) _ _
      (λ rowSite → ℚRing.solve-∀
        (siteKronecker columnSite rowSite)
        (siteKronecker columnSite (Periodic.shiftBackward axis rowSite))))
    (trans
      (sumRationalAddExact
        (Block.physicalBlockSites Path4.side4)
        (λ rowSite → entryMagnitude * siteKronecker columnSite rowSite)
        (λ rowSite → entryMagnitude
          * siteKronecker columnSite (Periodic.shiftBackward axis rowSite)))
      (cong₂ _+_
        (trans
          (Sums.sumRationalCong
            (Block.physicalBlockSites Path4.side4) _ _
            (λ rowSite → cong (entryMagnitude *_)
              (siteKroneckerSymmetric columnSite rowSite)))
          (siteSelectorScaledExact entryMagnitude columnSite))
        (columnShiftedSiteMajorantSumExact axis columnSite)))

defectStencilMajorantRowMassExact : ∀ row →
  Sums.sumRational physicalColumns (defectStencilMajorant row)
  ≡ defectRowMassBound
defectStencilMajorantRowMassExact (pair rowCoordinate rowSite) =
  trans
    (Fubini.sumCartesian
      Coordinates.lieCoordinates3 Incidence.bondCells4
      (defectStencilMajorant (pair rowCoordinate rowSite)))
    (trans
      (Sums.sumRationalCong Coordinates.lieCoordinates3 _
        (λ _ → + 1 / 128)
        (λ columnCoordinate →
          trans
            (Fubini.sumCartesian Bridge.axes4
              (Block.physicalBlockSites Path4.side4)
              (λ cell → defectStencilMajorant (pair rowCoordinate rowSite)
                (pair columnCoordinate cell)))
            (trans
              (Sums.sumRationalCong Bridge.axes4 _
                (λ _ → entryMagnitude + entryMagnitude)
                (λ axis → rowSiteMajorantSumExact axis rowSite))
              (ℚRing.solve [])))))
      (ℚRing.solve []))

defectStencilMajorantColumnMassExact : ∀ column →
  Sums.sumRational gaugeRows (λ row → defectStencilMajorant row column)
  ≡ defectColumnMassBound
defectStencilMajorantColumnMassExact
    (pair columnCoordinate (pair columnAxis columnSite)) =
  trans
    (Fubini.sumCartesian Coordinates.lieCoordinates3
      (Block.physicalBlockSites Path4.side4)
      (λ row → defectStencilMajorant row
        (pair columnCoordinate (pair columnAxis columnSite))))
    (trans
      (Sums.sumRationalCong Coordinates.lieCoordinates3 _
        (λ _ → entryMagnitude + entryMagnitude)
        (λ rowCoordinate → columnSiteMajorantSumExact columnAxis columnSite))
      (ℚRing.solve []))

selectedGaugeDefectAbsoluteRowMassBound :
  ∀ background → Relaxed.RelaxedInverseLinkRadius background →
  ∀ row →
  Mass.absoluteRectRowMass physicalColumns
    (Defect.gaugeDefectMatrix background) row
  ≤ defectRowMassBound
selectedGaugeDefectAbsoluteRowMassBound background radius row =
  let
    summed = Schur.sumPointwiseBelow physicalColumns _ _
      (selectedGaugeDefectEntryBelowStencilMajorant background radius row)
  in
  subst
    (λ upper →
      Mass.absoluteRectRowMass physicalColumns
        (Defect.gaugeDefectMatrix background) row ≤ upper)
    (defectStencilMajorantRowMassExact row)
    summed

selectedGaugeDefectAbsoluteColumnMassBound :
  ∀ background → Relaxed.RelaxedInverseLinkRadius background →
  ∀ column →
  Mass.absoluteRectColumnMass gaugeRows
    (Defect.gaugeDefectMatrix background) column
  ≤ defectColumnMassBound
selectedGaugeDefectAbsoluteColumnMassBound background radius column =
  let
    summed = Schur.sumPointwiseBelow gaugeRows _ _
      (λ row → selectedGaugeDefectEntryBelowStencilMajorant
        background radius row column)
  in
  subst
    (λ upper →
      Mass.absoluteRectColumnMass gaugeRows
        (Defect.gaugeDefectMatrix background) column ≤ upper)
    (defectStencilMajorantColumnMassExact column)
    summed

selectedGaugeDefectEntryAbsoluteLevel : ProofLevel
selectedGaugeDefectEntryAbsoluteLevel = machineChecked

selectedGaugeDefectAbsoluteMassLevel : ProofLevel
selectedGaugeDefectAbsoluteMassLevel = machineChecked
