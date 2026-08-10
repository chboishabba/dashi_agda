module DASHI.Physics.YangMills.BalabanSelectedFlatGaugeConstraintAbsoluteMassExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Tadeusz Bałaban,
-- "Propagators and Renormalization Transformations for Lattice Gauge
-- Theories. I", Communications in Mathematical Physics 95 (1984), 17--40.
-- DOI: 10.1007/BF01215223.
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
-- Compute the l1 absolute masses of the literal identity-background selected
-- gauge matrix L_0 directly from the already-proved transpose identification
-- L_0^* = -grad_periodic.  A gauge-row Kronecker basis at (a,x) gives
--
--   L_0((a,x),(b,mu,y))
--     = - delta_ab [ delta_{x,y+mu} - delta_{x,y} ].
--
-- Summing the corresponding positive stencil majorant on the side-four torus
-- gives the sharp uniform masses
--
--   sup_row sum_column |L_0(row,column)| <= 8,
--   sup_column sum_row |L_0(row,column)| <= 2.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_; -_; _≤_; ∣_∣)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using
  (cong; cong₂; subst; sym; trans)
open import Relation.Nullary.Decidable.Core using (yes; no)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier using (pair)
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreCarrier as Block
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact as Sums
import DASHI.Physics.YangMills.BalabanFiniteSumFubiniExact as Fubini
import DASHI.Physics.YangMills.BalabanP33FiniteWeightedSchurSquaredExact as Schur
import DASHI.Physics.YangMills.BalabanP33PhysicalCoordinateBasisExact as Basis
import DASHI.Physics.YangMills.BalabanP33PhysicalSU2FiniteCoordinatesExact as Coordinates
import DASHI.Physics.YangMills.BalabanP33PeriodicFourDimensionalHodgeIdentityExact as Periodic
import DASHI.Physics.YangMills.BalabanP33PhysicalPeriodicOpenReferenceBridgeExact as Bridge
import DASHI.Physics.YangMills.BalabanP33PhysicalFlatGaugeDivergenceIdentificationExact as FlatGauge
import DASHI.Physics.YangMills.BalabanP33PhysicalBackgroundGaugeFirstExact as GaugeFirst
import DASHI.Physics.YangMills.BalabanPath4AxisAverageExact as Path4
import DASHI.Physics.YangMills.BalabanP33LiteralBondCellIncidenceExact as Incidence
import DASHI.Physics.YangMills.BalabanSelectedCombinedConstraintRowCarrierExact as Rows
import DASHI.Physics.YangMills.BalabanSelectedFlatGaugeAdjointGramFloorExact as Flat
import DASHI.Physics.YangMills.BalabanFiniteRectangularAbsoluteMassExact as Mass

flatRows = Basis.elements Rows.selectedGaugeRowFiniteSelector
flatColumns = Coordinates.physicalSU2Coordinates4

flatRowMassBound flatColumnMassBound : ℚ
flatRowMassBound = + 8 / 1
flatColumnMassBound = + 2 / 1

gaugeRowBasis : FlatGauge.GaugeCoordinate4 → Flat.GaugeMultiplier
gaugeRowBasis target candidate =
  Basis.kronecker
    (Basis.decide Rows.selectedGaugeRowFiniteSelector)
    candidate target

flatMatrixEntryFromAdjointExact : ∀ row column →
  Flat.actualFlatGaugeAdjoint (gaugeRowBasis row) column
  ≡ Flat.identityGaugeConstraintMatrix row column
flatMatrixEntryFromAdjointExact row column =
  Basis.selectorExact Rows.selectedGaugeRowFiniteSelector
    (λ candidate → Flat.identityGaugeConstraintMatrix candidate column)
    row

lieKronecker : Coordinates.LieCoordinate3 → Coordinates.LieCoordinate3 → ℚ
lieKronecker =
  Basis.kronecker (Basis.decide Basis.lieCoordinateFiniteSelector)

siteKronecker : Periodic.Site4 → Periodic.Site4 → ℚ
siteKronecker = Basis.kronecker (Basis.decide Basis.site4FiniteSelector)

gaugeRowBasisFactorExact : ∀ rowCoordinate rowSite coordinate site →
  gaugeRowBasis (pair rowCoordinate rowSite) (pair coordinate site)
  ≡ lieKronecker coordinate rowCoordinate * siteKronecker site rowSite
gaugeRowBasisFactorExact rowCoordinate rowSite coordinate site =
  Basis.productKroneckerFactorExact
    (Basis.decide Basis.lieCoordinateFiniteSelector)
    (Basis.decide Basis.site4FiniteSelector)
    coordinate rowCoordinate site rowSite

flatMatrixEntryKroneckerExact :
  ∀ rowCoordinate rowSite columnCoordinate columnAxis columnSite →
  Flat.identityGaugeConstraintMatrix
      (pair rowCoordinate rowSite)
      (pair columnCoordinate (pair columnAxis columnSite))
  ≡ - (lieKronecker columnCoordinate rowCoordinate
      * (siteKronecker (Periodic.shiftForward columnAxis columnSite) rowSite
        - siteKronecker columnSite rowSite))
flatMatrixEntryKroneckerExact
    rowCoordinate rowSite columnCoordinate columnAxis columnSite =
  let
    row = pair rowCoordinate rowSite
    column = pair columnCoordinate (pair columnAxis columnSite)
    multiplier = gaugeRowBasis row

    toGradient = Flat.actualFlatGaugeAdjointPointwiseExact multiplier column

    forwardFactor = gaugeRowBasisFactorExact
      rowCoordinate rowSite columnCoordinate
      (Periodic.shiftForward columnAxis columnSite)
    currentFactor = gaugeRowBasisFactorExact
      rowCoordinate rowSite columnCoordinate columnSite

    expanded :
      - Periodic.forwardDifference columnAxis
          (Flat.multiplierField multiplier columnCoordinate) columnSite
      ≡ - (lieKronecker columnCoordinate rowCoordinate
          * (siteKronecker (Periodic.shiftForward columnAxis columnSite) rowSite
            - siteKronecker columnSite rowSite))
    expanded rewrite forwardFactor | currentFactor =
      ℚRing.solve-∀
        (lieKronecker columnCoordinate rowCoordinate)
        (siteKronecker (Periodic.shiftForward columnAxis columnSite) rowSite)
        (siteKronecker columnSite rowSite)
  in
  trans
    (sym (flatMatrixEntryFromAdjointExact row column))
    (trans toGradient expanded)

flatStencilMajorant : FlatGauge.GaugeCoordinate4 → Coordinates.PhysicalSU2Coordinate4 → ℚ
flatStencilMajorant
    (pair rowCoordinate rowSite)
    (pair columnCoordinate (pair columnAxis columnSite)) =
  lieKronecker columnCoordinate rowCoordinate
    * (siteKronecker (Periodic.shiftForward columnAxis columnSite) rowSite
      + siteKronecker columnSite rowSite)

kroneckerDifferenceAbsoluteBound :
  ∀ lie first second →
  (lie ≡ 0ℚ ⊎ lie ≡ 1ℚ) →
  (first ≡ 0ℚ ⊎ first ≡ 1ℚ) →
  (second ≡ 0ℚ ⊎ second ≡ 1ℚ) →
  ∣ - (lie * (first - second)) ∣ ≤ lie * (first + second)
kroneckerDifferenceAbsoluteBound .0ℚ first second (inj₁ refl) firstBit secondBit =
  ℚP.≤-refl
kroneckerDifferenceAbsoluteBound .1ℚ .0ℚ .0ℚ
    (inj₂ refl) (inj₁ refl) (inj₁ refl) = ℚP.≤-refl
kroneckerDifferenceAbsoluteBound .1ℚ .0ℚ .1ℚ
    (inj₂ refl) (inj₁ refl) (inj₂ refl) = ℚP.≤-refl
kroneckerDifferenceAbsoluteBound .1ℚ .1ℚ .0ℚ
    (inj₂ refl) (inj₂ refl) (inj₁ refl) = ℚP.≤-refl
kroneckerDifferenceAbsoluteBound .1ℚ .1ℚ .1ℚ
    (inj₂ refl) (inj₂ refl) (inj₂ refl) =
  subst
    (λ upper → 0ℚ ≤ upper)
    (sym (ℚRing.solve [] : 1ℚ * (1ℚ + 1ℚ) ≡ + 2 / 1))
    (ℚP.nonNegative⁻¹ (+ 2 / 1))

kroneckerBit : ∀ {A : Set} selector left right →
  let value = Basis.kronecker (Basis.decide selector) left right in
  value ≡ 0ℚ ⊎ value ≡ 1ℚ
kroneckerBit selector left right with Basis.decide selector left right
... | yes refl = inj₂ refl
... | no _ = inj₁ refl

flatEntryBelowStencilMajorant : ∀ row column →
  ∣ Flat.identityGaugeConstraintMatrix row column ∣
  ≤ flatStencilMajorant row column
flatEntryBelowStencilMajorant
    (pair rowCoordinate rowSite)
    (pair columnCoordinate (pair columnAxis columnSite)) =
  let
    lie = lieKronecker columnCoordinate rowCoordinate
    first = siteKronecker (Periodic.shiftForward columnAxis columnSite) rowSite
    second = siteKronecker columnSite rowSite
    raw = kroneckerDifferenceAbsoluteBound lie first second
      (kroneckerBit Basis.lieCoordinateFiniteSelector
        columnCoordinate rowCoordinate)
      (kroneckerBit Basis.site4FiniteSelector
        (Periodic.shiftForward columnAxis columnSite) rowSite)
      (kroneckerBit Basis.site4FiniteSelector columnSite rowSite)
  in
  subst
    (λ entry → ∣ entry ∣ ≤ lie * (first + second))
    (sym (flatMatrixEntryKroneckerExact
      rowCoordinate rowSite columnCoordinate columnAxis columnSite))
    raw

siteSelectorOneExact : ∀ target →
  Sums.sumRational (Block.physicalBlockSites Path4.side4)
    (λ candidate → siteKronecker candidate target)
  ≡ 1ℚ
siteSelectorOneExact target =
  Basis.selectorExact Basis.site4FiniteSelector (λ _ → 1ℚ) target

siteForwardSelectorOneExact : ∀ axis target →
  Sums.sumRational (Block.physicalBlockSites Path4.side4)
    (λ candidate → siteKronecker (Periodic.shiftForward axis candidate) target)
  ≡ 1ℚ
siteForwardSelectorOneExact axis target =
  let
    term = λ site → siteKronecker site target
  in
  trans
    (sym (Bridge.sumSitesMatchesGlobalSiteSum
      (λ candidate → term (Periodic.shiftForward axis candidate))))
    (trans
      (Periodic.sumSitesForwardInvariant term axis)
      (trans
        (Bridge.sumSitesMatchesGlobalSiteSum term)
        (siteSelectorOneExact target)))

lieSelectorScaledExact : ∀ coefficient target →
  Sums.sumRational Coordinates.lieCoordinates3
    (λ candidate → coefficient * lieKronecker candidate target)
  ≡ coefficient
lieSelectorScaledExact coefficient target =
  Basis.selectorExact Basis.lieCoordinateFiniteSelector
    (λ _ → coefficient) target

rowAxisSiteMassExact : ∀ lie axis rowSite →
  Sums.sumRational (Block.physicalBlockSites Path4.side4)
    (λ columnSite →
      lie * (siteKronecker (Periodic.shiftForward axis columnSite) rowSite
        + siteKronecker columnSite rowSite))
  ≡ (+ 2 / 1) * lie
rowAxisSiteMassExact lie axis rowSite =
  trans
    (Sums.sumRationalCong
      (Block.physicalBlockSites Path4.side4) _ _
      (λ columnSite → ℚRing.solve-∀ lie
        (siteKronecker (Periodic.shiftForward axis columnSite) rowSite)
        (siteKronecker columnSite rowSite)))
    (trans
      (Fubini.sumRationalAdd
        (Block.physicalBlockSites Path4.side4)
        (λ columnSite → lie * siteKronecker
          (Periodic.shiftForward axis columnSite) rowSite)
        (λ columnSite → lie * siteKronecker columnSite rowSite))
      (trans
        (cong₂ _+_
          (trans
            (Sums.sumRationalScale lie
              (Block.physicalBlockSites Path4.side4)
              (λ columnSite → siteKronecker
                (Periodic.shiftForward axis columnSite) rowSite))
            (cong (lie *_) (siteForwardSelectorOneExact axis rowSite)))
          (trans
            (Sums.sumRationalScale lie
              (Block.physicalBlockSites Path4.side4)
              (λ columnSite → siteKronecker columnSite rowSite))
            (cong (lie *_) (siteSelectorOneExact rowSite))))
        (ℚRing.solve-∀ lie)))

flatStencilRowMassExact : ∀ row →
  Sums.sumRational flatColumns (flatStencilMajorant row)
  ≡ flatRowMassBound
flatStencilRowMassExact (pair rowCoordinate rowSite) =
  trans
    (Fubini.sumCartesian Coordinates.lieCoordinates3 Incidence.bondCells4
      (flatStencilMajorant (pair rowCoordinate rowSite)))
    (trans
      (Sums.sumRationalCong Coordinates.lieCoordinates3 _
        (λ columnCoordinate →
          flatRowMassBound * lieKronecker columnCoordinate rowCoordinate)
        (λ columnCoordinate →
          trans
            (Fubini.sumCartesian GaugeFirst.axes4
              (Block.physicalBlockSites Path4.side4)
              (λ cell →
                flatStencilMajorant (pair rowCoordinate rowSite)
                  (pair columnCoordinate cell)))
            (trans
              (Sums.sumRationalCong GaugeFirst.axes4 _
                (λ _ → (+ 2 / 1)
                  * lieKronecker columnCoordinate rowCoordinate)
                (λ axis → rowAxisSiteMassExact
                  (lieKronecker columnCoordinate rowCoordinate) axis rowSite))
              (ℚRing.solve-∀
                (lieKronecker columnCoordinate rowCoordinate))))))
      (trans
        (Sums.sumRationalCong Coordinates.lieCoordinates3 _ _
          (λ columnCoordinate →
            ℚP.*-comm flatRowMassBound
              (lieKronecker columnCoordinate rowCoordinate)))
        (lieSelectorScaledExact flatRowMassBound rowCoordinate)))

columnSiteMassExact : ∀ lie axis columnSite →
  Sums.sumRational (Block.physicalBlockSites Path4.side4)
    (λ rowSite →
      lie * (siteKronecker (Periodic.shiftForward axis columnSite) rowSite
        + siteKronecker columnSite rowSite))
  ≡ (+ 2 / 1) * lie
columnSiteMassExact lie axis columnSite =
  trans
    (Sums.sumRationalCong
      (Block.physicalBlockSites Path4.side4) _ _
      (λ rowSite → ℚRing.solve-∀ lie
        (siteKronecker (Periodic.shiftForward axis columnSite) rowSite)
        (siteKronecker columnSite rowSite)))
    (trans
      (Fubini.sumRationalAdd
        (Block.physicalBlockSites Path4.side4)
        (λ rowSite → lie * siteKronecker
          (Periodic.shiftForward axis columnSite) rowSite)
        (λ rowSite → lie * siteKronecker columnSite rowSite))
      (trans
        (cong₂ _+_
          (trans
            (Sums.sumRationalScale lie
              (Block.physicalBlockSites Path4.side4)
              (λ rowSite → siteKronecker
                (Periodic.shiftForward axis columnSite) rowSite))
            (cong (lie *_) (siteSelectorOneExact
              (Periodic.shiftForward axis columnSite))))
          (trans
            (Sums.sumRationalScale lie
              (Block.physicalBlockSites Path4.side4)
              (λ rowSite → siteKronecker columnSite rowSite))
            (cong (lie *_) (siteSelectorOneExact columnSite))))
        (ℚRing.solve-∀ lie)))

flatStencilColumnMassExact : ∀ column →
  Sums.sumRational flatRows (λ row → flatStencilMajorant row column)
  ≡ flatColumnMassBound
flatStencilColumnMassExact
    (pair columnCoordinate (pair columnAxis columnSite)) =
  trans
    (Fubini.sumCartesian Coordinates.lieCoordinates3
      (Block.physicalBlockSites Path4.side4)
      (λ row → flatStencilMajorant row
        (pair columnCoordinate (pair columnAxis columnSite))))
    (trans
      (Sums.sumRationalCong Coordinates.lieCoordinates3 _
        (λ rowCoordinate →
          flatColumnMassBound * lieKronecker columnCoordinate rowCoordinate)
        (λ rowCoordinate → columnSiteMassExact
          (lieKronecker columnCoordinate rowCoordinate)
          columnAxis columnSite))
      (trans
        (Sums.sumRationalCong Coordinates.lieCoordinates3 _ _
          (λ rowCoordinate →
            ℚP.*-comm flatColumnMassBound
              (lieKronecker columnCoordinate rowCoordinate)))
        (lieSelectorScaledExact flatColumnMassBound columnCoordinate)))

selectedFlatGaugeAbsoluteRowMassBound : ∀ row →
  Mass.absoluteRectRowMass flatColumns Flat.identityGaugeConstraintMatrix row
  ≤ flatRowMassBound
selectedFlatGaugeAbsoluteRowMassBound row =
  let
    summed = Schur.sumPointwiseBelow flatColumns _ _
      (flatEntryBelowStencilMajorant row)
  in
  subst
    (λ upper →
      Mass.absoluteRectRowMass flatColumns
        Flat.identityGaugeConstraintMatrix row ≤ upper)
    (flatStencilRowMassExact row)
    summed

selectedFlatGaugeAbsoluteColumnMassBound : ∀ column →
  Mass.absoluteRectColumnMass flatRows Flat.identityGaugeConstraintMatrix column
  ≤ flatColumnMassBound
selectedFlatGaugeAbsoluteColumnMassBound column =
  let
    summed = Schur.sumPointwiseBelow flatRows _ _
      (λ row → flatEntryBelowStencilMajorant row column)
  in
  subst
    (λ upper →
      Mass.absoluteRectColumnMass flatRows
        Flat.identityGaugeConstraintMatrix column ≤ upper)
    (flatStencilColumnMassExact column)
    summed

selectedFlatGaugeConstraintAbsoluteMassLevel : ProofLevel
selectedFlatGaugeConstraintAbsoluteMassLevel = machineChecked
