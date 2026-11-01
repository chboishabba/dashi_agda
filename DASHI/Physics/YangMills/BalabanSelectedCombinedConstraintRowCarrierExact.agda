module DASHI.Physics.YangMills.BalabanSelectedCombinedConstraintRowCarrierExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Tadeusz Bałaban,
-- "Averaging Operations for Lattice Gauge Theories",
-- Communications in Mathematical Physics 98 (1985), 17--51.
-- DOI: 10.1007/BF01211042.
--
-- Tadeusz Bałaban,
-- "Propagators for Lattice Gauge Theories in a Background Field",
-- Communications in Mathematical Physics 99 (1985), 389--434.
-- DOI: 10.1007/BF01240355.
--
-- Roger A. Horn; Charles R. Johnson,
-- "Matrix Analysis", second edition, Cambridge University Press, 2012.
-- DOI: 10.1017/CBO9781139020411.
--
-- DASHI CONTRIBUTION
--
-- Construct the exact finite Kronecker carrier for the tagged sum of the
-- twelve block-average rows and the 768 covariant gauge rows.  The proof
-- establishes the selector law separately on both summands and proves all
-- cross-tag selector terms vanish.  The resulting 780-row carrier is now a
-- concrete input to the combined Gram/pseudoinverse lane; no abstract
-- multiplier set or assumed identity matrix is accepted.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; [])
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _+_; _*_)
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using
  (cong; cong₂; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier using
  (Dec; yes; no; Empty; DecidableEquality; map; _++_)
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact as Sums
import DASHI.Physics.YangMills.BalabanFiniteSumFubiniExact as Fubini
import DASHI.Physics.YangMills.BalabanConstructiveRationalMatrixInverseExact as Matrix
import DASHI.Physics.YangMills.BalabanP33PhysicalCoordinateBasisExact as Basis
import DASHI.Physics.YangMills.BalabanP33PhysicalFlatGaugeDivergenceIdentificationExact as FlatGauge
import DASHI.Physics.YangMills.BalabanSelectedBackgroundCombinedConstraintMatrixExact as Combined
import DASHI.Physics.YangMills.BalabanSelectedBlockAverageRowCarrierExact as AverageRows

emptyElim : ∀ {A : Set} → Empty → A
emptyElim ()

averageRowInjective : ∀ {left right} →
  Combined.averageConstraintRow left
  ≡ Combined.averageConstraintRow right →
  left ≡ right
averageRowInjective refl = refl

gaugeRowInjective : ∀ {left right} →
  Combined.gaugeConstraintRow left
  ≡ Combined.gaugeConstraintRow right →
  left ≡ right
gaugeRowInjective refl = refl

averageNotGauge : ∀ {left right} →
  Combined.averageConstraintRow left
  ≡ Combined.gaugeConstraintRow right → Empty
averageNotGauge ()

gaugeNotAverage : ∀ {left right} →
  Combined.gaugeConstraintRow left
  ≡ Combined.averageConstraintRow right → Empty
gaugeNotAverage ()

selectedGaugeRowFiniteSelector :
  Basis.FiniteSelector FlatGauge.GaugeCoordinate4
selectedGaugeRowFiniteSelector =
  Basis.productFiniteSelector
    Basis.lieCoordinateFiniteSelector
    Basis.site4FiniteSelector

selectedCombinedConstraintRowDecidableEquality :
  DecidableEquality Combined.SelectedConstraintRow4
selectedCombinedConstraintRowDecidableEquality
    (Combined.averageConstraintRow left)
    (Combined.averageConstraintRow right)
  with Basis.decide AverageRows.selectedBlockAverageRowFiniteSelector left right
... | yes refl = yes refl
... | no different = no (λ equality → different (averageRowInjective equality))
selectedCombinedConstraintRowDecidableEquality
    (Combined.gaugeConstraintRow left)
    (Combined.gaugeConstraintRow right)
  with Basis.decide selectedGaugeRowFiniteSelector left right
... | yes refl = yes refl
... | no different = no (λ equality → different (gaugeRowInjective equality))
selectedCombinedConstraintRowDecidableEquality
    (Combined.averageConstraintRow left)
    (Combined.gaugeConstraintRow right) = no averageNotGauge
selectedCombinedConstraintRowDecidableEquality
    (Combined.gaugeConstraintRow left)
    (Combined.averageConstraintRow right) = no gaugeNotAverage

selectedCombinedConstraintRows : List Combined.SelectedConstraintRow4
selectedCombinedConstraintRows =
  map Combined.averageConstraintRow
    (Basis.elements AverageRows.selectedBlockAverageRowFiniteSelector)
  ++ map Combined.gaugeConstraintRow
    (Basis.elements selectedGaugeRowFiniteSelector)

averageKroneckerExact : ∀ left right →
  Basis.kronecker selectedCombinedConstraintRowDecidableEquality
    (Combined.averageConstraintRow left)
    (Combined.averageConstraintRow right)
  ≡ Basis.kronecker
      (Basis.decide AverageRows.selectedBlockAverageRowFiniteSelector)
      left right
averageKroneckerExact left right
  with Basis.decide AverageRows.selectedBlockAverageRowFiniteSelector left right
... | yes refl = refl
... | no _ = refl

gaugeKroneckerExact : ∀ left right →
  Basis.kronecker selectedCombinedConstraintRowDecidableEquality
    (Combined.gaugeConstraintRow left)
    (Combined.gaugeConstraintRow right)
  ≡ Basis.kronecker
      (Basis.decide selectedGaugeRowFiniteSelector)
      left right
gaugeKroneckerExact left right
  with Basis.decide selectedGaugeRowFiniteSelector left right
... | yes refl = refl
... | no _ = refl

averageGaugeKroneckerZero : ∀ left right →
  Basis.kronecker selectedCombinedConstraintRowDecidableEquality
    (Combined.averageConstraintRow left)
    (Combined.gaugeConstraintRow right)
  ≡ 0ℚ
averageGaugeKroneckerZero left right = refl

gaugeAverageKroneckerZero : ∀ left right →
  Basis.kronecker selectedCombinedConstraintRowDecidableEquality
    (Combined.gaugeConstraintRow left)
    (Combined.averageConstraintRow right)
  ≡ 0ℚ
gaugeAverageKroneckerZero left right = refl

averagePartExact :
  ∀ vector target →
  Sums.sumRational
    (map Combined.averageConstraintRow
      (Basis.elements AverageRows.selectedBlockAverageRowFiniteSelector))
    (λ candidate →
      vector candidate
      * Basis.kronecker selectedCombinedConstraintRowDecidableEquality
          candidate (Combined.averageConstraintRow target))
  ≡ vector (Combined.averageConstraintRow target)
averagePartExact vector target =
  trans
    (Fubini.sumRationalMap
      Combined.averageConstraintRow
      (Basis.elements AverageRows.selectedBlockAverageRowFiniteSelector)
      (λ candidate →
        vector candidate
        * Basis.kronecker selectedCombinedConstraintRowDecidableEquality
            candidate (Combined.averageConstraintRow target)))
    (trans
      (Sums.sumRationalCong
        (Basis.elements AverageRows.selectedBlockAverageRowFiniteSelector)
        (λ candidate →
          vector (Combined.averageConstraintRow candidate)
          * Basis.kronecker selectedCombinedConstraintRowDecidableEquality
              (Combined.averageConstraintRow candidate)
              (Combined.averageConstraintRow target))
        (λ candidate →
          vector (Combined.averageConstraintRow candidate)
          * Basis.kronecker
              (Basis.decide AverageRows.selectedBlockAverageRowFiniteSelector)
              candidate target)
        (λ candidate →
          cong (vector (Combined.averageConstraintRow candidate) *_)
            (averageKroneckerExact candidate target)))
      (Basis.selectorExact
        AverageRows.selectedBlockAverageRowFiniteSelector
        (λ candidate → vector (Combined.averageConstraintRow candidate))
        target))

gaugePartExact :
  ∀ vector target →
  Sums.sumRational
    (map Combined.gaugeConstraintRow
      (Basis.elements selectedGaugeRowFiniteSelector))
    (λ candidate →
      vector candidate
      * Basis.kronecker selectedCombinedConstraintRowDecidableEquality
          candidate (Combined.gaugeConstraintRow target))
  ≡ vector (Combined.gaugeConstraintRow target)
gaugePartExact vector target =
  trans
    (Fubini.sumRationalMap
      Combined.gaugeConstraintRow
      (Basis.elements selectedGaugeRowFiniteSelector)
      (λ candidate →
        vector candidate
        * Basis.kronecker selectedCombinedConstraintRowDecidableEquality
            candidate (Combined.gaugeConstraintRow target)))
    (trans
      (Sums.sumRationalCong
        (Basis.elements selectedGaugeRowFiniteSelector)
        (λ candidate →
          vector (Combined.gaugeConstraintRow candidate)
          * Basis.kronecker selectedCombinedConstraintRowDecidableEquality
              (Combined.gaugeConstraintRow candidate)
              (Combined.gaugeConstraintRow target))
        (λ candidate →
          vector (Combined.gaugeConstraintRow candidate)
          * Basis.kronecker
              (Basis.decide selectedGaugeRowFiniteSelector)
              candidate target)
        (λ candidate →
          cong (vector (Combined.gaugeConstraintRow candidate) *_)
            (gaugeKroneckerExact candidate target)))
      (Basis.selectorExact
        selectedGaugeRowFiniteSelector
        (λ candidate → vector (Combined.gaugeConstraintRow candidate))
        target))

averagePartZeroAtGauge :
  ∀ vector target →
  Sums.sumRational
    (map Combined.averageConstraintRow
      (Basis.elements AverageRows.selectedBlockAverageRowFiniteSelector))
    (λ candidate →
      vector candidate
      * Basis.kronecker selectedCombinedConstraintRowDecidableEquality
          candidate (Combined.gaugeConstraintRow target))
  ≡ 0ℚ
averagePartZeroAtGauge vector target =
  trans
    (Fubini.sumRationalMap
      Combined.averageConstraintRow
      (Basis.elements AverageRows.selectedBlockAverageRowFiniteSelector)
      (λ candidate →
        vector candidate
        * Basis.kronecker selectedCombinedConstraintRowDecidableEquality
            candidate (Combined.gaugeConstraintRow target)))
    (trans
      (Sums.sumRationalCong
        (Basis.elements AverageRows.selectedBlockAverageRowFiniteSelector)
        (λ candidate →
          vector (Combined.averageConstraintRow candidate)
          * Basis.kronecker selectedCombinedConstraintRowDecidableEquality
              (Combined.averageConstraintRow candidate)
              (Combined.gaugeConstraintRow target))
        (λ _ → 0ℚ)
        (λ candidate →
          trans
            (cong (vector (Combined.averageConstraintRow candidate) *_)
              (averageGaugeKroneckerZero candidate target))
            (ℚRing.solve [])))
      (Fubini.sumRationalZero
        (Basis.elements AverageRows.selectedBlockAverageRowFiniteSelector)))

gaugePartZeroAtAverage :
  ∀ vector target →
  Sums.sumRational
    (map Combined.gaugeConstraintRow
      (Basis.elements selectedGaugeRowFiniteSelector))
    (λ candidate →
      vector candidate
      * Basis.kronecker selectedCombinedConstraintRowDecidableEquality
          candidate (Combined.averageConstraintRow target))
  ≡ 0ℚ
gaugePartZeroAtAverage vector target =
  trans
    (Fubini.sumRationalMap
      Combined.gaugeConstraintRow
      (Basis.elements selectedGaugeRowFiniteSelector)
      (λ candidate →
        vector candidate
        * Basis.kronecker selectedCombinedConstraintRowDecidableEquality
            candidate (Combined.averageConstraintRow target)))
    (trans
      (Sums.sumRationalCong
        (Basis.elements selectedGaugeRowFiniteSelector)
        (λ candidate →
          vector (Combined.gaugeConstraintRow candidate)
          * Basis.kronecker selectedCombinedConstraintRowDecidableEquality
              (Combined.gaugeConstraintRow candidate)
              (Combined.averageConstraintRow target))
        (λ _ → 0ℚ)
        (λ candidate →
          trans
            (cong (vector (Combined.gaugeConstraintRow candidate) *_)
              (gaugeAverageKroneckerZero candidate target))
            (ℚRing.solve [])))
      (Fubini.sumRationalZero
        (Basis.elements selectedGaugeRowFiniteSelector)))

selectedCombinedConstraintRowSelectorExact :
  ∀ vector target →
  Sums.sumRational selectedCombinedConstraintRows
    (λ candidate →
      vector candidate
      * Basis.kronecker selectedCombinedConstraintRowDecidableEquality
          candidate target)
  ≡ vector target
selectedCombinedConstraintRowSelectorExact vector
    (Combined.averageConstraintRow target) =
  trans
    (Fubini.sumRationalAppend
      (map Combined.averageConstraintRow
        (Basis.elements AverageRows.selectedBlockAverageRowFiniteSelector))
      (map Combined.gaugeConstraintRow
        (Basis.elements selectedGaugeRowFiniteSelector))
      (λ candidate →
        vector candidate
        * Basis.kronecker selectedCombinedConstraintRowDecidableEquality
            candidate (Combined.averageConstraintRow target)))
    (trans
      (cong₂ _+_
        (averagePartExact vector target)
        (gaugePartZeroAtAverage vector target))
      (ℚRing.solve-∀ (vector (Combined.averageConstraintRow target))))
selectedCombinedConstraintRowSelectorExact vector
    (Combined.gaugeConstraintRow target) =
  trans
    (Fubini.sumRationalAppend
      (map Combined.averageConstraintRow
        (Basis.elements AverageRows.selectedBlockAverageRowFiniteSelector))
      (map Combined.gaugeConstraintRow
        (Basis.elements selectedGaugeRowFiniteSelector))
      (λ candidate →
        vector candidate
        * Basis.kronecker selectedCombinedConstraintRowDecidableEquality
            candidate (Combined.gaugeConstraintRow target)))
    (trans
      (cong₂ _+_
        (averagePartZeroAtGauge vector target)
        (gaugePartExact vector target))
      (ℚRing.solve-∀ (vector (Combined.gaugeConstraintRow target))))

selectedCombinedConstraintRowFiniteSelector :
  Basis.FiniteSelector Combined.SelectedConstraintRow4
selectedCombinedConstraintRowFiniteSelector = record
  { Basis.FiniteSelector.elements = selectedCombinedConstraintRows
  ; Basis.FiniteSelector.decide =
      selectedCombinedConstraintRowDecidableEquality
  ; Basis.FiniteSelector.selectorExact =
      selectedCombinedConstraintRowSelectorExact
  }

selectedCombinedConstraintRowDelta :
  Combined.SelectedConstraintRow4 →
  Combined.SelectedConstraintRow4 → ℚ
selectedCombinedConstraintRowDelta row column =
  Basis.kronecker selectedCombinedConstraintRowDecidableEquality column row

selectedCombinedConstraintRowDeltaActsAsIdentity :
  ∀ vector row →
  Sums.sumRational selectedCombinedConstraintRows
    (λ column →
      selectedCombinedConstraintRowDelta row column * vector column)
  ≡ vector row
selectedCombinedConstraintRowDeltaActsAsIdentity vector row =
  trans
    (Sums.sumRationalCong selectedCombinedConstraintRows
      (λ column →
        selectedCombinedConstraintRowDelta row column * vector column)
      (λ column →
        vector column
        * Basis.kronecker selectedCombinedConstraintRowDecidableEquality
            column row)
      (λ column → ℚRing.solve []))
    (selectedCombinedConstraintRowSelectorExact vector row)

selectedCombinedConstraintRowCarrier :
  Matrix.FiniteRationalCoordinates Combined.SelectedConstraintRow4
selectedCombinedConstraintRowCarrier = record
  { Matrix.FiniteRationalCoordinates.coordinates =
      selectedCombinedConstraintRows
  ; Matrix.FiniteRationalCoordinates.delta =
      selectedCombinedConstraintRowDelta
  ; Matrix.FiniteRationalCoordinates.deltaActsAsIdentity =
      selectedCombinedConstraintRowDeltaActsAsIdentity
  }

selectedCombinedConstraintRowCarrierLevel : ProofLevel
selectedCombinedConstraintRowCarrierLevel = machineChecked
