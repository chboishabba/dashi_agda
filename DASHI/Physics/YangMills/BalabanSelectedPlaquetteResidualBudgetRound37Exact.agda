module DASHI.Physics.YangMills.BalabanSelectedPlaquetteResidualBudgetRound37Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Tadeusz Bałaban,
-- "The Variational Problem and Background Fields in Renormalization Group
-- Method for Lattice Gauge Theories".
-- DOI: 10.1007/BF01229381.
--
-- Tadeusz Bałaban,
-- "Propagators for Lattice Gauge Theories in a Background Field".
-- DOI: 10.1007/BF01240355.
--
-- DASHI CONTRIBUTION
--
-- Replace one undifferentiated extraction-spillover bound by four uniquely
-- named sources: gauge repair, block-constraint repair, covariant transport,
-- and locality boundary.  The rational coefficient ledger is exact and sums
-- to the remaining singleton budget 55/18874368.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
import Data.Integer.Base as Int
open import Data.Rational.Base as ℚ using
  (ℚ; _/_; _+_; _*_; _≤_)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst)

gaugeCoefficient constraintCoefficient transportCoefficient boundaryCoefficient : ℚ
gaugeCoefficient = Int.+ 10 / 18874368
constraintCoefficient = Int.+ 10 / 18874368
transportCoefficient = Int.+ 15 / 18874368
boundaryCoefficient = Int.+ 20 / 18874368

totalResidualCoefficient : ℚ
totalResidualCoefficient = Int.+ 55 / 18874368

residualCoefficientLedgerExact :
  (gaugeCoefficient + constraintCoefficient)
  + (transportCoefficient + boundaryCoefficient)
  ≡ totalResidualCoefficient
residualCoefficientLedgerExact = solve []

record SelectedVariationResiduals : Set where
  constructor selected-variation-residuals
  field
    gaugeResidual : ℚ
    constraintResidual : ℚ
    transportResidual : ℚ
    boundaryResidual : ℚ

open SelectedVariationResiduals public

residualTotal : SelectedVariationResiduals → ℚ
residualTotal residuals =
  (gaugeResidual residuals + constraintResidual residuals)
  + (transportResidual residuals + boundaryResidual residuals)

record SelectedVariationResidualBounds
    (charge : ℚ)
    (residuals : SelectedVariationResiduals) : Set where
  constructor selected-variation-residual-bounds
  field
    gaugeBound :
      gaugeResidual residuals ≤ gaugeCoefficient * charge
    constraintBound :
      constraintResidual residuals ≤ constraintCoefficient * charge
    transportBound :
      transportResidual residuals ≤ transportCoefficient * charge
    boundaryBound :
      boundaryResidual residuals ≤ boundaryCoefficient * charge

open SelectedVariationResidualBounds public

fourResidualBoundsSum :
  ∀ {charge residuals} →
  SelectedVariationResidualBounds charge residuals →
  residualTotal residuals
  ≤
  ((gaugeCoefficient + constraintCoefficient)
    + (transportCoefficient + boundaryCoefficient)) * charge
fourResidualBoundsSum {charge} {residuals} bounds =
  let
    firstPair = ℚP.+-mono-≤
      (gaugeBound bounds) (constraintBound bounds)
    secondPair = ℚP.+-mono-≤
      (transportBound bounds) (boundaryBound bounds)
    allFour = ℚP.+-mono-≤ firstPair secondPair
  in
  subst
    (λ upper → residualTotal residuals ≤ upper)
    (solve (charge ∷ []))
    allFour

selectedVariationSpilloverUpper :
  ∀ {charge residuals} →
  SelectedVariationResidualBounds charge residuals →
  residualTotal residuals ≤ totalResidualCoefficient * charge
selectedVariationSpilloverUpper {charge} {residuals} bounds =
  subst
    (λ coefficient →
      residualTotal residuals ≤ coefficient * charge)
    residualCoefficientLedgerExact
    (fourResidualBoundsSum bounds)

data ResidualOwner : Set where
  gaugeOwner constraintOwner transportOwner boundaryOwner : ResidualOwner

data ExtractionResidualAtom : Set where
  gaugeRepairAtom constraintRepairAtom
    covariantTransportAtom localityBoundaryAtom : ExtractionResidualAtom

ownerOf : ExtractionResidualAtom → ResidualOwner
ownerOf gaugeRepairAtom = gaugeOwner
ownerOf constraintRepairAtom = constraintOwner
ownerOf covariantTransportAtom = transportOwner
ownerOf localityBoundaryAtom = boundaryOwner

gaugeAtomOwnedExactly : ownerOf gaugeRepairAtom ≡ gaugeOwner
gaugeAtomOwnedExactly = refl

constraintAtomOwnedExactly :
  ownerOf constraintRepairAtom ≡ constraintOwner
constraintAtomOwnedExactly = refl

transportAtomOwnedExactly :
  ownerOf covariantTransportAtom ≡ transportOwner
transportAtomOwnedExactly = refl

boundaryAtomOwnedExactly :
  ownerOf localityBoundaryAtom ≡ boundaryOwner
boundaryAtomOwnedExactly = refl
