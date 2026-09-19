{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanSelectedWilsonBasisInsertionNormExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; 1ℚ; _+_; _*_; _≤_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier using (pair)
import DASHI.Physics.YangMills.BalabanP33PhysicalCoordinateBasisExact as Basis
import DASHI.Physics.YangMills.BalabanP33PhysicalSU2FiniteCoordinatesExact as Physical
import DASHI.Physics.YangMills.BalabanP33LiteralResidualKernelNumericalCalibrationExact as Calibration
import DASHI.Physics.YangMills.BalabanP33PhysicalRationalWilsonPlaquetteJetExact as Plaquette
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionWilsonSecondVariationExact as Wilson

basisCoordinateFactorExact :
  ∀ targetCoord targetCell coordinate cell →
  Basis.physicalBasis (pair targetCoord targetCell) (pair coordinate cell)
  ≡
  Basis.kronecker Calibration.lieCoordinateDecidableEquality coordinate targetCoord
  * Basis.kronecker Calibration.bondCellDecidableEquality cell targetCell
basisCoordinateFactorExact targetCoord targetCell coordinate cell =
  trans
    (Basis.identityEntryIsKronecker
      (pair coordinate cell) (pair targetCoord targetCell))
    (Basis.productKroneckerFactorExact
      Calibration.lieCoordinateDecidableEquality
      Calibration.bondCellDecidableEquality
      coordinate targetCoord cell targetCell)

basisInsertionNormSqExact :
  ∀ targetCoord targetCell axis site →
  Wilson.vectorNormSq
    (Plaquette.insertionAt
      (Physical.decodePhysicalSU2
        (Basis.physicalBasis (pair targetCoord targetCell)))
      axis site)
  ≡
  Basis.kronecker Calibration.bondCellDecidableEquality
    (pair axis site) targetCell
basisInsertionNormSqExact targetCoord targetCell axis site
  with Calibration.bondCellDecidableEquality (pair axis site) targetCell
... | no cellNeq
  rewrite basisCoordinateFactorExact targetCoord targetCell
      Physical.coordinateX (pair axis site)
        | basisCoordinateFactorExact targetCoord targetCell
      Physical.coordinateY (pair axis site)
        | basisCoordinateFactorExact targetCoord targetCell
      Physical.coordinateZ (pair axis site) =
  ℚRing.solve []
... | yes cellEq
  rewrite cellEq
        | basisCoordinateFactorExact targetCoord targetCell
      Physical.coordinateX targetCell
        | basisCoordinateFactorExact targetCoord targetCell
      Physical.coordinateY targetCell
        | basisCoordinateFactorExact targetCoord targetCell
      Physical.coordinateZ targetCell
  with targetCoord
... | Physical.coordinateX = ℚRing.solve []
... | Physical.coordinateY = ℚRing.solve []
... | Physical.coordinateZ = ℚRing.solve []

basisInsertionNormSqBelowOne :
  ∀ target axis site →
  Wilson.vectorNormSq
    (Plaquette.insertionAt
      (Physical.decodePhysicalSU2 (Basis.physicalBasis target))
      axis site)
  ≤ 1ℚ
basisInsertionNormSqBelowOne
    (pair targetCoord targetCell) axis site =
  subst
    (λ value → value ≤ 1ℚ)
    (sym (basisInsertionNormSqExact targetCoord targetCell axis site))
    (let
      k = Basis.kronecker Calibration.bondCellDecidableEquality
        (pair axis site) targetCell
     in
     caseBound k)
  where
  caseBound :
    ∀ cellSelector →
    cellSelector ≡
      Basis.kronecker Calibration.bondCellDecidableEquality
        (pair axis site) targetCell →
    cellSelector ≤ 1ℚ
  caseBound cellSelector selectorEq
    with Calibration.bondCellDecidableEquality (pair axis site) targetCell
  ... | yes _ =
    subst (λ value → value ≤ 1ℚ) (sym selectorEq) ℚP.≤-refl
  ... | no _ =
    subst (λ value → value ≤ 1ℚ) (sym selectorEq)
      (ℚP.nonNegative⁻¹ 1ℚ)

selectedWilsonBasisInsertionNormLevel : ProofLevel
selectedWilsonBasisInsertionNormLevel = machineChecked
