module DASHI.Physics.YangMills.BalabanFourDimensionalLDLTensorization where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.List.Base using (_++_)
open import Data.Rational using
  (ℚ; 0ℚ; _+_; _*_; _≤_; NonNegative; nonNegative)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanRationalLDLCertificate

------------------------------------------------------------------------
-- Four-axis tensorization consumer.
--
-- Every axis is represented by a finite family of mean-zero path coordinates.
-- The exact tensor-product carrier below sums all four families and obtains its
-- Poincare inequality solely by induction over the consumed LDL certificate.
-- A second adapter isolates the physical grid statement: the literal Wilson/RG
-- block must identify its variance and edge energy with these fibre folds.
------------------------------------------------------------------------

familyNormSq :
  ∀ {Coordinate} → RationalLDLCertificate Coordinate →
  List Coordinate → ℚ
familyNormSq certificate [] = 0ℚ
familyNormSq certificate (coordinate ∷ rest) =
  normSq certificate coordinate + familyNormSq certificate rest

familyEnergy :
  ∀ {Coordinate} → RationalLDLCertificate Coordinate →
  List Coordinate → ℚ
familyEnergy certificate [] = 0ℚ
familyEnergy certificate (coordinate ∷ rest) =
  energy certificate coordinate + familyEnergy certificate rest

scaleZero : ∀ coefficient → coefficient * 0ℚ ≡ 0ℚ
scaleZero = ℚRing.solve-∀

scalePlus : ∀ coefficient left right →
  coefficient * (left + right)
  ≡ coefficient * left + coefficient * right
scalePlus = ℚRing.solve-∀

familyLDLPoincare :
  ∀ {Coordinate}
    (certificate : RationalLDLCertificate Coordinate)
    (coordinates : List Coordinate) →
  coercivityConstant certificate * familyNormSq certificate coordinates
  ≤ familyEnergy certificate coordinates
familyLDLPoincare certificate []
  rewrite scaleZero (coercivityConstant certificate) = ℚP.≤-refl
familyLDLPoincare certificate (coordinate ∷ rest)
  rewrite scalePlus
    (coercivityConstant certificate)
    (normSq certificate coordinate)
    (familyNormSq certificate rest) =
  ℚP.+-mono-≤
    (ldlCertificatePoincare certificate coordinate)
    (familyLDLPoincare certificate rest)

record FourAxisTensorBlock (Coordinate : Set) : Set where
  constructor fourAxisTensorBlock
  field
    axis0 axis1 axis2 axis3 : List Coordinate

open FourAxisTensorBlock public

allTensorFibres :
  ∀ {Coordinate} → FourAxisTensorBlock Coordinate → List Coordinate
allTensorFibres block =
  axis0 block ++ axis1 block ++ axis2 block ++ axis3 block

tensorizedNormSq :
  ∀ {Coordinate} → RationalLDLCertificate Coordinate →
  FourAxisTensorBlock Coordinate → ℚ
tensorizedNormSq certificate block =
  familyNormSq certificate (allTensorFibres block)

tensorizedEdgeEnergy :
  ∀ {Coordinate} → RationalLDLCertificate Coordinate →
  FourAxisTensorBlock Coordinate → ℚ
tensorizedEdgeEnergy certificate block =
  familyEnergy certificate (allTensorFibres block)

fourAxisTensorBlockPoincare :
  ∀ {Coordinate}
    (certificate : RationalLDLCertificate Coordinate)
    (block : FourAxisTensorBlock Coordinate) →
  coercivityConstant certificate * tensorizedNormSq certificate block
  ≤ tensorizedEdgeEnergy certificate block
fourAxisTensorBlockPoincare certificate block =
  familyLDLPoincare certificate (allTensorFibres block)

record FourDimensionalTensorizationData
    (Block Coordinate : Set) : Set₁ where
  field
    pathCertificate : RationalLDLCertificate Coordinate
    pathCoercivityNonnegative :
      0ℚ ≤ coercivityConstant pathCertificate

    axis0Fibres axis1Fibres axis2Fibres axis3Fibres :
      Block → List Coordinate

    globalNormSq globalEdgeEnergy : Block → ℚ

    globalNormBelowFibres : ∀ block →
      globalNormSq block
      ≤ familyNormSq pathCertificate
          (axis0Fibres block
          ++ axis1Fibres block
          ++ axis2Fibres block
          ++ axis3Fibres block)

    fibreEnergyBelowGlobalEnergy : ∀ block →
      familyEnergy pathCertificate
          (axis0Fibres block
          ++ axis1Fibres block
          ++ axis2Fibres block
          ++ axis3Fibres block)
      ≤ globalEdgeEnergy block

open FourDimensionalTensorizationData public

allAxisFibres :
  ∀ {Block Coordinate} →
  FourDimensionalTensorizationData Block Coordinate → Block → List Coordinate
allAxisFibres dataSet block =
  axis0Fibres dataSet block
  ++ axis1Fibres dataSet block
  ++ axis2Fibres dataSet block
  ++ axis3Fibres dataSet block

fourDimensionalTensorizedPoincare :
  ∀ {Block Coordinate}
    (dataSet : FourDimensionalTensorizationData Block Coordinate)
    block →
  coercivityConstant (pathCertificate dataSet) * globalNormSq dataSet block
  ≤ globalEdgeEnergy dataSet block
fourDimensionalTensorizedPoincare dataSet block =
  let
    certificate = pathCertificate dataSet

    instance
      coefficientNonnegative :
        NonNegative (coercivityConstant certificate)
      coefficientNonnegative =
        nonNegative (pathCoercivityNonnegative dataSet)

    scaledNormComparison :
      coercivityConstant certificate * globalNormSq dataSet block
      ≤ coercivityConstant certificate
          * familyNormSq certificate (allAxisFibres dataSet block)
    scaledNormComparison =
      ℚP.*-monoˡ-≤-nonNeg (coercivityConstant certificate)
        (globalNormBelowFibres dataSet block)
  in
  ℚP.≤-trans
    scaledNormComparison
    (ℚP.≤-trans
      (familyLDLPoincare certificate (allAxisFibres dataSet block))
      (fibreEnergyBelowGlobalEnergy dataSet block))

fourAxisTensorProductCarrierLevel : ProofLevel
fourAxisTensorProductCarrierLevel = machineChecked

fourDimensionalLDLTensorizationLevel : ProofLevel
fourDimensionalLDLTensorizationLevel = machineChecked

physicalFourDimensionalFibreDecompositionLevel : ProofLevel
physicalFourDimensionalFibreDecompositionLevel = conditional
