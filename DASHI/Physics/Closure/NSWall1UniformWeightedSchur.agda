module DASHI.Physics.Closure.NSWall1UniformWeightedSchur where

open import Agda.Primitive using (Level; _⊔_; lsuc)

open import DASHI.Analysis.FiniteWeightedKernelSums
open import DASHI.Physics.Closure.NSPairIncidenceKernel
open import DASHI.Physics.Closure.NSWall1FourierShellInstance

------------------------------------------------------------------------
-- Scale-uniform weighted row/column control for the active Wall-1 family.
------------------------------------------------------------------------

record Wall1ScaleFamily
    {j v s : Level}
    (Scale : Set j)
    (Vector : Set v)
    (Scalar : Set s) : Set (lsuc (j ⊔ v ⊔ s)) where
  field
    atScale : Scale → Wall1FourierShellData Vector Scalar

open Wall1ScaleFamily public

record UniformWall1WeightedSchur
    {j v s : Level}
    {Scale : Set j}
    {Vector : Set v}
    {Scalar : Set s}
    (family : Wall1ScaleFamily Scale Vector Scalar) :
    Set (lsuc (j ⊔ v ⊔ s)) where
  field
    rowConstant : Scalar
    columnConstant : Scalar

    uniformRowBound :
      ∀ scale row →
      let P = wall1PairIncidenceData (atScale family scale)
          K = asFiniteWeightedKernel P
      in
      _≤_ K
        (rowWeightedSum K row)
        (multiply K rowConstant (rowWeight K row))

    uniformColumnBound :
      ∀ scale col →
      let P = wall1PairIncidenceData (atScale family scale)
          K = asFiniteWeightedKernel P
      in
      _≤_ K
        (columnWeightedSum K col)
        (multiply K columnConstant (colWeight K col))

open UniformWall1WeightedSchur public

uniformFiniteCertificate :
  ∀ {j v s}
    {Scale : Set j}
    {Vector : Set v}
    {Scalar : Set s}
    {family : Wall1ScaleFamily Scale Vector Scalar} →
  UniformWall1WeightedSchur family →
  ∀ scale →
  FiniteWeightedSchurCertificate
    (asFiniteWeightedKernel
      (wall1PairIncidenceData (atScale family scale)))
uniformFiniteCertificate U scale = record
  { rowConstant = rowConstant U
  ; columnConstant = columnConstant U
  ; rowBound = uniformRowBound U scale
  ; columnBound = uniformColumnBound U scale
  }

uniformPairIncidenceCertificate :
  ∀ {j v s}
    {Scale : Set j}
    {Vector : Set v}
    {Scalar : Set s}
    {family : Wall1ScaleFamily Scale Vector Scalar} →
  UniformWall1WeightedSchur family →
  ∀ scale →
  PairIncidenceWeightedCertificate
    (wall1PairIncidenceData (atScale family scale))
uniformPairIncidenceCertificate U scale = record
  { finiteCertificate = uniformFiniteCertificate U scale }

record Wall1BidirectionalUniformBounds
    {j v s : Level}
    (Scale : Set j)
    (Vector : Set v)
    (Scalar : Set s) : Set (lsuc (j ⊔ v ⊔ s)) where
  field
    k01Family : Wall1ScaleFamily Scale Vector Scalar
    k10Family : Wall1ScaleFamily Scale Vector Scalar

    k01Uniform : UniformWall1WeightedSchur k01Family
    k10Uniform : UniformWall1WeightedSchur k10Family

open Wall1BidirectionalUniformBounds public
