module DASHI.Physics.YangMills.BalabanDashenGrossConventionMap where

open import Agda.Builtin.Equality using (_≡_)

record DashenGrossConventionMap (Scalar : Set) : Set₁ where
  field
    balabanCoupling dashenGrossCoupling : Scalar
    generatorNormalization latticeSpacingNormalization determinantMultiplicity : Scalar
    combine : Scalar → Scalar → Scalar
    conventionMap : Scalar → Scalar
    calibrated :
      conventionMap balabanCoupling ≡ dashenGrossCoupling

open DashenGrossConventionMap public
