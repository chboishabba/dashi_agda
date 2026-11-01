module DASHI.Geometry.ConeArrowOrientationAsymmetry where

open import Agda.Builtin.Nat using (Nat)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import DASHI.Physics.OrbitSignatureDiscriminant as OSD

record IntrinsicOrientation : Set where
  field
    orientationTag : Nat
    orientationTag≡sig31 : orientationTag ≡ OSD.OrientationTag OSD.sig31

open IntrinsicOrientation public
