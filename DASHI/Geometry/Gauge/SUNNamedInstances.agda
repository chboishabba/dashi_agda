module DASHI.Geometry.Gauge.SUNNamedInstances where

open import Agda.Builtin.Bool using (false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Nat.Base using (_+_; _*_)

open import DASHI.Geometry.Gauge.SUNPrimitives
open import DASHI.Geometry.Gauge.SUNLane
open import DASHI.Geometry.Gauge.M6BitensorRepresentation
open import DASHI.Geometry.Gauge.M6SU3Fundamental


data SUNNamedInstanceObligation : Set where
  su1RepresentationMatterPending : SUNNamedInstanceObligation
  su2CurvatureProofPending       : SUNNamedInstanceObligation
  su3CurvatureProofPending       : SUNNamedInstanceObligation

su1TrivialLane : SUNLane 1
su1TrivialLane = canonicalSUNLane 1

su2SpinWeakLane : SUNLane 2
su2SpinWeakLane = canonicalSUNLane 2

su3ColourLane : SUNLane 3
su3ColourLane = canonicalSUNLane 3

-- The first named relational witness is the SU(3) mirror bitensor
-- 3 ⊗ 3* = 1 ⊕ 8. It records the invariant closed shell separately from the
-- traceless adjoint residue and does not claim Yang-Mills promotion.
su3M6MirrorBitensor : SU3MirrorM6Decomposition
su3M6MirrorBitensor = canonicalSU3MirrorM6

su3M6MirrorDimensionCloses : 3 * 3 ≡ 1 + 8
su3M6MirrorDimensionCloses = mirrorM6DimensionCloses

clayYangMillsPromotedIsFalseForNamedInstances : clayYangMillsPromoted ≡ false
clayYangMillsPromotedIsFalseForNamedInstances = refl
