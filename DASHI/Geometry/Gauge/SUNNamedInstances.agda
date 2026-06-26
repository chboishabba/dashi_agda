module DASHI.Geometry.Gauge.SUNNamedInstances where

open import Agda.Builtin.Bool using (false)
open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Geometry.Gauge.SUNPrimitives
open import DASHI.Geometry.Gauge.SUNLane

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

clayYangMillsPromotedIsFalseForNamedInstances : clayYangMillsPromoted ≡ false
clayYangMillsPromotedIsFalseForNamedInstances = refl
