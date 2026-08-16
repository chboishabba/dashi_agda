module DASHI.Biology.Physical.MorphogeneticControlFieldCapacityExact where

------------------------------------------------------------------------
-- Finite exact control-field information surface.
--
-- Three independent binary high-level constraints have eight possible target
-- patterns.  An exact three-bit control word is therefore sufficient and uses
-- every codeword.  This is a finite capacity regression, not a Shannon-channel
-- capacity theorem for biological tissue.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

record TargetConstraint3 : Set where
  constructor targetConstraint3
  field
    attachment : Bool
    differentiation : Bool
    junction : Bool

open TargetConstraint3 public

record ControlWord3 : Set where
  constructor controlWord3
  field
    high middle low : Bool

open ControlWord3 public

encodeTarget : TargetConstraint3 → ControlWord3
encodeTarget (targetConstraint3 a d j) = controlWord3 a d j

decodeTarget : ControlWord3 → TargetConstraint3
decodeTarget (controlWord3 a d j) = targetConstraint3 a d j

encodeDecodeExact :
  (word : ControlWord3) → encodeTarget (decodeTarget word) ≡ word
encodeDecodeExact (controlWord3 a d j) = refl

decodeEncodeExact :
  (target : TargetConstraint3) → decodeTarget (encodeTarget target) ≡ target
decodeEncodeExact (targetConstraint3 a d j) = refl

------------------------------------------------------------------------
-- Explicit eight-element target carrier.
------------------------------------------------------------------------

data Target8 : Set where
  t000 t001 t010 t011 t100 t101 t110 t111 : Target8

target8ToConstraint : Target8 → TargetConstraint3
target8ToConstraint t000 = targetConstraint3 false false false
target8ToConstraint t001 = targetConstraint3 false false true
target8ToConstraint t010 = targetConstraint3 false true false
target8ToConstraint t011 = targetConstraint3 false true true
target8ToConstraint t100 = targetConstraint3 true false false
target8ToConstraint t101 = targetConstraint3 true false true
target8ToConstraint t110 = targetConstraint3 true true false
target8ToConstraint t111 = targetConstraint3 true true true

constraintToTarget8 : TargetConstraint3 → Target8
constraintToTarget8 (targetConstraint3 false false false) = t000
constraintToTarget8 (targetConstraint3 false false true) = t001
constraintToTarget8 (targetConstraint3 false true false) = t010
constraintToTarget8 (targetConstraint3 false true true) = t011
constraintToTarget8 (targetConstraint3 true false false) = t100
constraintToTarget8 (targetConstraint3 true false true) = t101
constraintToTarget8 (targetConstraint3 true true false) = t110
constraintToTarget8 (targetConstraint3 true true true) = t111

constraintTargetRoundTrip :
  (target : TargetConstraint3) →
  target8ToConstraint (constraintToTarget8 target) ≡ target
constraintTargetRoundTrip (targetConstraint3 false false false) = refl
constraintTargetRoundTrip (targetConstraint3 false false true) = refl
constraintTargetRoundTrip (targetConstraint3 false true false) = refl
constraintTargetRoundTrip (targetConstraint3 false true true) = refl
constraintTargetRoundTrip (targetConstraint3 true false false) = refl
constraintTargetRoundTrip (targetConstraint3 true false true) = refl
constraintTargetRoundTrip (targetConstraint3 true true false) = refl
constraintTargetRoundTrip (targetConstraint3 true true true) = refl

targetConstraintRoundTrip :
  (target : Target8) →
  constraintToTarget8 (target8ToConstraint target) ≡ target
targetConstraintRoundTrip t000 = refl
targetConstraintRoundTrip t001 = refl
targetConstraintRoundTrip t010 = refl
targetConstraintRoundTrip t011 = refl
targetConstraintRoundTrip t100 = refl
targetConstraintRoundTrip t101 = refl
targetConstraintRoundTrip t110 = refl
targetConstraintRoundTrip t111 = refl

------------------------------------------------------------------------
-- Projection cost: forgetting any one target bit merges distinct goals.
------------------------------------------------------------------------

projectAttachmentDifferentiation : TargetConstraint3 → Bool × Bool
projectAttachmentDifferentiation target = attachment target , differentiation target

sameTwoBitProjectionDifferentJunction :
  projectAttachmentDifferentiation (targetConstraint3 true true false)
  ≡ projectAttachmentDifferentiation (targetConstraint3 true true true)
sameTwoBitProjectionDifferentJunction = refl

junctionResidualRestoresExactTarget :
  (target : TargetConstraint3) →
  let coarse = projectAttachmentDifferentiation target
  in targetConstraint3 (proj₁ coarse) (proj₂ coarse) (junction target) ≡ target
junctionResidualRestoresExactTarget (targetConstraint3 a d j) = refl

-- This is the same fibre-local information principle used elsewhere in PNF:
-- a coarse high-level target may need a residual bit when downstream control
-- distinguishes goals inside one coarse fibre.
