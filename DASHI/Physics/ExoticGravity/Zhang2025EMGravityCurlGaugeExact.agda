{-# OPTIONS --safe #-}
module DASHI.Physics.ExoticGravity.Zhang2025EMGravityCurlGaugeExact where

open import Agda.Builtin.Equality using (_≡_; refl)

private
  variable
    A B : Set

transEq : {x y z : A} → x ≡ y → y ≡ z → x ≡ z
transEq refl yz = yz

congEq : (f : A → B) → {x y : A} → x ≡ y → f x ≡ f y
congEq f refl = refl

------------------------------------------------------------------------
-- Abstract linear curl/gradient complex; laws are explicit *inputs*.
-- This theorem is structural, not an analytic proof on a physical spacetime.
------------------------------------------------------------------------

record CurlGradientComplex : Set₁ where
  field
    Field Potential CurlValue : Set
    addField : Field → Field → Field
    grad : Potential → Field
    curl : Field → CurlValue
    zeroCurl : CurlValue
    addCurl : CurlValue → CurlValue → CurlValue
    curlAddHom :
      (x y : Field) →
      curl (addField x y) ≡ addCurl (curl x) (curl y)
    curlGradZero :
      (p : Potential) → curl (grad p) ≡ zeroCurl
    curlRightNeutral :
      (v : CurlValue) → addCurl v zeroCurl ≡ v

open CurlGradientComplex public

curlInvisibleGradient :
  (complex : CurlGradientComplex) →
  (x : Field complex) →
  (p : Potential complex) →
  curl complex (addField complex x (grad complex p))
    ≡ curl complex x
curlInvisibleGradient c x p =
  transEq
    (curlAddHom c x (grad c p))
    (transEq
      (congEq (addCurl c (curl c x)) (curlGradZero c p))
      (curlRightNeutral c (curl c x)))

------------------------------------------------------------------------
-- The proposed curl relationship cannot by itself select G uniquely.
-- The gradient shift remains a candidate with the very same measured curl.
------------------------------------------------------------------------

record MatchedProposedCurl
  (c : CurlGradientComplex) : Set where
  field
    proposedGravity : Field c
    scaledElectric : Field c
    selectedPotential : Potential c
    curlsAgree :
      curl c proposedGravity ≡ curl c scaledElectric

open MatchedProposedCurl public

gaugeShiftPreservesProposedCurl :
  (c : CurlGradientComplex) →
  (statement : MatchedProposedCurl c) →
  curl c
    (addField c
      (proposedGravity statement)
      (grad c (selectedPotential statement)))
    ≡ curl c (scaledElectric statement)
gaugeShiftPreservesProposedCurl c statement =
  transEq
    (curlInvisibleGradient c
      (proposedGravity statement) (selectedPotential statement))
    (curlsAgree statement)

------------------------------------------------------------------------
-- Concrete finite countermodel: the two candidate fields can be different
-- even when their observed curl readings are identical.
-- This is a source-law nonidentifiability witness, not a gravity observation.
------------------------------------------------------------------------

data TwoFields : Set where
  baseField nontrivialGradientField : TwoFields

data OneCurl : Set where
  zeroCurlFixture : OneCurl

data PotentialBit : Set where
  constantPotential nonconstantPotential : PotentialBit

fixtureCurl : TwoFields → OneCurl
fixtureCurl baseField = zeroCurlFixture
fixtureCurl nontrivialGradientField = zeroCurlFixture

fixtureGrad : PotentialBit → TwoFields
fixtureGrad constantPotential = baseField
fixtureGrad nonconstantPotential = nontrivialGradientField

fixtureSameCurl :
  fixtureCurl baseField ≡ fixtureCurl nontrivialGradientField
fixtureSameCurl = refl

data Contradiction : Set where

fixtureFieldsAreNotEqual :
  baseField ≡ nontrivialGradientField → Contradiction
fixtureFieldsAreNotEqual ()

------------------------------------------------------------------------
-- Closed finite additive Z₂ field fixture. A nonzero gradient changes a
-- selected field while the curl readout is unchanged.
------------------------------------------------------------------------

fixtureAddField : TwoFields → TwoFields → TwoFields
fixtureAddField baseField y = y
fixtureAddField nontrivialGradientField baseField =
  nontrivialGradientField
fixtureAddField nontrivialGradientField nontrivialGradientField =
  baseField

fixtureAddCurl : OneCurl → OneCurl → OneCurl
fixtureAddCurl _ _ = zeroCurlFixture

fixtureComplex : CurlGradientComplex
fixtureComplex = record
  { Field = TwoFields
  ; Potential = PotentialBit
  ; CurlValue = OneCurl
  ; addField = fixtureAddField
  ; grad = fixtureGrad
  ; curl = fixtureCurl
  ; zeroCurl = zeroCurlFixture
  ; addCurl = fixtureAddCurl
  ; curlAddHom = λ x y → refl
  ; curlGradZero = λ p → refl
  ; curlRightNeutral = λ v → refl
  }

fixtureGradientIsNontrivial :
  fixtureAddField baseField (fixtureGrad nonconstantPotential)
    ≡ nontrivialGradientField
fixtureGradientIsNontrivial = refl

fixtureNontrivialShiftHasSameCurl :
  curl fixtureComplex
    (addField fixtureComplex baseField
      (grad fixtureComplex nonconstantPotential))
  ≡ curl fixtureComplex baseField
fixtureNontrivialShiftHasSameCurl =
  curlInvisibleGradient fixtureComplex baseField nonconstantPotential
