module DASHI.Geometry.WetsuitSeamOptimisationRegression where

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Geometry.WetsuitSeamOptimisationBoundary

underarm-side-is-preferred-prior : preferredZone underarmSide ≡ true
underarm-side-is-preferred-prior = refl

inner-leg-is-preferred-prior : preferredZone innerLeg ≡ true
inner-leg-is-preferred-prior = refl

shoulder-apex-is-forbidden-prior : forbiddenZone shoulderApex ≡ true
shoulder-apex-is-forbidden-prior = refl

spine-centre-is-forbidden-prior : forbiddenZone spineCentre ≡ true
spine-centre-is-forbidden-prior = refl

spine-adjacent-is-not-forbidden-prior : forbiddenZone spineAdjacent ≡ false
spine-adjacent-is-not-forbidden-prior = refl

continuum-claim-remains-closed : continuumWetsuitOptimalityPromoted ≡ false
continuum-claim-remains-closed = refl

manufacturing-authority-remains-closed :
  automaticManufacturingAuthorityPromoted ≡ false
manufacturing-authority-remains-closed = refl
