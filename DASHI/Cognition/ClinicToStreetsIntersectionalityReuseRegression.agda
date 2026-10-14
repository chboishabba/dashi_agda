module DASHI.Cognition.ClinicToStreetsIntersectionalityReuseRegression where

open import DASHI.Core.Prelude
open import Data.Empty using (⊥)

import DASHI.Core.IntersectionalNonFactorability as NF
import DASHI.Core.RequiredObserverAxisJoinAdequacyExact as AxisJoin
import DASHI.Cognition.ClinicToStreetsIntersectionalityReuseExact as X

canonicalAtomisingWitness :
  NF.NonFactorabilityWitness X.atomisingProjection X.structuralAxis
canonicalAtomisingWitness = X.canonicalAtomisingIntersectionalWitness

atomisationCannotRecoverStructuralAxis :
  NF.FactorsThrough X.atomisingProjection X.structuralAxis → ⊥
atomisationCannotRecoverStructuralAxis = X.atomisingProjectionCannotRecoverStructuralAxis

repairedObserverRetainsStructuralAxis :
  AxisJoin.RetainsAxis X.repairedProjection X.structuralAxis
repairedObserverRetainsStructuralAxis = X.repairedProjectionRetainsStructuralAxis

intersectionalityOwnerReused : X.reusesIntersectionalNonFactorability ≡ true
intersectionalityOwnerReused = refl

axisJoinOwnerReused : X.reusesRequiredAxisJoin ≡ true
axisJoinOwnerReused = refl

singleAxisWorldComplete : X.singleAxisWorldComplete ≡ false
singleAxisWorldComplete = refl

finiteAxisListExhaustive : X.finiteAxisListExhaustive ≡ false
finiteAxisListExhaustive = refl

representationPaysMaterialDistribution : X.representationPaysMaterialDistribution ≡ false
representationPaysMaterialDistribution = refl
