{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119CosmologyP2RenormalizedHilbertWardAuthorityTest where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Bool using (true; false)

import DASHI.Physics.Foundations.CMP119CosmologyP2RenormalizedHilbertWardAuthorityExact as P2

matchingRegression :
  P2.localCShortDistanceMatchingIsTheApplicabilityWitness ≡ true
matchingRegression = refl

sourceSpecificRegression :
  P2.noCMP119SpecificTraceScalarWeldRequired ≡ true
sourceSpecificRegression = refl

authorityInstantiationIsCompilerOnly :
  P2.authorityRecordInstantiationAddsNoMathematics ≡ true
authorityInstantiationIsCompilerOnly = refl

noSecondInstantiationLeaf :
  P2.remainingR2WorkIsInstantiationOfStandardWardAuthority ≡ false
noSecondInstantiationLeaf = refl

operatorIdentityIsTheRemainingTheorem :
  P2.remainingR2WorkIsExactRenormalizedOperatorIdentity ≡ true
operatorIdentityIsTheRemainingTheorem = refl
