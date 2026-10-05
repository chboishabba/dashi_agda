{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119CosmologyP3DistinctF2MarkedSourceSameCarrierTest where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Bool using (true; false)

import DASHI.Physics.Foundations.CMP119CosmologyP3DistinctF2MarkedSourceSameCarrierExact as F

sameCarrierDoesNotForceSameMarkedSourceRegression :
  F.sameCompositeCarrierDoesNotForceSameMarkedSource ≡ true
sameCarrierDoesNotForceSameMarkedSourceRegression = refl

r129StressSourceEqualityRetiredRegression :
  F.r129StressMarkedSourceEqualityNotRequiredForLocalCRechart ≡ true
r129StressSourceEqualityRetiredRegression = refl

remainingF2WorkRegression :
  F.remainingF2WorkIsConstructPhysicalMarkedF2Source ≡ true
remainingF2WorkRegression = refl

oldS3aEqualityIsNotPhysicsPremiseRegression :
  F.oldS3aStressSourceEqualityIsRequired ≡ false
oldS3aEqualityIsNotPhysicsPremiseRegression = refl
