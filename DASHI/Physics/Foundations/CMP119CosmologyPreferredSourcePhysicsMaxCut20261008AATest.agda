{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119CosmologyPreferredSourcePhysicsMaxCut20261008AATest where

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Foundations.CMP119CosmologyPreferredSourcePhysicsMaxCut20261008AAExact as AA

s3aIsOnePackage : AA.s3aOneSelectedPhysicalF2PackageRequired ≡ true
s3aIsOnePackage = refl

coefficientEnergyNotSeparateProject :
  AA.s3aCoefficientEnergyIndependentProjectRequired ≡ false
coefficientEnergyNotSeparateProject = refl

gaugeLocalNotSeparateProject :
  AA.s3aGaugeLocalIndependentProjectRequired ≡ false
gaugeLocalNotSeparateProject = refl

noRepresentationDebt : AA.representationOnlySameObjectDebtRemains ≡ false
noRepresentationDebt = refl
