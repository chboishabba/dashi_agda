{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119CosmologyPreferredSourcePhysicsMaxCut20261008AATest where

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Physics.Foundations.CMP119CosmologyPreferredSourcePhysicsMaxCut20261008AAExact as AA

s1InvariantCount : AA.s1UnprovenInvariantCount ≡ 4
s1InvariantCount = refl

s1NoInactiveScaleExtension : AA.s1InactiveScaleExtensionRequired ≡ false
s1NoInactiveScaleExtension = refl

s1NoPostHocBackgroundEquality : AA.s1PostHocBackgroundEqualityRequired ≡ false
s1NoPostHocBackgroundEquality = refl

s1NoTenTangentChoices : AA.s1IndependentTenTangentChoicesRequired ≡ false
s1NoTenTangentChoices = refl

s1ASTCompilerClosed : AA.s1ASTCompilesToExistingRound246Witness ≡ true
s1ASTCompilerClosed = refl

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
