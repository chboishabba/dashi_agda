module DASHI.Foundations.Moonshine196883Boundary where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_; _*_)
open import Agda.Builtin.String using (String)

moonshineLargeFactor : Nat
moonshineLargeFactor = 196883

moonshineLargeFactor-factorisation : 47 * (59 * 71) ≡ moonshineLargeFactor
moonshineLargeFactor-factorisation = refl

moonshinePlusIdentity : Nat
moonshinePlusIdentity = moonshineLargeFactor + 1

moonshinePlusIdentity-value : moonshinePlusIdentity ≡ 196884
moonshinePlusIdentity-value = refl

record FactorTriple : Set where
  constructor factorTriple
  field
    firstFactor : Nat
    secondFactor : Nat
    thirdFactor : Nat
    product : Nat
    productChecks : firstFactor * (secondFactor * thirdFactor) ≡ product

canonical475971FactorTriple : FactorTriple
canonical475971FactorTriple = factorTriple 47 59 71 196883 refl

record PlusOneSplit : Set where
  constructor plusOneSplit
  field
    identityPart : Nat
    residualPart : Nat
    assembledPart : Nat
    assembledChecks : identityPart + residualPart ≡ assembledPart

canonical196884Split : PlusOneSplit
canonical196884Split = plusOneSplit 1 196883 196884 refl

record Moonshine196883Boundary : Set where
  constructor moonshine196883Boundary
  field
    exactFactorisationChecked : Bool
    exactPlusOneSplitChecked : Bool
    typo19883AcceptedAsEquivalent : Bool
    typo19883AcceptedAsEquivalentIsFalse : typo19883AcceptedAsEquivalent ≡ false
    monsterRepresentationAuthorityPromoted : Bool
    monsterRepresentationAuthorityPromotedIsFalse : monsterRepresentationAuthorityPromoted ≡ false
    modularJAuthorityPromoted : Bool
    modularJAuthorityPromotedIsFalse : modularJAuthorityPromoted ≡ false
    interpretation : String

canonicalMoonshine196883Boundary : Moonshine196883Boundary
canonicalMoonshine196883Boundary =
  moonshine196883Boundary true true false refl false refl false refl
    "196883 = 47*59*71 and 196884 = 1+196883 are checked finite arithmetic; the identity/residual split does not by itself prove moonshine or modular-j claims"
