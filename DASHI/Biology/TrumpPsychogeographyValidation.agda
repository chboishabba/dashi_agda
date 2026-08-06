module DASHI.Biology.TrumpPsychogeographyValidation where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Unit using (⊤; tt)

import DASHI.Biology.ConsciousAccessRound10PsychogeographyValidation
import DASHI.Biology.TrumpPsychogeographyEverything

trumpPsychogeographyRoot : Set
trumpPsychogeographyRoot = ⊤

trumpPsychogeographyRootInhabited : trumpPsychogeographyRoot
trumpPsychogeographyRootInhabited = tt

trumpPsychogeographyRootStable : trumpPsychogeographyRoot ≡ ⊤
trumpPsychogeographyRootStable = refl
