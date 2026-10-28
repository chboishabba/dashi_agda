module DASHI.Arithmetic.PrimegameSSP15CarrierFactorisationExact where

------------------------------------------------------------------------
-- SOURCE AND ATTRIBUTION
--
-- John H. Conway, FRACTRAN: A Simple Universal Programming Language
-- for Arithmetic, 1987; Richard K. Guy, Conway's Prime Producing
-- Machine, Mathematics Magazine 56(1), 1983, 26–33.
-- OEIS A202138, A007546: the Guy 15/14,15/2 ordered variant contains
-- FOURTEEN FRACTIONS; Conway's 15/2,1/7 variant has FOURTEEN too.
--
-- Original in-repo carrier owner:
-- DASHI.Biology.SignedSSPFRACTRANWeaveExact.SSPPrime
-- has FIFTEEN typed SSP/Ogg prime lanes. The ten distinct prime
-- factors appearing in all fourteen Guy FRACTRAN fractions are
-- already members of that source-owned SSP15 carrier vocabulary.
--
-- NEW: every numerator and denominator is an explicit product of
-- existing typed lanes. The precise ordered numeric fraction list is
-- definitionally equal to the historical 14-rule Guy programme.
-- This is a finite factorisation proof, NOT a universal interpreter,
-- a signed compiler simulation or a prime-generation kernel theorem.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; _*_; suc)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Product using (_×_; _,_)

import DASHI.Biology.SignedSSPFRACTRANWeaveExact as Signed

-- A FRACTRAN factor belongs to the existing SSPPrime typed atlas.
-- It is not a new, untyped numerical prime or arbitrary Ogg label.
multiplyCarrierFactors : List Signed.SSPPrime → Nat
multiplyCarrierFactors [] = 1
multiplyCarrierFactors (p ∷ rest) =
  Signed.primeValue p * multiplyCarrierFactors rest

record TypedFraction : Set where
  constructor typedFraction
  field
    numeratorCarriers denominatorCarriers : List Signed.SSPPrime

open TypedFraction public

fractionNumbers : TypedFraction → Nat × Nat
fractionNumbers (typedFraction num den) =
  multiplyCarrierFactors num , multiplyCarrierFactors den

mapFractionNumbers : List TypedFraction → List (Nat × Nat)
mapFractionNumbers [] = []
mapFractionNumbers (f ∷ rest) =
  fractionNumbers f ∷ mapFractionNumbers rest

-- This is the Guy variant, not Conway's alternate 1/7 list.
-- Every number is factored through original SSP15 *constructors*.
guyFourteenTyped : List TypedFraction
guyFourteenTyped =
  typedFraction (Signed.ssp17 ∷ []) (Signed.ssp7 ∷ Signed.ssp13 ∷ [])
  ∷ typedFraction
      (Signed.ssp2 ∷ Signed.ssp3 ∷ Signed.ssp13 ∷ [])
      (Signed.ssp5 ∷ Signed.ssp17 ∷ [])
  ∷ typedFraction
      (Signed.ssp19 ∷ [])
      (Signed.ssp3 ∷ Signed.ssp17 ∷ [])
  ∷ typedFraction
      (Signed.ssp23 ∷ [])
      (Signed.ssp2 ∷ Signed.ssp19 ∷ [])
  ∷ typedFraction
      (Signed.ssp29 ∷ [])
      (Signed.ssp3 ∷ Signed.ssp11 ∷ [])
  ∷ typedFraction
      (Signed.ssp7 ∷ Signed.ssp11 ∷ [])
      (Signed.ssp29 ∷ [])
  ∷ typedFraction
      (Signed.ssp5 ∷ Signed.ssp19 ∷ [])
      (Signed.ssp23 ∷ [])
  ∷ typedFraction
      (Signed.ssp7 ∷ Signed.ssp11 ∷ [])
      (Signed.ssp19 ∷ [])
  ∷ typedFraction
      []
      (Signed.ssp17 ∷ [])
  ∷ typedFraction
      (Signed.ssp11 ∷ [])
      (Signed.ssp13 ∷ [])
  ∷ typedFraction
      (Signed.ssp13 ∷ [])
      (Signed.ssp11 ∷ [])
  ∷ typedFraction
      (Signed.ssp3 ∷ Signed.ssp5 ∷ [])
      (Signed.ssp2 ∷ Signed.ssp7 ∷ [])
  ∷ typedFraction
      (Signed.ssp3 ∷ Signed.ssp5 ∷ [])
      (Signed.ssp2 ∷ [])
  ∷ typedFraction
      (Signed.ssp5 ∷ Signed.ssp11 ∷ [])
      []
  ∷ []

guyFourteenNumeric : List (Nat × Nat)
guyFourteenNumeric =
  (17 , 91) ∷ (78 , 85) ∷ (19 , 51) ∷ (23 , 38)
  ∷ (29 , 33) ∷ (77 , 29) ∷ (95 , 23) ∷ (77 , 19)
  ∷ (1 , 17) ∷ (11 , 13) ∷ (13 , 11) ∷ (15 , 14)
  ∷ (15 , 2) ∷ (55 , 1) ∷ []

typedFractionsAreExactGuyFourteen :
  mapFractionNumbers guyFourteenTyped ≡ guyFourteenNumeric
typedFractionsAreExactGuyFourteen = refl

guyProgrammeRuleCountIsFourteen :
  Signed.listCount guyFourteenTyped ≡ 14
guyProgrammeRuleCountIsFourteen = refl

-- The exact carrier support of all fourteen rules.
primegameSupportInsideSSP15 : List Signed.SSPPrime
primegameSupportInsideSSP15 =
  Signed.ssp2 ∷ Signed.ssp3 ∷ Signed.ssp5 ∷ Signed.ssp7
  ∷ Signed.ssp11 ∷ Signed.ssp13 ∷ Signed.ssp17
  ∷ Signed.ssp19 ∷ Signed.ssp23 ∷ Signed.ssp29 ∷ []

primegameUsesTenTypedCarriers :
  Signed.listCount primegameSupportInsideSSP15 ≡ 10
primegameUsesTenTypedCarriers = refl

originalSSPAtlasHasFifteenTypedCarriers :
  Signed.listCount Signed.canonicalSSPPrimes ≡ 15
originalSSPAtlasHasFifteenTypedCarriers =
  Signed.canonicalSSPPrimeCountIsFifteen

-- Historical rule count ≠ the Ogg-carrier atlas cardinality.
historicalProgrammeCountIsNotSSPCount :
  Signed.listCount guyFourteenTyped ≡ 14
  × Signed.listCount Signed.canonicalSSPPrimes ≡ 15
historicalProgrammeCountIsNotSSPCount =
  guyProgrammeRuleCountIsFourteen ,
  originalSSPAtlasHasFifteenTypedCarriers
