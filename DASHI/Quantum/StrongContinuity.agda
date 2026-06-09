module DASHI.Quantum.StrongContinuity where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

open import DASHI.Unifier using (WaveLift)
open import DASHI.Quantum.GNSUniversalProperty using
  (GNSUniversalPropertyWitness; canonicalGNSUniversalPropertyWitness)
open import DASHI.Quantum.SelfAdjointColimitGenerator using
  (SelfAdjointColimitGeneratorWitness;
   canonicalSelfAdjointColimitGeneratorWitness)
open import DASHI.Quantum.Stone using
  (StoneBundle; StoneConsequences; StoneContinuity; Stone-theorem;
   onePointFiniteDistance; onePointFiniteHilbertSpace; onePointFiniteLift;
   onePointFiniteStoneBundle; onePointFiniteStrongContinuity;
   onePointFiniteTower)

-- Strong continuity on the GNS completion is the inherited Stone continuity
-- of the concrete one-point finite bundle.

record StrongContinuityWitness : Setω where
  field
    gnsUniversalProperty :
      GNSUniversalPropertyWitness

    selfAdjointColimitGenerator :
      SelfAdjointColimitGeneratorWitness

    stoneBundle :
      StoneBundle onePointFiniteTower onePointFiniteHilbertSpace

    stoneBundleIsCanonical :
      stoneBundle ≡ onePointFiniteStoneBundle

    strongContinuity :
      StoneContinuity (WaveLift.U onePointFiniteLift) onePointFiniteDistance

    strongContinuityIsCanonical :
      strongContinuity ≡ onePointFiniteStrongContinuity

    stoneConsequences :
      StoneConsequences stoneBundle

    witnessBoundary :
      List String

open StrongContinuityWitness public

canonicalStrongContinuityWitness : StrongContinuityWitness
canonicalStrongContinuityWitness =
  record
    { gnsUniversalProperty = canonicalGNSUniversalPropertyWitness
    ; selfAdjointColimitGenerator =
        canonicalSelfAdjointColimitGeneratorWitness
    ; stoneBundle = onePointFiniteStoneBundle
    ; stoneBundleIsCanonical = refl
    ; strongContinuity = onePointFiniteStrongContinuity
    ; strongContinuityIsCanonical = refl
    ; stoneConsequences = Stone-theorem onePointFiniteStoneBundle
    ; witnessBoundary =
        "StrongContinuity packages the concrete one-point Stone continuity witness"
        ∷ "The continuity law is the inherited onePointFiniteStrongContinuity theorem"
        ∷ "The Stone bundle and its consequences are threaded through unchanged"
        ∷ []
    }

strongContinuityBoundary : List String
strongContinuityBoundary =
  "StrongContinuity is the concrete Stone one-point continuity witness"
  ∷ "No new continuity postulates are introduced"
  ∷ []
