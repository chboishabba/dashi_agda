module DASHI.Quantum.Stone_Gates where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

open import DASHI.Quantum.GNSUniversalProperty using
  (GNSUniversalPropertyWitness; canonicalGNSUniversalPropertyWitness)
open import DASHI.Quantum.SelfAdjointGenerator using
  (SelfAdjointColimitGeneratorWitness;
   canonicalSelfAdjointColimitGeneratorWitness)
open import DASHI.Quantum.StrongContinuity using
  (StrongContinuityWitness; canonicalStrongContinuityWitness)
open import DASHI.Quantum.Stone using
  (StoneBundle; StoneConsequences; Stone-theorem
  ; onePointFiniteHilbertSpace; onePointFiniteStoneBundle; onePointFiniteTower)

record StoneGatesWitnessBundle : Setω where
  field
    gnsUniversalPropertyWitness :
      GNSUniversalPropertyWitness

    selfAdjointColimitGeneratorWitness :
      SelfAdjointColimitGeneratorWitness

    strongContinuityWitness :
      StrongContinuityWitness

    stoneBundle :
      StoneBundle onePointFiniteTower onePointFiniteHilbertSpace

    stoneBundleIsCanonical :
      stoneBundle ≡ onePointFiniteStoneBundle

    stoneConsequences :
      StoneConsequences stoneBundle

    witnessBoundary :
      List String

open StoneGatesWitnessBundle public

canonicalStoneGatesWitnessBundle :
  StoneGatesWitnessBundle
canonicalStoneGatesWitnessBundle =
  record
    { gnsUniversalPropertyWitness =
        canonicalGNSUniversalPropertyWitness
    ; selfAdjointColimitGeneratorWitness =
        canonicalSelfAdjointColimitGeneratorWitness
    ; strongContinuityWitness =
        canonicalStrongContinuityWitness
    ; stoneBundle =
        onePointFiniteStoneBundle
    ; stoneBundleIsCanonical =
        refl
    ; stoneConsequences =
        Stone-theorem onePointFiniteStoneBundle
    ; witnessBoundary =
        "Stone_Gates packages the canonical GNS, self-adjoint generator, and strong-continuity witnesses"
        ∷ "The package is downstream of Stone and does not introduce an import cycle"
        ∷ "Stone.agda keeps its own local finite Stone core while exposing the GNS witness alias"
        ∷ []
    }

