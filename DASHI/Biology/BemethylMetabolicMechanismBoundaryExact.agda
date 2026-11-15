module DASHI.Biology.BemethylMetabolicMechanismBoundaryExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Biology.BemethylActoprotectorClaimAtlasExact as Claims

data MechanismRoute : Set where
  CoriCycleRoute : MechanismRoute
  MitochondrialEnzymeRoute : MechanismRoute
  AntioxidantEnzymeRoute : MechanismRoute
  ImmuneProteinRoute : MechanismRoute

record MechanismBoundary : Set where
  field
    atlas : Claims.BemethylClaimAtlas
    route : MechanismRoute
    routeReported : Bool
    proteinSynthesisDependenceReported : Bool
    molecularTargetIdentified : Bool
    routeEstablishesWholeOrganismEfficacy : Bool
    reading : String

open MechanismBoundary public

coriBoundary : MechanismBoundary
coriBoundary = record
  { atlas = Claims.canonicalBemethylClaimAtlas
  ; route = CoriCycleRoute
  ; routeReported = true
  ; proteinSynthesisDependenceReported = true
  ; molecularTargetIdentified = false
  ; routeEstablishesWholeOrganismEfficacy = false
  ; reading = "Reported gluconeogenesis/lactate-utilisation route; mechanism target and human causal sufficiency remain open"
  }

mitochondrialBoundary : MechanismBoundary
mitochondrialBoundary = record
  { atlas = Claims.canonicalBemethylClaimAtlas
  ; route = MitochondrialEnzymeRoute
  ; routeReported = true
  ; proteinSynthesisDependenceReported = true
  ; molecularTargetIdentified = false
  ; routeEstablishesWholeOrganismEfficacy = false
  ; reading = "Reported mitochondrial-enzyme/protein-synthesis route; not a solved target mechanism"
  }

antioxidantBoundary : MechanismBoundary
antioxidantBoundary = record
  { atlas = Claims.canonicalBemethylClaimAtlas
  ; route = AntioxidantEnzymeRoute
  ; routeReported = true
  ; proteinSynthesisDependenceReported = true
  ; molecularTargetIdentified = false
  ; routeEstablishesWholeOrganismEfficacy = false
  ; reading = "Reported induction of endogenous antioxidant enzymes rather than direct radical scavenging"
  }

proteinSynthesisDependenceDoesNotIdentifyTarget :
  molecularTargetIdentified mitochondrialBoundary ≡ false
proteinSynthesisDependenceDoesNotIdentifyTarget = refl

routeDoesNotEstablishWholeOrganismEfficacy :
  routeEstablishesWholeOrganismEfficacy coriBoundary ≡ false
routeDoesNotEstablishWholeOrganismEfficacy = refl
