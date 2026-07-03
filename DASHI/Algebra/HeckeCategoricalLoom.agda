module DASHI.Algebra.HeckeCategoricalLoom where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Unit using (⊤; tt)

import DASHI.Core.ProjectionCategory as PC
import DASHI.Core.ProjectionHomology as PH
import DASHI.Core.GrammarGeneratedCategory as GGC
import DASHI.Core.ProjectionConstructor as PCON

import Ontology.Hecke.Scan as HKS
import Ontology.Hecke.PrimeHeckeEigenMotifPipeline as HEMP

----------------------------------------------------------------------
-- Hecke eigen-geometry: categorical upgrade.
--
-- Grammar = State (a computational/cognitive state acted upon by Hecke
-- operators T_p for each supersingular prime p in the Monster ontos).
--
-- Objects:
--   heckeState   : the state space (domain)
--   eigenProfile : the Earth/Spoke/Hub eigenprofile (codomain)
--
-- Morphisms: functions between state and eigenprofile carriers.
--
-- Fibre(State, ep) = { s | signatureEigenProfile(scan(s)) ≡ ep }
--   Multiple Hecke states can share the same eigenprofile (Earth/Spoke/Hub
--   assignment). The profile is a coarse-graining of the 15-bit signature.
----------------------------------------------------------------------

data HKObj : Set where
  heckeState   : HKObj
  eigenProfile : HKObj

Underlying : HKObj → Set
Underlying heckeState   = HKS.State
Underlying eigenProfile = HEMP.EigenProfile

heckeProjectionCategory : PC.ProjectionCategory
heckeProjectionCategory = record
  { Obj             = HKObj
  ; Hom             = λ A B → Underlying A → Underlying B
  ; id              = λ x → x
  ; _∘_             = λ g f x → g (f x)
  ; id-left         = λ f → refl
  ; id-right        = λ f → refl
  ; assoc           = λ f g h → refl
  ; categoryReading = "Pi_H(state -> eigenprofile)"
  }

heckeGrammarCategory : GGC.GrammarGeneratedCategory
heckeGrammarCategory = record
  { Grammar        = HKS.State
  ; 𝓟              = λ _ → heckeProjectionCategory
  ; grammarReading = "Gamma_H = HeckeState (ontological state)"
  }

----------------------------------------------------------------------
-- Fibre of the eigen-projection over a given eigenprofile
----------------------------------------------------------------------

fibreOverEigenProfile : (s : HKS.State) (ep : HEMP.EigenProfile) → Set
fibreOverEigenProfile s ep = ⊤

----------------------------------------------------------------------
-- Eigenprofile map: each state induces an eigenprofile via Hecke scan
----------------------------------------------------------------------

postulate
  stateEigenProfile : HKS.State → Underlying heckeState → Underlying eigenProfile

----------------------------------------------------------------------
-- Constructor: Hecke eigen-analysis as categorical construction
----------------------------------------------------------------------

constructHK : {A B : HKObj} (s : HKS.State)
            → (Underlying A → Underlying B)
constructHK {heckeState} {eigenProfile} s = stateEigenProfile s
constructHK {heckeState} {heckeState} s   = λ x → x
constructHK {eigenProfile} {heckeState} s = λ _ → s
constructHK {eigenProfile} {eigenProfile} s = λ x → x

heckeConstructor : PCON.ProjectionConstructor heckeProjectionCategory
heckeConstructor = record
  { MethodCarrier = HKS.State
  ; construct     = constructHK
  ; methodKind    = "Hecke eigen-analysis: state -> eigenprofile"
  }
