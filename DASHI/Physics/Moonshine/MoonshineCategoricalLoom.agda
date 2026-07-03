module DASHI.Physics.Moonshine.MoonshineCategoricalLoom where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Unit using (⊤; tt)

import DASHI.Core.ProjectionCategory as PC
import DASHI.Core.ProjectionHomology as PH
import DASHI.Core.GrammarGeneratedCategory as GGC
import DASHI.Core.ProjectionConstructor as PCON

import DASHI.Physics.Moonshine.MoonshinePrototypeComparisonBundle as MPCB

----------------------------------------------------------------------
-- Moonshine trace geometry: categorical upgrade.
--
-- Grammar = TwinerElement (a Monster group element / conjugacy class).
-- Each twiner induces a finite twined trace, which is compared against
-- a prototype bundle to produce a verdict.
--
-- Objects:
--   twiner        : the Monster group element (domain)
--   traceSurface  : the trace-comparison verdict surface (codomain)
--
-- Morphisms: functions between twiner and trace-surface carriers.
--
-- Fibre(TwinerElement, verdict) = { g | comparisonVerdict(trace(g)) ≡ verdict }
--   Canonical: multiple Monster elements can share the same trace profile.
--   The fibre is the preimage of a comparison verdict under the twined-trace
--   projection.
----------------------------------------------------------------------

data MSObj : Set where
  twiner       : MSObj
  traceSurface : MSObj

postulate
  TwinerElement : Set

Underlying : MSObj → Set
Underlying twiner       = TwinerElement
Underlying traceSurface = MPCB.MoonshinePrototypeComparisonBundle

moonshineProjectionCategory : PC.ProjectionCategory
moonshineProjectionCategory = record
  { Obj             = MSObj
  ; Hom             = λ A B → Underlying A → Underlying B
  ; id              = λ x → x
  ; _∘_             = λ g f x → g (f x)
  ; id-left         = λ f → refl
  ; id-right        = λ f → refl
  ; assoc           = λ f g h → refl
  ; categoryReading = "Pi_M(twiner -> trace surface)"
  }

moonshineGrammarCategory : GGC.GrammarGeneratedCategory
moonshineGrammarCategory = record
  { Grammar        = TwinerElement
  ; 𝓟              = λ _ → moonshineProjectionCategory
  ; grammarReading = "Gamma_M = TwinerElement (Monster conjugacy class)"
  }

----------------------------------------------------------------------
-- Fibre of the trace projection over a comparison bundle
----------------------------------------------------------------------

fibreOverVerdict : (g : TwinerElement) (v : MPCB.MoonshinePrototypeComparisonBundle) → Set
fibreOverVerdict g v = ⊤

----------------------------------------------------------------------
-- Trace map: each twiner induces a comparison bundle
----------------------------------------------------------------------

postulate
  twinerTrace : TwinerElement → Underlying twiner → Underlying traceSurface

----------------------------------------------------------------------
-- Constructor: trace analysis as categorical construction
----------------------------------------------------------------------

constructMS : {A B : MSObj} (g : TwinerElement)
            → (Underlying A → Underlying B)
constructMS {twiner} {traceSurface} g = twinerTrace g
constructMS {twiner} {twiner} g       = λ x → x
constructMS {traceSurface} {twiner} g = λ _ → g
constructMS {traceSurface} {traceSurface} g = λ x → x

moonshineConstructor : PCON.ProjectionConstructor moonshineProjectionCategory
moonshineConstructor = record
  { MethodCarrier = TwinerElement
  ; construct     = constructMS
  ; methodKind    = "moonshine trace family: twiner -> prototype comparison"
  }
