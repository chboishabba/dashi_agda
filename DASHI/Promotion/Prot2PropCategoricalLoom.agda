module DASHI.Promotion.Prot2PropCategoricalLoom where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Sigma using (Σ; _,_)
open import Agda.Builtin.Unit using (⊤; tt)

import DASHI.Core.ProjectionCategory as PC
import DASHI.Core.GrammarGeneratedCategory as GGC
import DASHI.Core.ProjectionConstructor as PCON

import DASHI.Promotion.Prot2PropArchitecture as P2P
import DASHI.Promotion.ProteinEncoding as PE

----------------------------------------------------------------------
-- Prot2Prop: categorical upgrade.
----------------------------------------------------------------------

data Prot2PropObj : Set where
  carrier' : Prot2PropObj
  surface'  : P2P.Property -> Prot2PropObj

Underlying : Prot2PropObj -> Set
Underlying carrier'      = P2P.ProteinLatentCarrier
Underlying (surface' p)  = P2P.PropertySurface p

prot2PropProjectionCategory : P2P.Property -> PC.ProjectionCategory
prot2PropProjectionCategory p = record
  { Obj             = Prot2PropObj
  ; Hom             = λ A B -> Underlying A -> Underlying B
  ; id              = λ x -> x
  ; _∘_             = λ g f x -> g (f x)
  ; id-left         = λ f -> refl
  ; id-right        = λ f -> refl
  ; assoc           = λ f g h -> refl
  ; categoryReading = "Pi_Prot2Prop(property)"
  }

prot2PropGrammarCategory : GGC.GrammarGeneratedCategory
prot2PropGrammarCategory = record
  { Grammar        = P2P.Property
  ; 𝓟              = prot2PropProjectionCategory
  ; grammarReading = "Gamma_Prot2Prop = Property"
  }

constructP2P : {A B : Prot2PropObj} (r : P2P.ProteinLatentCarrier)
             → (Underlying A → Underlying B)
constructP2P {carrier'} {carrier'} r      = λ x → x
constructP2P {carrier'} {surface' p} r    = λ x → P2P.f p x
constructP2P {surface' p} {carrier'} r    = λ _ → r
constructP2P {surface' p} {surface' q} r  = λ x → x

prot2PropConstructor : PCON.ProjectionConstructor (prot2PropProjectionCategory PE.Solubility)
prot2PropConstructor = record
  { MethodCarrier = P2P.ProteinLatentCarrier
  ; construct     = constructP2P
  ; methodKind    = "multi-task learning"
  }
