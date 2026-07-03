module DASHI.Physics.NSAIEncodingCategoricalLoom where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Unit using (⊤; tt)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Core.ProjectionCategory as PC
import DASHI.Core.GrammarGeneratedCategory as GGC
import DASHI.Core.ProjectionConstructor as PCON

import DASHI.Physics.NSAIEncoding as NSAI

----------------------------------------------------------------------
-- NS-AI: categorical upgrade.
--
-- Objects:
--   carrierPkg   : the (flow × simulation) carrier package
--   observable   : an observable flow surface
--
-- Grammar = FlowObservable.
-- Each observable type generates the projection category where
-- Hom-spaces are functions between the relevant sets.
--
-- Fibre(piNS o, s) = { cp : CarrierPackage | piNS cp o ≡ s }
----------------------------------------------------------------------

data NSAIObj : Set where
  carrierPkg : NSAIObj
  observable : NSAIObj

Underlying : NSAIObj -> Set
Underlying carrierPkg = NSAI.CarrierPackage
Underlying observable  = NSAI.ObservableFlowSurface

nsaiProjectionCategory : NSAI.FlowObservable -> PC.ProjectionCategory
nsaiProjectionCategory o = record
  { Obj             = NSAIObj
  ; Hom             = λ A B -> Underlying A -> Underlying B
  ; id              = λ x -> x
  ; _∘_             = λ g f x -> g (f x)
  ; id-left         = λ f -> refl
  ; id-right        = λ f -> refl
  ; assoc           = λ f g h -> refl
  ; categoryReading = "Pi_NSAI(observable)"
  }

nsaiGrammarCategory : GGC.GrammarGeneratedCategory
nsaiGrammarCategory = record
  { Grammar        = NSAI.FlowObservable
  ; 𝓟              = nsaiProjectionCategory
  ; grammarReading = "Gamma_NSAI = FlowObservable"
  }

constructNSAI : {A B : NSAIObj} (cp : NSAI.CarrierPackage)
              → (Underlying A → Underlying B)
constructNSAI {carrierPkg} {carrierPkg} cp = λ x -> x
constructNSAI {carrierPkg} {observable} cp = λ _ -> NSAI.πNS cp NSAI.VelocityField
constructNSAI {observable} {carrierPkg} cp = λ _ -> cp
constructNSAI {observable} {observable} cp = λ x -> x

nsaiConstructor : PCON.ProjectionConstructor (nsaiProjectionCategory NSAI.VelocityField)
nsaiConstructor = record
  { MethodCarrier = NSAI.CarrierPackage
  ; construct     = constructNSAI
  ; methodKind    = "ML surrogate"
  }
