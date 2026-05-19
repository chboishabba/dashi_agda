module DASHI.Physics.CLOCKPhaseBridge where

open import Agda.Builtin.Equality using (_≡_; refl)

open import Base369 using
  ( HexTruth
  ; TriTruth
  ; hex-0
  ; hex-1
  ; hex-2
  ; hex-3
  ; hex-4
  ; hex-5
  ; tri-low
  ; tri-mid
  ; tri-high
  ; rotateHex
  ; rotateTri
  ; spin
  )
open import Contraction as Contr using (Contractive≢)
open import DASHI.MDL.MDLLyapunov as MDL using (MDLFunctional; MDLLyapunov)
open import UFTC_Lattice as UFTC using (ConeInterior; ConeInteriorPreserved)
open import Ultrametric as UMetric using (Ultrametric)

coarseHex : HexTruth → TriTruth
coarseHex hex-0 = tri-low
coarseHex hex-1 = tri-mid
coarseHex hex-2 = tri-high
coarseHex hex-3 = tri-low
coarseHex hex-4 = tri-mid
coarseHex hex-5 = tri-high

coarseHex-rotateHex : ∀ h → coarseHex (rotateHex h) ≡ rotateTri (coarseHex h)
coarseHex-rotateHex hex-0 = refl
coarseHex-rotateHex hex-1 = refl
coarseHex-rotateHex hex-2 = refl
coarseHex-rotateHex hex-3 = refl
coarseHex-rotateHex hex-4 = refl
coarseHex-rotateHex hex-5 = refl

coarseHex-spin¹ : ∀ h → coarseHex (spin 1 rotateHex h) ≡ rotateTri (coarseHex h)
coarseHex-spin¹ = coarseHex-rotateHex

coarseHex-six-step-cycle : ∀ h → coarseHex (spin 6 rotateHex h) ≡ coarseHex h
coarseHex-six-step-cycle hex-0 = refl
coarseHex-six-step-cycle hex-1 = refl
coarseHex-six-step-cycle hex-2 = refl
coarseHex-six-step-cycle hex-3 = refl
coarseHex-six-step-cycle hex-4 = refl
coarseHex-six-step-cycle hex-5 = refl

record PhaseLift : Set₁ where
  field
    State : Set
    step  : State → State
    phase : State → HexTruth

open PhaseLift public

step² : (P : PhaseLift) → State P → State P
step² P x = step P (step P x)

coarsePhase : (P : PhaseLift) → State P → TriTruth
coarsePhase P x = coarseHex (phase P x)

record HexPhaseAdvance² (P : PhaseLift) : Set₁ where
  field
    phase-step² : ∀ x → phase P (step² P x) ≡ rotateHex (phase P x)

open HexPhaseAdvance² public

coarsePhase-step² :
  (P : PhaseLift) →
  HexPhaseAdvance² P →
  ∀ x →
  coarsePhase P (step² P x) ≡ rotateTri (coarsePhase P x)
coarsePhase-step² P A x
  rewrite phase-step² A x
  = coarseHex-rotateHex (phase P x)

record PhasePhysicsBridge : Set₁ where
  field
    lift            : PhaseLift
    phaseAdvance²   : HexPhaseAdvance² lift
    cone            : ConeInterior {X = State lift}
    conePreserved   : ConeInteriorPreserved (step lift) cone
    ultrametric     : Ultrametric (State lift)
    contractive     : Contractive≢ ultrametric (step lift)
    mdlFunctional   : MDLFunctional (State lift)
    mdlLyapunov     : MDLLyapunov (step lift) mdlFunctional

open PhasePhysicsBridge public

bridge-coarsePhase-step² :
  (B : PhasePhysicsBridge) →
  ∀ x →
  coarsePhase (lift B) (step² (lift B) x) ≡ rotateTri (coarsePhase (lift B) x)
bridge-coarsePhase-step² B = coarsePhase-step² (lift B) (phaseAdvance² B)
