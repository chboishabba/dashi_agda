module DASHI.Physics.CLOCKPhaseInstance where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Nat using (_≤_)
open import Data.Nat.Properties as NatP using (≤-refl)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (trans; sym)

open import Base369 using (HexTruth; TriTruth; rotateHex; rotateTri)
open import DASHI.Physics.CLOCKPhaseBridge using
  ( PhaseLift
  ; HexPhaseAdvance²
  ; coarseHex
  ; coarseHex-rotateHex
  ; step²
  ; coarsePhase
  ; coarsePhase-step²
  )
open import UFTC_Lattice as UFTC using (ConeInterior; ConeInteriorPreserved)

record ClockState : Set where
  constructor clk
  field
    hand   : HexTruth
    lagBit : Bool

open ClockState public

clockStep : ClockState → ClockState
clockStep (clk h false) = clk h true
clockStep (clk h true)  = clk (rotateHex h) false

clockPhase : ClockState → HexTruth
clockPhase = hand

clockLift : PhaseLift
clockLift = record
  { State = ClockState
  ; step  = clockStep
  ; phase = clockPhase
  }

clock-step²-even : ∀ h → step² clockLift (clk h false) ≡ clk (rotateHex h) false
clock-step²-even h = refl

clock-step²-odd : ∀ h → step² clockLift (clk h true) ≡ clk (rotateHex h) true
clock-step²-odd h = refl

clockPhaseAdvance² : HexPhaseAdvance² clockLift
clockPhaseAdvance² = record
  { phase-step² = phase-step²
  }
  where
    phase-step² : ∀ x → PhaseLift.phase clockLift (step² clockLift x) ≡ rotateHex (PhaseLift.phase clockLift x)
    phase-step² (clk h false) = refl
    phase-step² (clk h true)  = refl

clock-coarsePhase-step² :
  ∀ x →
  coarsePhase clockLift (step² clockLift x) ≡
  rotateTri (coarsePhase clockLift x)
clock-coarsePhase-step² = coarsePhase-step² clockLift clockPhaseAdvance²

lagDefect : ClockState → Nat
lagDefect (clk h false) = zero
lagDefect (clk h true)  = suc zero

clock-lag-resolved : ∀ h → lagDefect (clk h false) ≡ zero
clock-lag-resolved h = refl

clock-lag-stable-under-step² :
  ∀ x →
  lagDefect (step² clockLift x) ≡ lagDefect x
clock-lag-stable-under-step² (clk h false) = refl
clock-lag-stable-under-step² (clk h true) = refl

lagBit-step²-preserved :
  ∀ x → lagBit (step² clockLift x) ≡ lagBit x
lagBit-step²-preserved (clk h false) = refl
lagBit-step²-preserved (clk h true) = refl

strobeInv : ClockState → Set
strobeInv (clk h lag) = lag ≡ false

lagDefect-nonincreasing-step² :
  ∀ x →
  lagDefect (step² clockLift x) ≤ lagDefect x
lagDefect-nonincreasing-step² x
  rewrite clock-lag-stable-under-step² x
  = NatP.≤-refl

StrobeState : Set
StrobeState = HexTruth

strobeStep : StrobeState → StrobeState
strobeStep = rotateHex

strobeEmbed : StrobeState → ClockState
strobeEmbed h = clk h false

strobeProject : ClockState → StrobeState
strobeProject = hand

normalizeToStrobe : ClockState → ClockState
normalizeToStrobe (clk h false) = clk h false
normalizeToStrobe (clk h true)  = clk (rotateHex h) false

strobeInv-embed : ∀ h → strobeInv (strobeEmbed h)
strobeInv-embed h = refl

normalizeToStrobe-inv : ∀ x → strobeInv (normalizeToStrobe x)
normalizeToStrobe-inv (clk h false) = refl
normalizeToStrobe-inv (clk h true) = refl

normalizeToStrobe-id-onInv :
  ∀ x →
  strobeInv x →
  normalizeToStrobe x ≡ x
normalizeToStrobe-id-onInv (clk h false) _ = refl
normalizeToStrobe-id-onInv (clk h true) ()

normalizeToStrobe-is-step-if-needed :
  ∀ x →
  normalizeToStrobe x ≡ x ⊎ normalizeToStrobe x ≡ clockStep x
normalizeToStrobe-is-step-if-needed (clk h false) = inj₁ refl
normalizeToStrobe-is-step-if-needed (clk h true) = inj₂ refl

strobeEmbedProject-onInv :
  ∀ x →
  strobeInv x →
  strobeEmbed (strobeProject x) ≡ x
strobeEmbedProject-onInv (clk h false) _ = refl
strobeEmbedProject-onInv (clk h true) ()

strobeInv-step² :
  ∀ x →
  strobeInv x →
  strobeInv (step² clockLift x)
strobeInv-step² (clk h false) _ = refl
strobeInv-step² (clk h true)  ()

strobePhase : StrobeState → TriTruth
strobePhase = coarseHex

clock-step²-on-strobe :
  ∀ h →
  step² clockLift (strobeEmbed h) ≡ strobeEmbed (strobeStep h)
clock-step²-on-strobe h = refl

normalizeToStrobe-step² :
  ∀ x →
  step² clockLift (normalizeToStrobe x) ≡
  strobeEmbed (strobeStep (strobeProject (normalizeToStrobe x)))
normalizeToStrobe-step² (clk h false) = refl
normalizeToStrobe-step² (clk h true) = refl

strobeProject-step² :
  ∀ x →
  strobeProject (step² clockLift x) ≡ strobeStep (strobeProject x)
strobeProject-step² (clk h false) = refl
strobeProject-step² (clk h true) = refl

strobe-coarse-dynamics :
  ∀ h →
  strobePhase (strobeStep h) ≡ rotateTri (strobePhase h)
strobe-coarse-dynamics = coarseHex-rotateHex

clock-effective-coarse-dynamics :
  ∀ h →
  coarsePhase clockLift (step² clockLift (strobeEmbed h)) ≡
  rotateTri (coarsePhase clockLift (strobeEmbed h))
clock-effective-coarse-dynamics h = clock-coarsePhase-step² (strobeEmbed h)

record EffectiveClockClosure : Set₁ where
  field
    Inv                : ClockState → Set
    inv-step²          : ∀ x → Inv x → Inv (step² clockLift x)
    defect             : ClockState → Nat
    defect-nonincr-step² :
      ∀ x → defect (step² clockLift x) ≤ defect x
    coarse-phase-step² :
      ∀ x → Inv x →
      coarsePhase clockLift (step² clockLift x) ≡
      rotateTri (coarsePhase clockLift x)

clockEffectiveClosure : EffectiveClockClosure
clockEffectiveClosure =
  record
    { Inv = strobeInv
    ; inv-step² = strobeInv-step²
    ; defect = lagDefect
    ; defect-nonincr-step² = lagDefect-nonincreasing-step²
    ; coarse-phase-step² = λ x _ → clock-coarsePhase-step² x
    }

------------------------------------------------------------------------
-- Cone admissibility on the stroboscopic sector
------------------------------------------------------------------------

ClockCone : ConeInterior {ClockState}
ClockCone =
  record
    { InInterior = λ x → lagBit x ≡ false
    ; Boundary   = λ x → lagBit x ≡ true
    }

clockStep²-conePreserved : ConeInteriorPreserved (step² clockLift) ClockCone
clockStep²-conePreserved =
  record
    { preserve = λ x interior →
        inj₁ (trans (lagBit-step²-preserved x) interior)
    }

record EffectiveClockCone : Set₁ where
  field
    cone          : ConeInterior {ClockState}
    conePreserved : ConeInteriorPreserved (step² clockLift) cone

clockEffectiveCone : EffectiveClockCone
clockEffectiveCone =
  record
    { cone = ClockCone
    ; conePreserved = clockStep²-conePreserved
    }

------------------------------------------------------------------------
-- Bridging the concrete clock cone/closure into a step² bridge package
------------------------------------------------------------------------

record PhasePhysicsBridgeStep² : Set₁ where
  field
    lift                 : PhaseLift
    phaseAdvance²        : HexPhaseAdvance² lift
    cone                 : ConeInterior {X = PhaseLift.State lift}
    conePreserved-step²  : ConeInteriorPreserved (step² lift) cone
    defect               : PhaseLift.State lift → Nat
    defect-nonincr-step² : ∀ x → defect (step² lift x) ≤ defect x
    coarse-phase-step²   :
      ∀ x → coarsePhase lift (step² lift x) ≡ rotateTri (coarsePhase lift x)

open PhasePhysicsBridgeStep² public

clockBridgeStep² : PhasePhysicsBridgeStep²
clockBridgeStep² =
  record
    { lift = clockLift
    ; phaseAdvance² = clockPhaseAdvance²
    ; cone = ClockCone
    ; conePreserved-step² = clockStep²-conePreserved
    ; defect = lagDefect
    ; defect-nonincr-step² = lagDefect-nonincreasing-step²
    ; coarse-phase-step² = clock-coarsePhase-step²
    }

record EffectiveClockSectorBridge : Set₁ where
  field
    project           : ClockState → StrobeState
    embed             : StrobeState → ClockState
    embed-project-inv : ∀ x → strobeInv x → embed (project x) ≡ x
    project-step²     : ∀ x → project (step² clockLift x) ≡ strobeStep (project x)
    embed-step        : ∀ h → step² clockLift (embed h) ≡ embed (strobeStep h)

clockSectorBridge : EffectiveClockSectorBridge
clockSectorBridge =
  record
    { project = strobeProject
    ; embed = strobeEmbed
    ; embed-project-inv = strobeEmbedProject-onInv
    ; project-step² = strobeProject-step²
    ; embed-step = clock-step²-on-strobe
    }
