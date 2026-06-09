module DASHI.Physics.Closure.ExtremalFrobeniusVec15OrbitAction where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

open import MonsterOntos using (SSP; p47; p59; p71)
import Ontology.GodelLattice as GL
import DASHI.Physics.Closure.ExtremalFrobeniusVacuumFixedPoint as Vacuum

------------------------------------------------------------------------
-- Vec15 orbit action under the extremal p47/p59/p71 clocks.
--
-- No module named
-- DASHI.Physics.Closure.ExtremalFrobeniusClockCarrier is present in this
-- checkout, so the clock triple target is local and minimal here.

missingClockCarrierImport :
  String
missingClockCarrierImport =
  "DASHI.Physics.Closure.ExtremalFrobeniusClockCarrier"

data ExtremalClock : Set where
  clock47 :
    ExtremalClock

  clock59 :
    ExtremalClock

  clock71 :
    ExtremalClock

clockPrime :
  ExtremalClock →
  SSP
clockPrime clock47 =
  p47
clockPrime clock59 =
  p59
clockPrime clock71 =
  p71

record ExtremalClockTriple : Set where
  field
    p47Clock :
      ExtremalClock

    p59Clock :
      ExtremalClock

    p71Clock :
      ExtremalClock

    p47ClockIsCanonical :
      p47Clock
      ≡
      clock47

    p59ClockIsCanonical :
      p59Clock
      ≡
      clock59

    p71ClockIsCanonical :
      p71Clock
      ≡
      clock71

open ExtremalClockTriple public

canonicalExtremalClockTriple :
  ExtremalClockTriple
canonicalExtremalClockTriple =
  record
    { p47Clock =
        clock47
    ; p59Clock =
        clock59
    ; p71Clock =
        clock71
    ; p47ClockIsCanonical =
        refl
    ; p59ClockIsCanonical =
        refl
    ; p71ClockIsCanonical =
        refl
    }

zeroFactorVec :
  GL.FactorVec
zeroFactorVec =
  Vacuum.zeroFactorVec

setLaneZero :
  SSP →
  GL.FactorVec →
  GL.FactorVec
setLaneZero p =
  GL.updateVec15 p (λ _ → zero)

clockLaneAction :
  ExtremalClock →
  GL.FactorVec →
  GL.FactorVec
clockLaneAction clock47 =
  setLaneZero p47
clockLaneAction clock59 =
  setLaneZero p59
clockLaneAction clock71 =
  setLaneZero p71

extremalClockTripleAction :
  ExtremalClockTriple →
  GL.FactorVec →
  GL.FactorVec
extremalClockTripleAction clocks v =
  clockLaneAction (p71Clock clocks)
    (clockLaneAction (p59Clock clocks)
      (clockLaneAction (p47Clock clocks) v))

canonicalExtremalClockTripleAction :
  GL.FactorVec →
  GL.FactorVec
canonicalExtremalClockTripleAction =
  extremalClockTripleAction canonicalExtremalClockTriple

identityClockAction :
  GL.FactorVec →
  GL.FactorVec
identityClockAction v =
  v

p47ZeroFixed :
  clockLaneAction clock47 zeroFactorVec
  ≡
  zeroFactorVec
p47ZeroFixed =
  refl

p59ZeroFixed :
  clockLaneAction clock59 zeroFactorVec
  ≡
  zeroFactorVec
p59ZeroFixed =
  refl

p71ZeroFixed :
  clockLaneAction clock71 zeroFactorVec
  ≡
  zeroFactorVec
p71ZeroFixed =
  refl

tripleZeroFixed :
  canonicalExtremalClockTripleAction zeroFactorVec
  ≡
  zeroFactorVec
tripleZeroFixed =
  refl

identityLaw :
  (v : GL.FactorVec) →
  identityClockAction v
  ≡
  v
identityLaw v =
  refl

setLaneZeroIdempotent :
  (p : SSP) →
  (v : GL.FactorVec) →
  setLaneZero p (setLaneZero p v)
  ≡
  setLaneZero p v
setLaneZeroIdempotent p
  (GL.v15 e2 e3 e5 e7 e11 e13 e17 e19 e23 e29 e31 e41 e47 e59 e71)
  with p
... | MonsterOntos.p2 =
  refl
... | MonsterOntos.p3 =
  refl
... | MonsterOntos.p5 =
  refl
... | MonsterOntos.p7 =
  refl
... | MonsterOntos.p11 =
  refl
... | MonsterOntos.p13 =
  refl
... | MonsterOntos.p17 =
  refl
... | MonsterOntos.p19 =
  refl
... | MonsterOntos.p23 =
  refl
... | MonsterOntos.p29 =
  refl
... | MonsterOntos.p31 =
  refl
... | MonsterOntos.p41 =
  refl
... | MonsterOntos.p47 =
  refl
... | MonsterOntos.p59 =
  refl
... | MonsterOntos.p71 =
  refl

canonicalTripleIdempotent :
  (v : GL.FactorVec) →
  canonicalExtremalClockTripleAction
    (canonicalExtremalClockTripleAction v)
  ≡
  canonicalExtremalClockTripleAction v
canonicalTripleIdempotent
  (GL.v15 e2 e3 e5 e7 e11 e13 e17 e19 e23 e29 e31 e41 e47 e59 e71) =
  refl

record ExtremalFrobeniusVec15OrbitAction : Set where
  field
    clockCarrierImport :
      String

    clockCarrierImportMissing :
      Bool

    clockCarrierImportMissingIsTrue :
      clockCarrierImportMissing
      ≡
      true

    clocks :
      ExtremalClockTriple

    clocksAreCanonical :
      clocks
      ≡
      canonicalExtremalClockTriple

    orbitAction :
      GL.FactorVec →
      GL.FactorVec

    orbitActionIsCanonical :
      orbitAction
      ≡
      canonicalExtremalClockTripleAction

    p47VacuumFixed :
      clockLaneAction clock47 zeroFactorVec
      ≡
      zeroFactorVec

    p59VacuumFixed :
      clockLaneAction clock59 zeroFactorVec
      ≡
      zeroFactorVec

    p71VacuumFixed :
      clockLaneAction clock71 zeroFactorVec
      ≡
      zeroFactorVec

    zeroVacuumFixed :
      orbitAction zeroFactorVec
      ≡
      zeroFactorVec

    identityAction :
      GL.FactorVec →
      GL.FactorVec

    identityActionLaw :
      (v : GL.FactorVec) →
      identityAction v
      ≡
      v

    canonicalCompositionLaw :
      (v : GL.FactorVec) →
      orbitAction (orbitAction v)
      ≡
      orbitAction v

    orbitCountPromoted :
      Bool

    orbitCountPromotedIsFalse :
      orbitCountPromoted
      ≡
      false

    actionBoundary :
      List String

open ExtremalFrobeniusVec15OrbitAction public

canonicalExtremalFrobeniusVec15OrbitAction :
  ExtremalFrobeniusVec15OrbitAction
canonicalExtremalFrobeniusVec15OrbitAction =
  record
    { clockCarrierImport =
        missingClockCarrierImport
    ; clockCarrierImportMissing =
        true
    ; clockCarrierImportMissingIsTrue =
        refl
    ; clocks =
        canonicalExtremalClockTriple
    ; clocksAreCanonical =
        refl
    ; orbitAction =
        canonicalExtremalClockTripleAction
    ; orbitActionIsCanonical =
        refl
    ; p47VacuumFixed =
        p47ZeroFixed
    ; p59VacuumFixed =
        p59ZeroFixed
    ; p71VacuumFixed =
        p71ZeroFixed
    ; zeroVacuumFixed =
        tripleZeroFixed
    ; identityAction =
        identityClockAction
    ; identityActionLaw =
        identityLaw
    ; canonicalCompositionLaw =
        canonicalTripleIdempotent
    ; orbitCountPromoted =
        false
    ; orbitCountPromotedIsFalse =
        refl
    ; actionBoundary =
        "ExtremalFrobeniusClockCarrier is not present; this module supplies the minimal local p47/p59/p71 clock triple"
        ∷ "The orbit action is the canonical p47, p59, p71 lane-zeroing action through Ontology.GodelLattice.updateVec15"
        ∷ "The zero FactorVec vacuum is fixed by the three lane actions and by the combined clock-triple action"
        ∷ "The identity law is definitional for identityClockAction"
        ∷ "The canonical composition law is the definitional idempotence of setting the same extremal coordinates to zero twice"
        ∷ "No orbit-count theorem, uniqueness theorem, Monster theorem, or terminal claim is promoted here"
        ∷ []
    }
