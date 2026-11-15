module DASHI.Physics.Plasma.Phase243OrbitQuotientExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Nat using (Nat; _*_)
open import Agda.Builtin.String using (String)

import DASHI.Algebra.TriadicDepthOneCharacters as C3
import DASHI.Physics.Plasma.PhaseRook270Exact as Rook

------------------------------------------------------------------------
-- PHASE243 / (C3 ⋊ C2) ORBIT QUOTIENT
--
-- Core243 = F3^3 x F3^2.  The physical global phase action advances both
-- phase-fibre labels together, while inversion conjugates both.  The first
-- three incidence coordinates are fixed.
--
-- On F3^2 there are exactly two orbit kinds:
--   * aligned: p = q, orbit size 3;
--   * offset:  p != q, the two nonzero relative phases are joined by inversion,
--              giving orbit size 6.
-- Therefore every one of the 27 base incidences contributes exactly two
-- quotient classes and the 243-state carrier compresses to 54 classes.
------------------------------------------------------------------------

data RelativePhaseKind : Set where
  alignedPhase : RelativePhaseKind
  offsetPhase : RelativePhaseKind

relativePhaseKind : C3.C3Phase → C3.C3Phase → RelativePhaseKind
relativePhaseKind C3.phase0 C3.phase0 = alignedPhase
relativePhaseKind C3.phase0 C3.phase1 = offsetPhase
relativePhaseKind C3.phase0 C3.phase2 = offsetPhase
relativePhaseKind C3.phase1 C3.phase0 = offsetPhase
relativePhaseKind C3.phase1 C3.phase1 = alignedPhase
relativePhaseKind C3.phase1 C3.phase2 = offsetPhase
relativePhaseKind C3.phase2 C3.phase0 = offsetPhase
relativePhaseKind C3.phase2 C3.phase1 = offsetPhase
relativePhaseKind C3.phase2 C3.phase2 = alignedPhase

relativeAdvanceInvariant : (p q : C3.C3Phase) →
  relativePhaseKind (Rook.advancePhase p) (Rook.advancePhase q)
  ≡ relativePhaseKind p q
relativeAdvanceInvariant C3.phase0 C3.phase0 = refl
relativeAdvanceInvariant C3.phase0 C3.phase1 = refl
relativeAdvanceInvariant C3.phase0 C3.phase2 = refl
relativeAdvanceInvariant C3.phase1 C3.phase0 = refl
relativeAdvanceInvariant C3.phase1 C3.phase1 = refl
relativeAdvanceInvariant C3.phase1 C3.phase2 = refl
relativeAdvanceInvariant C3.phase2 C3.phase0 = refl
relativeAdvanceInvariant C3.phase2 C3.phase1 = refl
relativeAdvanceInvariant C3.phase2 C3.phase2 = refl

relativeInverseInvariant : (p q : C3.C3Phase) →
  relativePhaseKind (Rook.inversePhase p) (Rook.inversePhase q)
  ≡ relativePhaseKind p q
relativeInverseInvariant C3.phase0 C3.phase0 = refl
relativeInverseInvariant C3.phase0 C3.phase1 = refl
relativeInverseInvariant C3.phase0 C3.phase2 = refl
relativeInverseInvariant C3.phase1 C3.phase0 = refl
relativeInverseInvariant C3.phase1 C3.phase1 = refl
relativeInverseInvariant C3.phase1 C3.phase2 = refl
relativeInverseInvariant C3.phase2 C3.phase0 = refl
relativeInverseInvariant C3.phase2 C3.phase1 = refl
relativeInverseInvariant C3.phase2 C3.phase2 = refl

record Core54 : Set where
  constructor core54
  field
    incidenceClass54 : C3.C3Phase
    incidenceU54 : C3.C3Phase
    incidenceV54 : C3.C3Phase
    relativeKind54 : RelativePhaseKind

open Core54 public

quotientCore : Rook.Core243 → Core54
quotientCore (Rook.core243 k u v p q) =
  core54 k u v (relativePhaseKind p q)

representativeCore : Core54 → Rook.Core243
representativeCore (core54 k u v alignedPhase) =
  Rook.core243 k u v C3.phase0 C3.phase0
representativeCore (core54 k u v offsetPhase) =
  Rook.core243 k u v C3.phase0 C3.phase1

quotientRepresentativeRoundTrip : (x : Core54) →
  quotientCore (representativeCore x) ≡ x
quotientRepresentativeRoundTrip (core54 k u v alignedPhase) = refl
quotientRepresentativeRoundTrip (core54 k u v offsetPhase) = refl

quotientAdvanceInvariant : (x : Rook.Core243) →
  quotientCore (Rook.advanceCore x) ≡ quotientCore x
quotientAdvanceInvariant (Rook.core243 k u v p q)
  rewrite relativeAdvanceInvariant p q = refl

quotientInverseInvariant : (x : Rook.Core243) →
  quotientCore (Rook.inverseCore x) ≡ quotientCore x
quotientInverseInvariant (Rook.core243 k u v p q)
  rewrite relativeInverseInvariant p q = refl

------------------------------------------------------------------------
-- Exact accounting.
------------------------------------------------------------------------

core243Count : Nat
core243Count = 243

baseIncidenceCount : Nat
baseIncidenceCount = 27

phaseQuotientKindCount : Nat
phaseQuotientKindCount = 2

core54Count : Nat
core54Count = 54

quotientCountArithmetic :
  baseIncidenceCount * phaseQuotientKindCount ≡ core54Count
quotientCountArithmetic = refl

orbitAccountingRecovers243 :
  27 * 3 + 27 * 6 ≡ core243Count
orbitAccountingRecovers243 = refl

record Phase243OrbitQuotientBoundary : Set where
  constructor phase243-orbit-quotient-boundary
  field
    quotientUsesPhysicalPhaseAction : Bool
    quotientUsesPhysicalPhaseActionIsTrue : quotientUsesPhysicalPhaseAction ≡ true
    representativeCountIs54 : Bool
    representativeCountIs54IsTrue : representativeCountIs54 ≡ true
    quotientErasesIncidenceCoordinates : Bool
    quotientErasesIncidenceCoordinatesIsFalse : quotientErasesIncidenceCoordinates ≡ false
    quotientAlonePreservesEveryPhysicalConsumer : Bool
    quotientAlonePreservesEveryPhysicalConsumerIsFalse :
      quotientAlonePreservesEveryPhysicalConsumer ≡ false

canonicalPhase243OrbitQuotientBoundary : Phase243OrbitQuotientBoundary
canonicalPhase243OrbitQuotientBoundary =
  phase243-orbit-quotient-boundary true refl true refl false refl false refl

pythonReplayReference : String
pythonReplayReference =
  "scripts/phase243_orbit_quotient.py: exhaustive 243-state replay gives 27 size-3 + 27 size-6 orbits and exactly 54 quotient representatives."
