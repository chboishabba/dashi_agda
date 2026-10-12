module DASHI.Physics.Plasma.Phase243TorusReparameterizationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Algebra.TriadicDepthOneCharacters as C3
import DASHI.Physics.Plasma.PhaseRook270Exact as Rook

------------------------------------------------------------------------
-- INCIDENCE-INDEXED TORUS REPARAMETERIZATION
--
-- The current Phase243 chart uses four harmonic families:
--
--   axisFamily            : theta
--   finiteFamily phase0   : 3 zeta
--   finiteFamily phase1   : theta - 3 zeta
--   finiteFamily phase2   : theta + 3 zeta.
--
-- Encode a discrete torus translation by (a,b) in C3 x C3 with
--
--   Delta theta = 2 pi a / 3,
--   Delta zeta  = 2 pi b / 9.
--
-- The induced harmonic phase shifts are then exactly
--
--   a, b, a-b, a+b  (mod 3).
--
-- The real coefficient convention used by the Python geometry chart is
--   cos(phi) cos(H) + sin(phi) sin(H) = cos(H-phi).
-- Therefore coefficient-phase advance phi -> phi + 2pi/3 is implemented by
-- a coordinate pullback whose harmonic shift is phase2 = -1 mod 3.
------------------------------------------------------------------------

record TorusThirdNinthShift : Set where
  constructor torus-third-ninth-shift
  field
    thetaThird : C3.C3Phase
    zetaNinth : C3.C3Phase

open TorusThirdNinthShift public

harmonicCoordinatePhase :
  Rook.HarmonicFamily → TorusThirdNinthShift → C3.C3Phase
harmonicCoordinatePhase Rook.axisFamily shift = thetaThird shift
harmonicCoordinatePhase (Rook.finiteFamily C3.phase0) shift = zetaNinth shift
harmonicCoordinatePhase (Rook.finiteFamily C3.phase1) shift =
  C3.multiplyPhase
    (thetaThird shift)
    (C3.conjugatePhase (zetaNinth shift))
harmonicCoordinatePhase (Rook.finiteFamily C3.phase2) shift =
  C3.multiplyPhase (thetaThird shift) (zetaNinth shift)

------------------------------------------------------------------------
-- The two harmonic families selected by each Core243 incidence class.
------------------------------------------------------------------------

leftHarmonic : C3.C3Phase → C3.C3Phase → Rook.HarmonicFamily
leftHarmonic C3.phase0 v = Rook.axisFamily
leftHarmonic C3.phase1 C3.phase0 = Rook.finiteFamily C3.phase1
leftHarmonic C3.phase1 C3.phase1 = Rook.finiteFamily C3.phase0
leftHarmonic C3.phase1 C3.phase2 = Rook.finiteFamily C3.phase0
leftHarmonic C3.phase2 v = Rook.finiteFamily v

rightHarmonic : C3.C3Phase → C3.C3Phase → Rook.HarmonicFamily
rightHarmonic C3.phase0 v = Rook.finiteFamily v
rightHarmonic C3.phase1 C3.phase0 = Rook.finiteFamily C3.phase2
rightHarmonic C3.phase1 C3.phase1 = Rook.finiteFamily C3.phase2
rightHarmonic C3.phase1 C3.phase2 = Rook.finiteFamily C3.phase1
rightHarmonic C3.phase2 v = Rook.finiteFamily v

------------------------------------------------------------------------
-- Canonical translation solving "both selected harmonics shift by -1".
-- incidenceU is a channel/missing-channel coordinate and does not affect the
-- torus wavevector, so only incidenceClass and incidenceV enter the solution.
------------------------------------------------------------------------

canonicalAdvanceShift :
  C3.C3Phase → C3.C3Phase → TorusThirdNinthShift
canonicalAdvanceShift C3.phase0 C3.phase0 =
  torus-third-ninth-shift C3.phase2 C3.phase2
canonicalAdvanceShift C3.phase0 C3.phase1 =
  torus-third-ninth-shift C3.phase2 C3.phase0
canonicalAdvanceShift C3.phase0 C3.phase2 =
  torus-third-ninth-shift C3.phase2 C3.phase0
canonicalAdvanceShift C3.phase1 C3.phase0 =
  torus-third-ninth-shift C3.phase2 C3.phase0
canonicalAdvanceShift C3.phase1 C3.phase1 =
  torus-third-ninth-shift C3.phase0 C3.phase2
canonicalAdvanceShift C3.phase1 C3.phase2 =
  torus-third-ninth-shift C3.phase1 C3.phase2
canonicalAdvanceShift C3.phase2 C3.phase0 =
  torus-third-ninth-shift C3.phase0 C3.phase2
canonicalAdvanceShift C3.phase2 C3.phase1 =
  torus-third-ninth-shift C3.phase0 C3.phase1
canonicalAdvanceShift C3.phase2 C3.phase2 =
  torus-third-ninth-shift C3.phase0 C3.phase2

leftCanonicalAdvanceShift :
  (k v : C3.C3Phase) →
  harmonicCoordinatePhase (leftHarmonic k v) (canonicalAdvanceShift k v)
  ≡ C3.phase2
leftCanonicalAdvanceShift C3.phase0 C3.phase0 = refl
leftCanonicalAdvanceShift C3.phase0 C3.phase1 = refl
leftCanonicalAdvanceShift C3.phase0 C3.phase2 = refl
leftCanonicalAdvanceShift C3.phase1 C3.phase0 = refl
leftCanonicalAdvanceShift C3.phase1 C3.phase1 = refl
leftCanonicalAdvanceShift C3.phase1 C3.phase2 = refl
leftCanonicalAdvanceShift C3.phase2 C3.phase0 = refl
leftCanonicalAdvanceShift C3.phase2 C3.phase1 = refl
leftCanonicalAdvanceShift C3.phase2 C3.phase2 = refl

rightCanonicalAdvanceShift :
  (k v : C3.C3Phase) →
  harmonicCoordinatePhase (rightHarmonic k v) (canonicalAdvanceShift k v)
  ≡ C3.phase2
rightCanonicalAdvanceShift C3.phase0 C3.phase0 = refl
rightCanonicalAdvanceShift C3.phase0 C3.phase1 = refl
rightCanonicalAdvanceShift C3.phase0 C3.phase2 = refl
rightCanonicalAdvanceShift C3.phase1 C3.phase0 = refl
rightCanonicalAdvanceShift C3.phase1 C3.phase1 = refl
rightCanonicalAdvanceShift C3.phase1 C3.phase2 = refl
rightCanonicalAdvanceShift C3.phase2 C3.phase0 = refl
rightCanonicalAdvanceShift C3.phase2 C3.phase1 = refl
rightCanonicalAdvanceShift C3.phase2 C3.phase2 = refl

------------------------------------------------------------------------
-- Symbolic pullback on the phase labels.
------------------------------------------------------------------------

pullbackPhase :
  Rook.HarmonicFamily → TorusThirdNinthShift → C3.C3Phase → C3.C3Phase
pullbackPhase harmonic shift phase =
  C3.multiplyPhase
    phase
    (C3.conjugatePhase (harmonicCoordinatePhase harmonic shift))

phase2PullbackAdvances : (p : C3.C3Phase) →
  C3.multiplyPhase p (C3.conjugatePhase C3.phase2)
  ≡ Rook.advancePhase p
phase2PullbackAdvances C3.phase0 = refl
phase2PullbackAdvances C3.phase1 = refl
phase2PullbackAdvances C3.phase2 = refl

pullbackCoreByCanonicalAdvance : Rook.Core243 → Rook.Core243
pullbackCoreByCanonicalAdvance (Rook.core243 k u v p q) =
  Rook.core243
    k u v
    (pullbackPhase (leftHarmonic k v) (canonicalAdvanceShift k v) p)
    (pullbackPhase (rightHarmonic k v) (canonicalAdvanceShift k v) q)

canonicalAdvancePullbackIntertwines : (x : Rook.Core243) →
  pullbackCoreByCanonicalAdvance x ≡ Rook.advanceCore x
canonicalAdvancePullbackIntertwines (Rook.core243 k u v p q)
  rewrite leftCanonicalAdvanceShift k v
        | rightCanonicalAdvanceShift k v
        | phase2PullbackAdvances p
        | phase2PullbackAdvances q = refl

------------------------------------------------------------------------
-- Spatial reflection (theta,zeta) -> (-theta,-zeta) sends every real harmonic
-- phase to its conjugate.  At the symbolic carrier this is exactly inversion.
------------------------------------------------------------------------

reflectCore : Rook.Core243 → Rook.Core243
reflectCore (Rook.core243 k u v p q) =
  Rook.core243 k u v (C3.conjugatePhase p) (C3.conjugatePhase q)

reflectionIntertwines : (x : Rook.Core243) →
  reflectCore x ≡ Rook.inverseCore x
reflectionIntertwines (Rook.core243 k u v p q) = refl

------------------------------------------------------------------------
-- Boundary / executable receipt.
------------------------------------------------------------------------

record Phase243TorusReparameterizationBoundary : Set where
  constructor phase243-torus-reparameterization-boundary
  field
    everyCoreIncidenceHasCanonicalAdvanceShift : Bool
    everyCoreIncidenceHasCanonicalAdvanceShiftIsTrue :
      everyCoreIncidenceHasCanonicalAdvanceShift ≡ true
    phaseAdvanceHasExactSymbolicTorusPullback : Bool
    phaseAdvanceHasExactSymbolicTorusPullbackIsTrue :
      phaseAdvanceHasExactSymbolicTorusPullback ≡ true
    inversionHasExactSymbolicReflection : Bool
    inversionHasExactSymbolicReflectionIsTrue :
      inversionHasExactSymbolicReflection ≡ true
    symbolicIntertwinerAloneProvesCoilEngineeringSymmetry : Bool
    symbolicIntertwinerAloneProvesCoilEngineeringSymmetryIsFalse :
      symbolicIntertwinerAloneProvesCoilEngineeringSymmetry ≡ false

canonicalPhase243TorusReparameterizationBoundary :
  Phase243TorusReparameterizationBoundary
canonicalPhase243TorusReparameterizationBoundary =
  phase243-torus-reparameterization-boundary
    true refl
    true refl
    true refl
    false refl

pythonIntertwinerReference : String
pythonIntertwinerReference =
  "scripts/phase243_torus_intertwiner.py: all 27 incidence shifts solved; all 243 two-harmonic states replay phase advance by torus translation and inversion by reflection to floating error below 1e-12."
