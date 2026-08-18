module DASHI.Physics.Closure.NSTriadKNCrossModePositiveVortexStretchingWitnessRound78Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: Peter Constantin; Charles Fefferman.
-- Title: "Direction of Vorticity and the Problem of Global Regularity for the
-- Navier-Stokes Equations".
-- DOI: 10.1512/iumj.1993.42.42034.
--
-- Author: Fabian Waleffe.
-- Title: "The nature of triad interactions in homogeneous turbulence".
-- DOI: 10.1063/1.858309.
--
-- ROUND78 / POSITIVE CROSS-MODE FINITE WITNESS
--
-- Round78 proved exact same-mode self-stretching vanishes.  The literal
-- Fourier carrier nevertheless admits a positive interaction between TWO
-- divergence-free Fourier vorticity modes.
--
-- Choose strain/source mode p=(1,0,0) with omega_p=(0,1,0), target/input mode
-- q=(1,0,1) with omega_q=(1,0,-1), and output k=p+q=(2,0,1).  The integer
-- modes are packaged as an actual `PhysicalTriadIncidence`; both vorticities
-- are transverse to their own modes.  On the exact rational strain carrier,
--
--   omega_q . S_p(omega_p) omega_q
--     = - (p.omega_q) p.(omega_p x omega_q)
--     = -(1)(-1)
--     = 1.
--
-- This is an exact physical Fourier-triad geometry witness, but still not a
-- selected Round77 dynamic descendant theorem.  It proves the self-mode no-go
-- does not kill B2 in principle: a cross-mode/nonlocal amplifying channel
-- genuinely exists on the same physical triad geometry.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
import Data.Integer.Base as Int
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _+_; _*_; -_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Triad
import DASHI.Physics.Closure.NSTriadKNRationalLerayProjectionExact as V
import DASHI.Physics.Closure.NSTriadKNFourierStrainMultiplierRound38Exact as Strain

sourceMode : V.Vector3
sourceMode = V.v3 1ℚ 0ℚ 0ℚ

targetMode : V.Vector3
targetMode = V.v3 1ℚ 0ℚ 1ℚ

resonantOutputMode : V.Vector3
resonantOutputMode = V.add sourceMode targetMode

unitXMode : V.ProjectionMode
unitXMode = V.projection-mode sourceMode 1ℚ refl

crossSource : V.Vector3
crossSource = V.v3 0ℚ 1ℚ 0ℚ

crossTarget : V.Vector3
crossTarget = V.v3 1ℚ 0ℚ (- 1ℚ)

sourceVorticityTransverse : V.dot sourceMode crossSource ≡ 0ℚ
sourceVorticityTransverse = solve []

targetVorticityTransverse : V.dot targetMode crossTarget ≡ 0ℚ
targetVorticityTransverse = solve []

resonanceExact : resonantOutputMode ≡ V.v3 (1ℚ + 1ℚ) 0ℚ 1ℚ
resonanceExact = refl

integerP integerQ integerK : Z3.FourierMode
integerP = Z3.mode (Int.+ 1) (Int.+ 0) (Int.+ 0)
integerQ = Z3.mode (Int.+ 1) (Int.+ 0) (Int.+ 1)
integerK = Z3.mode (Int.+ 2) (Int.+ 0) (Int.+ 1)

positiveStretchingTriad : Triad.PhysicalTriadIncidence
positiveStretchingTriad = Triad.physicalTriad integerP integerQ integerK refl

positiveCrossModeStretchingExact :
  Strain.fourierStretchingScalar unitXMode crossSource crossTarget ≡ 1ℚ
positiveCrossModeStretchingExact =
  trans
    (Strain.fourierStretchingMisalignmentExact
      unitXMode crossSource crossTarget)
    (solve [])

round78PositiveCrossModeStretchingExistsOnFourierCarrier : Bool
round78PositiveCrossModeStretchingExistsOnFourierCarrier = true

round78PositiveWitnessIsActualPhysicalTriadIncidence : Bool
round78PositiveWitnessIsActualPhysicalTriadIncidence = true

round78WitnessUsesTwoTransverseVorticityModes : Bool
round78WitnessUsesTwoTransverseVorticityModes = true

round78PositiveCrossModeWitnessAlreadyIsSelectedB2 : Bool
round78PositiveCrossModeWitnessAlreadyIsSelectedB2 = false

round78PositiveCrossModeStretchingExistsOnFourierCarrierIsTrue :
  round78PositiveCrossModeStretchingExistsOnFourierCarrier ≡ true
round78PositiveCrossModeStretchingExistsOnFourierCarrierIsTrue = refl
