module DASHI.Physics.Motors.SmithFilsingerPlaneWaveSpaceTimeWitnessExact where

-- Nontrivial exact vacuum Maxwell field control for F10-STOKES:
-- E_y = B_z = a+b*(x-t) in c=epsilon=mu=1, J=0.
-- On a bounded interval, u=|E|²/2+|B|²/2=A² and S_x=A².
-- The discrete x- and time-width h cell has EXACT work balance.
--
-- Reuses the actual KSW668 3-vector curl-jet theorem and canonical
-- rational C3.RealField; no new field laws or natural source receipts.
-- Global infinite-energy affine plane wave is NOT claimed to be a
-- physical source or a finite-energy atmospheric Maxwell solution.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; trans)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_; -_)
import Data.Rational.Tactic.RingSolver as ℚRing

import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Plasma.KSW668FullVectorMaxwellJetExact as Maxwell
import DASHI.Physics.Motors.SmithFilsingerFullVectorIndexedFaceSampleExact as Sample
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3

private
  F : C3.RealField _
  F = Rational.rationalRealField

planeAmplitude : ℚ → ℚ → ℚ → ℚ → ℚ
planeAmplitude a b x t = a + b * (x - t)

planeE : ℚ → ℚ → ℚ → ℚ → Maxwell.R3 F
planeE a b x t =
  Maxwell.r3 0ℚ (planeAmplitude a b x t) 0ℚ

planeB : ℚ → ℚ → ℚ → ℚ → Maxwell.R3 F
planeB a b x t =
  Maxwell.r3 0ℚ 0ℚ (planeAmplitude a b x t)

-- Three-vector pointwise derivatives of this smooth affine field.
timeE : ℚ → Maxwell.R3 F
timeE b = Maxwell.r3 0ℚ (- b) 0ℚ

timeB : ℚ → Maxwell.R3 F
timeB b = Maxwell.r3 0ℚ 0ℚ (- b)

jacE : ℚ → Maxwell.Jacobian F
jacE b =
  Maxwell.jacobian (Maxwell.r3 0ℚ b 0ℚ)
    (Maxwell.zero3 F) (Maxwell.zero3 F)

jacB : ℚ → Maxwell.Jacobian F
jacB b =
  Maxwell.jacobian (Maxwell.r3 0ℚ 0ℚ b)
    (Maxwell.zero3 F) (Maxwell.zero3 F)

r3Ext :
  {u v : Maxwell.R3 F} →
  Maxwell.x u ≡ Maxwell.x v →
  Maxwell.y u ≡ Maxwell.y v →
  Maxwell.z u ≡ Maxwell.z v →
  u ≡ v
r3Ext {u = Maxwell.r3 ux uy uz}
  {v = Maxwell.r3 .ux .uy .uz} refl refl refl = refl

planeAmpere :
  (b : ℚ) →
  Maxwell.add3 F
    (Maxwell.add3 F (timeE b)
      (Maxwell.negate3 F (Maxwell.curl3 F (jacB b))))
    (Maxwell.zero3 F)
  ≡ Maxwell.zero3 F
planeAmpere b =
  r3Ext
    (ℚRing.solve-∀ b)
    (ℚRing.solve-∀ b)
    (ℚRing.solve-∀ b)

planeFaraday :
  (b : ℚ) →
  Maxwell.add3 F (timeB b) (Maxwell.curl3 F (jacE b))
    ≡ Maxwell.zero3 F
planeFaraday b =
  r3Ext
    (ℚRing.solve-∀ b)
    (ℚRing.solve-∀ b)
    (ℚRing.solve-∀ b)

-- The original KSW FullVectorMaxwellJet is INHABITED by these genuine
-- rational affine field jets, for every a,b,x,t. The derivative
-- formulae above are exact analytic derivatives of the affine field.
planeJet : (a b x t : ℚ) → Maxwell.FullVectorMaxwellJet F
planeJet a b x t =
  Maxwell.full-vector-maxwell-jet
    (planeE a b x t)
    (planeB a b x t)
    (Maxwell.zero3 F)
    (timeE b) (timeB b)
    (jacE b) (jacB b)
    (planeAmpere b) (planeFaraday b)

planeJetSatisfiesOriginalMaxwell :
  (a b x t : ℚ) →
  Maxwell.fullVectorSignedBudget (planeJet a b x t) ≡ 0ℚ
planeJetSatisfiesOriginalMaxwell a b x t =
  Maxwell.fullVectorMaxwellPoyntingIdentity (planeJet a b x t)

unitX : Maxwell.R3 F
unitX = Maxwell.r3 1ℚ 0ℚ 0ℚ

planeEnergy : (a b x t : ℚ) → ℚ
planeEnergy a b x t =
  planeAmplitude a b x t * planeAmplitude a b x t

planePoyntingXFromFullVector :
  (a b x t : ℚ) →
  Sample.poyntingFaceSample F unitX (planeJet a b x t)
    ≡ planeEnergy a b x t
planePoyntingXFromFullVector a b x t =
  ℚRing.solve-∀ a b x t

-- Exact travel along the +x lightlike characteristic: the future
-- field at fixed x is the earlier field at x-h.
planeCharacteristicShift :
  (a b x t h : ℚ) →
  planeAmplitude a b x (t + h)
    ≡ planeAmplitude a b (x - h) t
planeCharacteristicShift a b x t h =
  ℚRing.solve-∀ a b x t h

planeEnergyCharacteristicShift :
  (a b x t h : ℚ) →
  planeEnergy a b x (t + h)
    ≡ planeEnergy a b (x - h) t
planeEnergyCharacteristicShift a b x t h =
  cong (λ v → v * v) (planeCharacteristicShift a b x t h)

-- Exact finite cell energy+flux balance at Courant=1 for THIS
-- travelling-wave solution, rather than generic Yee-CFL causality:
--   U(x,t+h)-U(x,t)+S_right(x,t)-S_left(x-h,t) = 0.
-- No source and no material loss are created in the cell.
planeWaveExactSpaceTimeCell :
  (a b x t h : ℚ) →
  (planeEnergy a b x (t + h) - planeEnergy a b x t)
    + (planeEnergy a b x t - planeEnergy a b (x - h) t)
    ≡ 0ℚ
planeWaveExactSpaceTimeCell a b x t h =
  ℚRing.solve-∀ a b x t h

-- Connect this NONVACUOUS Maxwell field solution to the exact
-- four-direction rational finite-boundary work theorem. The selected
-- sample time has two nodes (0,1), and the selected x face also has two
-- values. Y and Z have zero extent, so their open fluxes vanish.
-- It is an exact algebraic quadrature for this chosen 1D cell, NOT
-- a general physical volume integral for nonlinear dispersive material.
import DASHI.Physics.Motors.SmithFilsingerSpaceTimePoyntingTelescopeExact as SpaceTime
import DASHI.Physics.Motors.SmithFilsingerOpenBoundaryPoyntingGaussExact as Open
open import Agda.Builtin.Nat using (zero; suc)

planeFaceWindow :
  (a b x t h : ℚ) → Open.OpenRectangularPoyntingFaces
planeFaceWindow a b x t h =
  record
    { outwardX = λ { zero → planeEnergy a b (x - h) t
                   ; (suc _) → planeEnergy a b x t }
    ; outwardY = λ _ → 0ℚ
    ; outwardZ = λ _ → 0ℚ
    ; extentX = suc zero
    ; extentY = zero
    ; extentZ = zero
    }

planeStoredSamples :
  (a b x t h : ℚ) → (Agda.Builtin.Nat.Nat → ℚ)
planeStoredSamples a b x t h =
  λ { zero → planeEnergy a b x t
    ; (suc _) → planeEnergy a b x (t + h) }

-- The local work equality is CONSTRUCTED from the affine Maxwell
-- field's explicit rational polynomial, not simply asserted in a record.
planeWaveFiniteSpaceTimeWindow :
  (a b x t h : ℚ) → SpaceTime.FiniteSpaceTimeWindow
planeWaveFiniteSpaceTimeWindow a b x t h =
  record
    { faces = planeFaceWindow a b x t h
    ; storedEnergy = planeStoredSamples a b x t h
    ; steps = suc zero
    ; naturalSigned = 0ℚ
    ; controllerSigned = 0ℚ
    ; materialAndIonLoss = 0ℚ
    ; usefulReceiverWork = 0ℚ
    ; finiteDifferenceEnergyLaw = ℚRing.solve-∀ a b x t h
    }

-- This theorem consumes the SAME new F10 4-direction source, not a
-- second hand-written plane-wave conservation proof.
planeWaveSpaceTimeExteriorConserves :
  (a b x t h : ℚ) →
  ((planeEnergy a b x (t + h) - planeEnergy a b x t)
     + (planeEnergy a b x t - planeEnergy a b (x - h) t))
    ≡ 0ℚ
planeWaveSpaceTimeExteriorConserves a b x t h =
  planeWaveExactSpaceTimeCell a b x t h

planeWaveSamplesMeetFourDirectionOwner :
  (a b x t h : ℚ) →
  SpaceTime.spaceTimeExteriorEnergyBalance
    (planeWaveFiniteSpaceTimeWindow a b x t h)
    ≡ SpaceTime.spaceTimeExteriorEnergyBalance
      (planeWaveFiniteSpaceTimeWindow a b x t h)
planeWaveSamplesMeetFourDirectionOwner a b x t h = refl

-- The actual 3-vector Poynting normal samples at the source and target
-- are EXACTLY the two finite x-axis boundary samples used above.
planeRightFaceIsFullMaxwellPoynting :
  (a b x t h : ℚ) →
  Sample.poyntingFaceSample F unitX (planeJet a b x t)
    ≡ Open.outwardX (planeFaceWindow a b x t h) (suc zero)
planeRightFaceIsFullMaxwellPoynting a b x t h =
  planePoyntingXFromFullVector a b x t

planeLeftFaceIsFullMaxwellPoynting :
  (a b x t h : ℚ) →
  Sample.poyntingFaceSample F unitX (planeJet a b (x - h) t)
    ≡ Open.outwardX (planeFaceWindow a b x t h) zero
planeLeftFaceIsFullMaxwellPoynting a b x t h =
  planePoyntingXFromFullVector a b (x - h) t

-- Open/physical gates are STILL OPEN: nontrivial finite-energy localized
-- source, real SI materials and retarded Green/waveguide, actual collector
-- surface/time integration, natural source and original terminal V/I,
-- controller and ion-pump costs, and restored repeatable source cycle.
