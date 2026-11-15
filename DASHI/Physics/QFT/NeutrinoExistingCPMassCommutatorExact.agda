module DASHI.Physics.QFT.NeutrinoExistingCPMassCommutatorExact where

------------------------------------------------------------------------
-- SAME-SPACE CP-ODD COMMUTATOR: EXACT CYCL0TOMIC NUMERICAL WITNESS
--
-- ORIGINAL: Cecilia Jarlskog, PRL 55 (1985) 1039 and
--           PRD 35 (1987) 1685, basis-independent CP measures.
-- EXISTING DASHI DONORS:
--   NeutrinoExistingCPSectorLeptonBridgeExact: nonzero complex PMNS J,
--     Hnu = U diag(delta-m²) U-dagger in Q(zeta3);
--   NeutrinoSameLeptonMassOperatorRationalExact: charged spectrum labels;
--   Monster3BCyclotomicLinearAlgebraExact: exact Q(zeta3) operations.
-- New: explicit charged/neutral commutator C=[H_l,H_nu],
-- and its cubic trace as a finite 3-cycle contraction.
--
-- IMPORTANT: charged masses 1,4,9 are arbitrary positive example labels,
-- not physical lepton mass inputs.  Neutrino delta m² inputs are from
-- NuFIT 6.1; charged-current model, mass hierarchy, CP phase choice
-- and global likelihood are not derived. This is algebraic CP violation
-- in a fully defined TOY model, not a discovered neutrino effect.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_; -_; normalize)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Empty using (⊥)

import DASHI.Moonshine.C3CyclotomicAmplitudeAlgebraExact as Q3
import DASHI.Moonshine.Monster3BCyclotomicLinearAlgebraExact as L
import DASHI.Physics.QFT.NeutrinoThreeFlavourFiniteExact as Base
import DASHI.Physics.QFT.NeutrinoExistingCPSectorLeptonBridgeExact as CP

open Base using (Flavour; electron; muon; tau)

chargedMassSquared : Flavour → ℚ
chargedMassSquared electron = normalize 1 1
chargedMassSquared muon = normalize 4 1
chargedMassSquared tau = normalize 9 1

-- [H_l,H_nu]_{ab} = (m_l(a)^2 - m_l(b)^2) H_nu{ab}.
-- Thus diagonal entries are 0, and trace(C^3) is the sum of
-- the two oriented 3-cycles, each appearing three times.
commutator : Flavour → Flavour → Q3.Cyclotomic3
commutator a b =
  L.scale (chargedMassSquared a - chargedMassSquared b)
    (CP.neutralMassSquared a b)

threeCycle : Flavour → Flavour → Flavour → Q3.Cyclotomic3
threeCycle a b c =
  Q3.multiply
    (Q3.multiply (commutator a b) (commutator b c))
    (commutator c a)

traceCube : Q3.Cyclotomic3
traceCube = L.scale (normalize 3 1)
  (L.add (threeCycle electron muon tau)
         (threeCycle electron tau muon))

-- Exact evaluated value in the (1,zeta) basis:
-- (u,v) = (V/2,V), where v is the rational coefficient below.
traceCubeOddCoefficient : ℚ
traceCubeOddCoefficient =
  normalize 3272103619391689547963065344000000 292590225473523169

traceCubeCoefficientExact :
  Q3.zetaCoeff traceCube ≡ traceCubeOddCoefficient
traceCubeCoefficientExact = solve []

traceCubePureImaginaryInOrdinaryComplexPlane :
  Q3.rationalCoeff traceCube + Q3.rationalCoeff traceCube
  ≡ Q3.zetaCoeff traceCube
traceCubePureImaginaryInOrdinaryComplexPlane = solve []

traceCubeNotZero :
  Q3.zetaCoeff traceCube ≡ 0ℚ → ⊥
traceCubeNotZero ()

-- The Jarlskog commutator identity in this concrete example:
--
-- Tr([Hl,Hnu]^3)_zetaCoefficient = 6 * product(Delta_l)
--                                    * product(Delta_nu)
--                                    * quartet_zetaCoefficient.
--
-- For this particular source-written example the rational factor is
-- 331886081170152000; no physical charged mass is asserted.
commutatorJarlskogFactor : ℚ
commutatorJarlskogFactor = normalize 331886081170152000 1

traceCubeFactorsThroughLeptonicJarlskog :
  Q3.zetaCoeff traceCube ≡
    commutatorJarlskogFactor * Q3.zetaCoeff CP.quartet
traceCubeFactorsThroughLeptonicJarlskog = solve []

-- CP conjugation flips the sign of the imaginary component.  This
-- witness depends on the chosen delta=+120deg phase, not the CKM
-- Hecke phase nor a measured PMNS delta.
traceCubeConjugateIsNegative :
  Q3.conjugate traceCube ≡ L.negate traceCube
traceCubeConjugateIsNegative =
  Q3.cyclotomic3Ext (solve []) (solve [])

data PhysicalCPObservationPromotion : Set where

noPhysicalObservationFromAlgebraOnly :
  PhysicalCPObservationPromotion → ⊥
noPhysicalObservationFromAlgebraOnly ()
