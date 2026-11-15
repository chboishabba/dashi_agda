module DASHI.Physics.QFT.NeutrinoHornedWilsonInterferenceExact where

------------------------------------------------------------------------
-- Source-specific exact Wilson-loop CHARACTER and two-arm
-- interference fixture, NOT an observed neutrino/AB signal.
--
-- Original physics: Aharonov--Bohm 1959, Yang-Mills Wilson loop;
-- non-Abelian Wilson loop experiments: Chen et al., Nature Commun
-- 10, 3125 (2019); Sugawa et al., npj Quantum Inf 7, 144 (2021).
-- Original DASHI:
-- SUNWilsonClassFunction.sunWilsonLoopGaugeInvariant (canonical
-- class-function owner, gauge invariant subject to trace authority);
-- NeutrinoHornedSU3RootExact.selectedTS (the chosen SU3 root);
-- NeutrinoHornedC3RephasingNoGoExact (C3 conjugation does NOT
-- create an independent Wilson-loop observable).
--
-- New exact computation:
--  W=TS1; tr W = (176093404722400 -
--                 19836986431118*zeta) / 181846007130841.
--  For an UNPOLARIZED abstract three-component fundamental
--  two-path interferometer with unit path transports (I,W)
--  and controlled relative path phase phi=0,
--    P_samePort = (1/2)(1+ReTr(W)/3)
--               = 434928608401/648677790003.
--  This is a conditional MODEL PREDICTION for the selected,
--  POST-HOC W only. No detector, physical lepton SU3 gauge
--  current, physically fixed path or gauge dynamical action.
--
-- Gauge transforms conjugate W at the loop basepoint;
-- trace is unchanged.  Source-group threefold rotation acts
-- by conjugation, hence cannot create three different P.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ; _+_; _*_; _-_; normalize)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Empty using (⊥)

import DASHI.Moonshine.C3CyclotomicAmplitudeAlgebraExact as C
import DASHI.Physics.QFT.NeutrinoHornedSU3RootExact as Root
import DASHI.Physics.QFT.NeutrinoHornedC3RephasingNoGoExact as CP
import DASHI.Physics.YangMills.SUNWilsonClassFunction as Wilson

selectedWilsonCharacter : C.Cyclotomic3
selectedWilsonCharacter =
  CP.traceRootMatrix Root.selectedTS

selectedWilsonRationalCoeff :
  C.rationalCoeff selectedWilsonCharacter
    ≡ normalize 176093404722400 181846007130841
selectedWilsonRationalCoeff = solve []

selectedWilsonZetaCoeff :
  C.zetaCoeff selectedWilsonCharacter
    ≡ normalize 0 1 -
       normalize 19836986431118 181846007130841
selectedWilsonZetaCoeff = solve []

-- Quadratic field trace equals twice the ordinary-complex REAL part
-- after ζ=-1/2+i√3/2.  No complex sqrt(3) authority is invented.
selectedWilsonDoubleComplexReal :
  C.trace selectedWilsonCharacter
    ≡ normalize 372023795875918 181846007130841
selectedWilsonDoubleComplexReal = solve []

-- P(phi=0) = 1/2 + fieldTrace(tr W)/12.
unpolarizedTwoArmPort0 : ℚ
unpolarizedTwoArmPort0 =
  normalize 1 2
  + (normalize 1 12 * C.trace selectedWilsonCharacter)

unpolarizedPort0Exact :
  unpolarizedTwoArmPort0 ≡
    normalize 434928608401 648677790003
unpolarizedPort0Exact = solve []

selectedWilsonNotTrivial :
  selectedWilsonCharacter ≡
    C.embedRational (normalize 3 1) → ⊥
selectedWilsonNotTrivial ()

rootWilsonC3OrbitCharacterEqual :
  CP.traceRootMatrix CP.onceRotatedRoot
    ≡ selectedWilsonCharacter
rootWilsonC3OrbitCharacterEqual =
  CP.rootCharacterUnchangedUnderFirstRotation

-- Existing Wilson theorem consumer:
-- Wilson.sunWilsonLoopGaugeInvariant is the canonical generic proof
-- for ANY closed path once the literal SU3 matrix carrier and trace
-- authority have been instantiated. We do not copy or replace it.
-- The current 3x3 rational fixture is not proof that an actual
-- Hatcher loop in a specific smooth 3-manifold has this holonomy.
