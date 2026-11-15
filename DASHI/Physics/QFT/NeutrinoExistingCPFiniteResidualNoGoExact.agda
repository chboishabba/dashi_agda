module DASHI.Physics.QFT.NeutrinoExistingCPFiniteResidualNoGoExact where

------------------------------------------------------------------------
-- CP-NONZERO / FINITE-FLAVOUR-GROUP COUNTEREXAMPLE.
--
-- ORIGINAL:
-- C. Jarlskog 1985 and 1987, CP invariants in flavour mass matrices.
-- R. M. Fonseca and W. Grimus, JHEP 09 (2014) 033, finite residual
-- symmetries in Majorana-neutrino models.
-- Standard algebraic number theory: trace of finite-order matrix
-- algebraic integer; relative trace from Q(zeta) to Q integral.
--
-- REUSED SOURCE OWNERS:
-- NeutrinoExistingCPSectorLeptonBridgeExact -- U at δ=+120deg.
-- C3CyclotomicAmplitudeAlgebraExact -- Q(zeta), trace, conjugation.
-- Monster3BCyclotomicLinearAlgebraExact -- phase addition/scale.
-- NeutrinoSameLeptonMassOperatorRationalExact -- older CP-even no-go.
--
-- NEW RESULT:
-- For this CP-nonzero complex U, the charged-lepton residual is still
-- T=diag(1,zeta,zeta²), and the neutrino residual is
-- S1=U diag(1,-1,-1) U†=2|u1><u1|-I.
-- Exact Q(zeta) field trace of tr(T*S1) is a rational in (2,3),
-- so by standard external algebraic-integrality theorems TS1
-- has infinite order.  CP violation does NOT repair the finite-group
-- obstruction for this selected post-hoc rational mixing family.
-- No universal impossibility for all complex finite flavour groups.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Bool using (false)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_; -_; normalize)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Nat using (_≤ᵇ_)
open import Data.Empty using (⊥)

import DASHI.Moonshine.C3CyclotomicAmplitudeAlgebraExact as Q3
import DASHI.Moonshine.Monster3BCyclotomicLinearAlgebraExact as L
import DASHI.Physics.QFT.NeutrinoExistingCPSectorLeptonBridgeExact as CP
import DASHI.Physics.QFT.NeutrinoThreeFlavourFiniteExact as N

two : ℚ
two = 1ℚ + 1ℚ

-- S1 = 2 u1 u1† - I, computed on the same lepton space.
s1Diagonal : N.Flavour → ℚ
s1Diagonal a =
  two * Q3.norm (CP.pmns a N.mass1) - 1ℚ

chargedC3TimesNeutralTrace : Q3.Cyclotomic3
chargedC3TimesNeutralTrace =
  L.add (Q3.embedRational (s1Diagonal N.electron))
    (L.add (L.scale (s1Diagonal N.muon) Q3.zeta)
           (L.scale (s1Diagonal N.tau) Q3.zetaSquared))

traceField : ℚ
traceField = Q3.trace chargedC3TimesNeutralTrace

-- Because tr(S1)=-1, Tr_{Q(zeta)/Q}(tr(TS1))
--   = 3 S1_ee - tr(S1) = 6 |U_e1|² - 2.
-- Depends only on first row of U, not the CP phase.
sourceIndependentTraceFormula :
  traceField ≡
    (normalize 6 1) * Q3.norm (CP.pmns N.electron N.mass1)
      - (normalize 2 1)
sourceIndependentTraceFormula = solve []

sameGaloisTraceAsCPConservingExample :
  traceField ≡ normalize 442358853598 216225930001
sameGaloisTraceAsCPConservingExample = solve []

-- Independent natural-number inequalities bound it strictly
-- between 2 and 3; the integer gap is an exact certificate.
traceExceedsTwo :
  (442358853598 ≤ᵇ 432451860002) ≡ false
traceExceedsTwo = refl

traceBelowThree :
  (648677790003 ≤ᵇ 442358853598) ≡ false
traceBelowThree = refl

cpPhaseStillNonzero :
  Q3.zetaCoeff CP.quartet ≡
    normalize 9859116742272000 292590225473523169
cpPhaseStillNonzero = CP.quartetZetaCoefficientExact

-- To conclude "TS1 infinite order" FROM THE ABOVE, one must import
-- and type-check the following STANDARD number-theory implication:
-- finite-order TS1 => algebraic-integer trace =>
-- relative Galois trace in Z.  No phantom constructor/witness
-- pretends that general theorem has been kernel proved here.

data FiniteFlavourGroupProof : Set where

finiteFlavourGroupStillNotConstructed :
  FiniteFlavourGroupProof → ⊥
finiteFlavourGroupStillNotConstructed ()
