module DASHI.Physics.QFT.NeutrinoHornedC3RephasingNoGoExact where

------------------------------------------------------------------------
-- MAX-CUT PHYSICAL DISCRIMINATOR: Ad_T ORBIT != DISTINCT LEPTON
-- OSCILLATION PHYSICS.
--
-- Original authority: Cecilia Jarlskog (1985/1987), rephasing
-- invariants; PDG neutrino-mixing conventions; standard charged-
-- lepton field basis freedom in the weak charged current.
--
-- Existing owners:
-- NeutrinoExistingCPSectorLeptonBridgeExact.pmns, neutralMassSquared
-- NeutrinoHornedSU3RootExact.phaseT and C3 inner conjugation.
-- C3CyclotomicAmplitudeAlgebraExact for EXACT Q(zeta3) products,
-- conjugation and norm (not a newly invented complex field).
--
-- The charged-phase C3 generator T=diag(1,zeta,zeta²) moves the
-- displayed matrix entries and yields a three-point algebraic orbit.
-- BUT U' = T U is charged-lepton ROW REPHASING. Observable
-- oscillation quartets and transition PROBABILITIES are invariant.
--
-- Explicit here: nine exact |U'_{ai}|²=|U_{ai}|², exact CP-odd
-- rephasing quartet equality and nine covariant neutral Hamiltonian
-- entries H'_{ab}=T_a H_{ab} conj(T_b).
--
-- These are CLOSED ARITHMETIC witness clauses for the selected
-- post-hoc PMNS toy, not a physical PMNS prediction. Source-written
-- Agda; no Agda kernel was executed in the available runtime.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ)
open import Data.Rational.Tactic.RingSolver using (solve)

import DASHI.Moonshine.C3CyclotomicAmplitudeAlgebraExact as C
import DASHI.Moonshine.Monster3BCyclotomicLinearAlgebraExact as L
import DASHI.Physics.QFT.NeutrinoThreeFlavourFiniteExact as N
import DASHI.Physics.QFT.NeutrinoExistingCPSectorLeptonBridgeExact as CP
import DASHI.Physics.QFT.NeutrinoHornedSU3RootExact as Root

open N using
  (Flavour; electron; muon; tau; MassBasis; mass1; mass2; mass3)

rephasedPMNS : Flavour → MassBasis → C.Cyclotomic3
rephasedPMNS a i =
  C.multiply (Root.phaseT a) (CP.pmns a i)

bornOriginal : Flavour → MassBasis → ℚ
bornOriginal a i = C.norm (CP.pmns a i)

bornRephased : Flavour → MassBasis → ℚ
bornRephased a i = C.norm (rephasedPMNS a i)

rephasingPreservesNineBornEntries :
  (a : Flavour) (i : MassBasis) →
  bornRephased a i ≡ bornOriginal a i
rephasingPreservesNineBornEntries electron mass1 = solve []
rephasingPreservesNineBornEntries electron mass2 = solve []
rephasingPreservesNineBornEntries electron mass3 = solve []
rephasingPreservesNineBornEntries muon mass1 = solve []
rephasingPreservesNineBornEntries muon mass2 = solve []
rephasingPreservesNineBornEntries muon mass3 = solve []
rephasingPreservesNineBornEntries tau mass1 = solve []
rephasingPreservesNineBornEntries tau mass2 = solve []
rephasingPreservesNineBornEntries tau mass3 = solve []

rephasedQuartet : C.Cyclotomic3
rephasedQuartet =
  C.multiply
    (C.multiply
      (C.multiply
        (rephasedPMNS electron mass1)
        (rephasedPMNS muon mass2))
      (C.conjugate (rephasedPMNS electron mass2)))
    (C.conjugate (rephasedPMNS muon mass1))

jarlskogQuartetInvariantUnderThreefoldRowRephasing :
  rephasedQuartet ≡ CP.quartet
jarlskogQuartetInvariantUnderThreefoldRowRephasing =
  C.cyclotomic3Ext (solve []) (solve [])

rephasedMassSquared : Flavour → Flavour → C.Cyclotomic3
rephasedMassSquared a b =
  Root.sum3
    (L.scale (CP.massEigenvalue mass1)
      (C.multiply (rephasedPMNS a mass1)
        (C.conjugate (rephasedPMNS b mass1))))
    (L.scale (CP.massEigenvalue mass2)
      (C.multiply (rephasedPMNS a mass2)
        (C.conjugate (rephasedPMNS b mass2))))
    (L.scale (CP.massEigenvalue mass3)
      (C.multiply (rephasedPMNS a mass3)
        (C.conjugate (rephasedPMNS b mass3))))

basisConjugatedMassSquared : Flavour → Flavour → C.Cyclotomic3
basisConjugatedMassSquared a b =
  C.multiply
    (C.multiply (Root.phaseT a) (CP.neutralMassSquared a b))
    (C.conjugate (Root.phaseT b))

sameMassSquaredUpToChargedLeptonRephasing :
  (a b : Flavour) →
  rephasedMassSquared a b ≡ basisConjugatedMassSquared a b
sameMassSquaredUpToChargedLeptonRephasing electron electron = C.cyclotomic3Ext (solve []) (solve [])
sameMassSquaredUpToChargedLeptonRephasing electron muon = C.cyclotomic3Ext (solve []) (solve [])
sameMassSquaredUpToChargedLeptonRephasing electron tau = C.cyclotomic3Ext (solve []) (solve [])
sameMassSquaredUpToChargedLeptonRephasing muon electron = C.cyclotomic3Ext (solve []) (solve [])
sameMassSquaredUpToChargedLeptonRephasing muon muon = C.cyclotomic3Ext (solve []) (solve [])
sameMassSquaredUpToChargedLeptonRephasing muon tau = C.cyclotomic3Ext (solve []) (solve [])
sameMassSquaredUpToChargedLeptonRephasing tau electron = C.cyclotomic3Ext (solve []) (solve [])
sameMassSquaredUpToChargedLeptonRephasing tau muon = C.cyclotomic3Ext (solve []) (solve [])
sameMassSquaredUpToChargedLeptonRephasing tau tau = C.cyclotomic3Ext (solve []) (solve [])

-- The nonzero Ad_T(A)-A result in Root concerns a *matrix orbit*.
-- It does NOT show distinct measured neutrino families, values of
-- Jarlskog J, cross sections, or PMNS oscillation probabilities.
-- The simultaneous row-basis rotation changes the Hamiltonian
-- entries covariantly and leaves basis-invariant observables intact.
--
-- To recover a physical C3 effect, an additional fixed reference
-- interaction/source/measurement must break this rephasing
-- redundancy. No such same-object source has been supplied.

------------------------------------------------------------------------
-- CHARACTER/WILSON-TRACE BOUNDARY.
-- If rho(r(g))=T rho(g) T^-1, then for any horn group word g,
-- tr rho(r(g)) = tr rho(g).  This is the standard invariance
-- of characters under inner conjugation, NOT a claim of zero
-- source holonomy.  Closed source-specific equalities below audit
-- the selected CP matrix rather than asserting an unimported
-- universal finite-matrix trace theorem.
------------------------------------------------------------------------

traceRootMatrix :
  (Flavour → Flavour → C.Cyclotomic3) → C.Cyclotomic3
traceRootMatrix M =
  Root.sum3 (M electron electron) (M muon muon) (M tau tau)

onceRotatedRoot : Flavour → Flavour → C.Cyclotomic3
onceRotatedRoot = Root.rotateByChargedT Root.selectedTS

twiceRotatedRoot : Flavour → Flavour → C.Cyclotomic3
twiceRotatedRoot = Root.rotateByChargedT onceRotatedRoot

rootCharacterUnchangedUnderFirstRotation :
  traceRootMatrix onceRotatedRoot
    ≡ traceRootMatrix Root.selectedTS
rootCharacterUnchangedUnderFirstRotation =
  C.cyclotomic3Ext (solve []) (solve [])

rootCharacterUnchangedUnderSecondRotation :
  traceRootMatrix twiceRotatedRoot
    ≡ traceRootMatrix onceRotatedRoot
rootCharacterUnchangedUnderSecondRotation =
  C.cyclotomic3Ext (solve []) (solve [])

-- The earlier exact proof
-- Root.chargedRotationActuallyMovesCPRoot
-- and these trace equalities are consistent:
-- nontrivial matrix orbit != nontrivial class-function observable.
