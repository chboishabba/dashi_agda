module DASHI.Physics.QFT.NeutrinoExistingCPSectorLeptonBridgeExact where

------------------------------------------------------------------------
-- REUSE existing exact cyclotomic complex phase / CKM Jarlskog donors.
-- Do NOT confuse the CKM quark phase and leptonic PMNS phase.
--
-- ORIGINAL SCHOLARLY ROOTS:
--   C. Jarlskog, PRL 55 (1985) 1039, DOI 10.1103/PhysRevLett.55.1039
--   C. Jarlskog, PRD 35 (1987) 1685, DOI 10.1103/PhysRevD.35.1685
--   PDG, 2025 Review of Particle Physics, Neutrino Masses, Mixing,
--     and Oscillations (Jarlskog invariant, rephasing convention)
--   NuFIT 6.1 (2025), global fit, www.nu-fit.org
--
-- EXISTING DASHI SOURCE ROOTS:
--   C3CyclotomicAmplitudeAlgebraExact: Q(zeta3) exact multiplication,
--     conjugation, norm, and third-root phase values.
--   Monster3BCyclotomicLinearAlgebraExact: addition, rational scaling.
--   CPPhaseStructuralOriginReceipt / HeckeCharacterPhaseReceipt /
--   Y13ComplexEntryReceipt / JarlskogDiagnosticAnalysis:
--     CKM CP *candidates/diagnostics* only, physical promotion FALSE.
--   CKMGateAbRetirementReceipt: pure CM angle retired as CKM prediction.
--   NeutrinoSameLeptonMassOperatorRationalExact: earlier REAL matrix
--     donor, whose vanishing CP invariant is a model limitation.
--
-- NEW DASHI mathematical contribution:
-- Instantiate a *different* complex, CP-nontrivial lepton-sector
-- U=R23 R13(delta) R12 with phase exp(+i delta)=zeta3, delta=120deg.
-- Rational sin/cos inputs are deliberately post hoc and unchanged
-- from the earlier REAL rational mixing-matrix reconstruction.
-- Prove exact unitary Gram, mass-squared eigenbasis, and a nonzero
-- phase-sensitive Jarlskog coefficient in Q(zeta3).
--
-- THIS IS NOT A FIRST-PRINCIPLES DERIVATION OF LEPTONIC DELTA_CP.
-- No experimental NuFIT likelihood, charged current, gauge-invariant
-- Yukawa mechanism or Majorana/Dirac distinction is asserted.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Bool using (false; true)
open import Data.Empty using (⊥)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_; -_; normalize)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Agda.Builtin.List using ([]; _∷_)

import DASHI.Moonshine.C3CyclotomicAmplitudeAlgebraExact as Q3
import DASHI.Moonshine.Monster3BCyclotomicLinearAlgebraExact as Lin
import DASHI.Physics.QFT.NeutrinoThreeFlavourFiniteExact as Three
import DASHI.Physics.Closure.JarlskogDiagnosticAnalysis as CKMJ
import DASHI.Physics.Closure.HeckeCharacterPhaseReceipt as CKMHecke
import DASHI.Physics.Closure.CKMGateAbRetirementReceipt as CKMRetirement
import DASHI.Physics.Closure.Y13ComplexEntryReceipt as CKMY13

open Three using
  (Flavour; electron; muon; tau; MassBasis; mass1; mass2; mass3)

-- Rational Pythagorean pairs, chosen to approximate published
-- three-flavour oscillation angles, not implied by the third root.
s12 c12 s13 c13 s23 c23 : ℚ
s12 = normalize 161 289
c12 = normalize 240 289
s13 = normalize 240 1609
c13 = normalize 1591 1609
s23 = normalize 20 29
c23 = normalize 21 29

add : Q3.Cyclotomic3 → Q3.Cyclotomic3 → Q3.Cyclotomic3
add = Lin.add

scale : ℚ → Q3.Cyclotomic3 → Q3.Cyclotomic3
scale = Lin.scale

real : ℚ → Q3.Cyclotomic3
real = Q3.embedRational

negC : Q3.Cyclotomic3 → Q3.Cyclotomic3
negC = Lin.negate

mul : Q3.Cyclotomic3 → Q3.Cyclotomic3 → Q3.Cyclotomic3
mul = Q3.multiply

conj : Q3.Cyclotomic3 → Q3.Cyclotomic3
conj = Q3.conjugate

-- PDG parameterization with exp(+i δ)=zeta3 and
-- exp(-i δ)=zeta3Squared in U_e3.
pmns : Flavour → MassBasis → Q3.Cyclotomic3
pmns electron mass1 = real (c12 * c13)
pmns electron mass2 = real (s12 * c13)
pmns electron mass3 = scale s13 Q3.zetaSquared
pmns muon mass1 =
  add (real (- (s12 * c23))) (scale (- (c12 * s23 * s13)) Q3.zeta)
pmns muon mass2 =
  add (real (c12 * c23)) (scale (- (s12 * s23 * s13)) Q3.zeta)
pmns muon mass3 = real (s23 * c13)
pmns tau mass1 =
  add (real (s12 * s23)) (scale (- (c12 * c23 * s13)) Q3.zeta)
pmns tau mass2 =
  add (real (- (c12 * s23))) (scale (- (s12 * c23 * s13)) Q3.zeta)
pmns tau mass3 = real (c23 * c13)

sum3 : Q3.Cyclotomic3 → Q3.Cyclotomic3 → Q3.Cyclotomic3 →
  Q3.Cyclotomic3
sum3 a b c = add a (add b c)

rowGram : Flavour → Flavour → Q3.Cyclotomic3
rowGram a b =
  sum3
    (mul (pmns a mass1) (conj (pmns b mass1)))
    (mul (pmns a mass2) (conj (pmns b mass2)))
    (mul (pmns a mass3) (conj (pmns b mass3)))

colGram : MassBasis → MassBasis → Q3.Cyclotomic3
colGram i j =
  sum3
    (mul (conj (pmns electron i)) (pmns electron j))
    (mul (conj (pmns muon i)) (pmns muon j))
    (mul (conj (pmns tau i)) (pmns tau j))

flavourDelta : Flavour → Flavour → Q3.Cyclotomic3
flavourDelta electron electron = Q3.one
flavourDelta muon muon = Q3.one
flavourDelta tau tau = Q3.one
flavourDelta _ _ = Q3.zero

massDelta : MassBasis → MassBasis → Q3.Cyclotomic3
massDelta mass1 mass1 = Q3.one
massDelta mass2 mass2 = Q3.one
massDelta mass3 mass3 = Q3.one
massDelta _ _ = Q3.zero

-- Nine concrete calculations on the ACTUAL cyclotomic scalar owner.
pmnsUnitaryRows : (a b : Flavour) →
  rowGram a b ≡ flavourDelta a b
pmnsUnitaryRows electron electron = Q3.cyclotomic3Ext (solve []) (solve [])
pmnsUnitaryRows electron muon = Q3.cyclotomic3Ext (solve []) (solve [])
pmnsUnitaryRows electron tau = Q3.cyclotomic3Ext (solve []) (solve [])
pmnsUnitaryRows muon electron = Q3.cyclotomic3Ext (solve []) (solve [])
pmnsUnitaryRows muon muon = Q3.cyclotomic3Ext (solve []) (solve [])
pmnsUnitaryRows muon tau = Q3.cyclotomic3Ext (solve []) (solve [])
pmnsUnitaryRows tau electron = Q3.cyclotomic3Ext (solve []) (solve [])
pmnsUnitaryRows tau muon = Q3.cyclotomic3Ext (solve []) (solve [])
pmnsUnitaryRows tau tau = Q3.cyclotomic3Ext (solve []) (solve [])

pmnsUnitaryCols : (i j : MassBasis) →
  colGram i j ≡ massDelta i j
pmnsUnitaryCols mass1 mass1 = Q3.cyclotomic3Ext (solve []) (solve [])
pmnsUnitaryCols mass1 mass2 = Q3.cyclotomic3Ext (solve []) (solve [])
pmnsUnitaryCols mass1 mass3 = Q3.cyclotomic3Ext (solve []) (solve [])
pmnsUnitaryCols mass2 mass1 = Q3.cyclotomic3Ext (solve []) (solve [])
pmnsUnitaryCols mass2 mass2 = Q3.cyclotomic3Ext (solve []) (solve [])
pmnsUnitaryCols mass2 mass3 = Q3.cyclotomic3Ext (solve []) (solve [])
pmnsUnitaryCols mass3 mass1 = Q3.cyclotomic3Ext (solve []) (solve [])
pmnsUnitaryCols mass3 mass2 = Q3.cyclotomic3Ext (solve []) (solve [])
pmnsUnitaryCols mass3 mass3 = Q3.cyclotomic3Ext (solve []) (solve [])

-- All three eigenvalue differences are external NuFIT normal-ordering
-- empirical inputs, scaled as integer multiples of 10^-8 eV².
massEigenvalue : MassBasis → ℚ
massEigenvalue mass1 = 0ℚ
massEigenvalue mass2 = normalize 7537 1
massEigenvalue mass3 = normalize 251100 1

neutralMassSquared : Flavour → Flavour → Q3.Cyclotomic3
neutralMassSquared a b =
  sum3
    (scale (massEigenvalue mass1)
      (mul (pmns a mass1) (conj (pmns b mass1))))
    (scale (massEigenvalue mass2)
      (mul (pmns a mass2) (conj (pmns b mass2))))
    (scale (massEigenvalue mass3)
      (mul (pmns a mass3) (conj (pmns b mass3))))

applyNeutralMass : Flavour → MassBasis → Q3.Cyclotomic3
applyNeutralMass a i =
  sum3
    (mul (neutralMassSquared a electron) (pmns electron i))
    (mul (neutralMassSquared a muon) (pmns muon i))
    (mul (neutralMassSquared a tau) (pmns tau i))

-- A complex Hermitian, not real symmetric, mass-squared operator.
neutralMassEigenEquation : (a : Flavour) (i : MassBasis) →
  applyNeutralMass a i ≡ scale (massEigenvalue i) (pmns a i)
neutralMassEigenEquation electron mass1 = Q3.cyclotomic3Ext (solve []) (solve [])
neutralMassEigenEquation electron mass2 = Q3.cyclotomic3Ext (solve []) (solve [])
neutralMassEigenEquation electron mass3 = Q3.cyclotomic3Ext (solve []) (solve [])
neutralMassEigenEquation muon mass1 = Q3.cyclotomic3Ext (solve []) (solve [])
neutralMassEigenEquation muon mass2 = Q3.cyclotomic3Ext (solve []) (solve [])
neutralMassEigenEquation muon mass3 = Q3.cyclotomic3Ext (solve []) (solve [])
neutralMassEigenEquation tau mass1 = Q3.cyclotomic3Ext (solve []) (solve [])
neutralMassEigenEquation tau mass2 = Q3.cyclotomic3Ext (solve []) (solve [])
neutralMassEigenEquation tau mass3 = Q3.cyclotomic3Ext (solve []) (solve [])

-- Convention-independent leptonic quartet:
-- J = Im(U_e1 U_mu2 conjugate(U_e2) conjugate(U_mu1)).
-- We capture the exact cyclotomic zeta coefficient; the actual
-- physical complex imaginary part is (sqrt(3)/2) times it.
quartet : Q3.Cyclotomic3
quartet =
  mul
    (mul
      (mul (pmns electron mass1) (pmns muon mass2))
      (conj (pmns electron mass2)))
    (conj (pmns muon mass1))

cpOddCoefficient : ℚ
cpOddCoefficient = normalize 9859116742272000 292590225473523169

quartetZetaCoefficientExact :
  Q3.zetaCoeff quartet ≡ cpOddCoefficient
quartetZetaCoefficientExact = solve []

-- Explicit nonzero witness: the exact rational is positive, and
-- no equality to zero can be constructed (distinct reduced numerators).
quartetZetaCoefficientNotZero :
  Q3.zetaCoeff quartet ≡ 0ℚ → ⊥
quartetZetaCoefficientNotZero ()

-- Complex conjugation negates this coefficient, which demonstrates
-- sensitivity to CP conjugation on the SAME flavour operator.
quartetCPConjugateZetaCoefficientExact :
  Q3.zetaCoeff (conj quartet) ≡ - cpOddCoefficient
quartetCPConjugateZetaCoefficientExact = solve []

-- Quark CKM donors are retained at their actual evidence grade.
-- The fact that a CKM phase exists does not make it a PMNS angle.
ckmJarlskogDiagnosticDoesNotPromotePhysicalCP :
  CKMJ.physicalCPDerived
    CKMJ.canonicalJarlskogDiagnosticAnalysisReceipt ≡ false
ckmJarlskogDiagnosticDoesNotPromotePhysicalCP = refl

ckmHeckePhaseDoesNotPromotePhysicalCP :
  CKMHecke.physicalCPPhaseDerived
    CKMHecke.canonicalHeckeCharacterPhaseReceipt ≡ false
ckmHeckePhaseDoesNotPromotePhysicalCP = refl

ckmPureCMGammaWasRetired :
  CKMRetirement.formulaRetiredAsPrediction
    CKMRetirement.canonicalCKMGateAbRetirementReceipt
    ≡ true
ckmPureCMGammaWasRetired = refl

ckmComplexY13DoesNotPromotePhysicalCKM :
  CKMY13.physicalCKMPromoted
    CKMY13.canonicalY13ComplexEntryReceipt ≡ false
ckmComplexY13DoesNotPromotePhysicalCKM = refl

-- A nonzero finite model CP invariant is mathematical existence,
-- NOT a measured leptonic CP phase, a phase prediction from ζ alone,
-- an actual Dirac/Majorana mass mechanism or a CKM/PMNS identification.
data PhysicalLeptonicCPPromotion : Set where

physicalLeptonicCPPromotionStillBlocked :
  PhysicalLeptonicCPPromotion → ⊥
physicalLeptonicCPPromotionStillBlocked ()
