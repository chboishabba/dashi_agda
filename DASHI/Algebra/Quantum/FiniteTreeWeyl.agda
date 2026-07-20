module DASHI.Algebra.Quantum.FiniteTreeWeyl where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Agda.Builtin.String using (String)

open import DASHI.Unified.GRQuantumProofTerms using (⊥; WaveLiftCCRProof)

------------------------------------------------------------------------
-- Exact finite qutrit/cylinder algebra.
--
-- The finite theorem is a Weyl-style shift/phase relation.  It is deliberately
-- not mislabeled as an exact finite-dimensional Heisenberg CCR: the continuum
-- CCR requires a separate scaling-limit proof.


data Qutrit : Set where
  q0 q1 q2 : Qutrit


data Phase3 : Set where
  p0 p1 p2 : Phase3

phaseAdd : Phase3 → Phase3 → Phase3
phaseAdd p0 right = right
phaseAdd p1 p0 = p1
phaseAdd p1 p1 = p2
phaseAdd p1 p2 = p0
phaseAdd p2 p0 = p2
phaseAdd p2 p1 = p0
phaseAdd p2 p2 = p1

shift : Qutrit → Qutrit
shift q0 = q1
shift q1 = q2
shift q2 = q0

phaseOf : Qutrit → Phase3
phaseOf q0 = p0
phaseOf q1 = p1
phaseOf q2 = p2

finiteWeylShiftLaw :
  (q : Qutrit) →
  phaseOf (shift q) ≡ phaseAdd p1 (phaseOf q)
finiteWeylShiftLaw q0 = refl
finiteWeylShiftLaw q1 = refl
finiteWeylShiftLaw q2 = refl

shiftThreeIsIdentity : (q : Qutrit) → shift (shift (shift q)) ≡ q
shiftThreeIsIdentity q0 = refl
shiftThreeIsIdentity q1 = refl
shiftThreeIsIdentity q2 = refl

------------------------------------------------------------------------
-- Finite-depth cylinders and the exact project/refine section law.

Cylinder : Set
Cylinder = List Qutrit

refine : Cylinder → Cylinder
refine cylinder = q0 ∷ cylinder

project : Cylinder → Cylinder
project [] = []
project (_ ∷ rest) = rest

projectRefine : (cylinder : Cylinder) → project (refine cylinder) ≡ cylinder
projectRefine cylinder = refl

q0≢q1 : q0 ≡ q1 → ⊥
q0≢q1 ()

refineProjectNotIdentityAtQ1 :
  refine (project (q1 ∷ [])) ≡ (q1 ∷ []) → ⊥
refineProjectNotIdentityAtQ1 ()

-- The section/retraction asymmetry is the exact finite noncommutativity source:
-- project ∘ refine = id, but refine ∘ project is not id on arbitrary cylinders.
record TreeShiftReceipt : Set where
  constructor tree-shift-receipt
  field
    projectRefineReceipt :
      (cylinder : Cylinder) → project (refine cylinder) ≡ cylinder
    refinementProjectionMismatchWitness :
      refine (project (q1 ∷ [])) ≡ (q1 ∷ []) → ⊥
    finiteWeylReceipt :
      (q : Qutrit) →
      phaseOf (shift q) ≡ phaseAdd p1 (phaseOf q)
open TreeShiftReceipt public

canonicalTreeShiftReceipt : TreeShiftReceipt
canonicalTreeShiftReceipt =
  tree-shift-receipt
    projectRefine
    refineProjectNotIdentityAtQ1
    finiteWeylShiftLaw

------------------------------------------------------------------------
-- Exact finite Born-style norm on one-hot qutrit amplitudes.

Amplitude : Set
Amplitude = Qutrit → Nat

basisAmplitude : Qutrit → Amplitude
basisAmplitude q0 q0 = 1
basisAmplitude q0 q1 = 0
basisAmplitude q0 q2 = 0
basisAmplitude q1 q0 = 0
basisAmplitude q1 q1 = 1
basisAmplitude q1 q2 = 0
basisAmplitude q2 q0 = 0
basisAmplitude q2 q1 = 0
basisAmplitude q2 q2 = 1

normSquared : Amplitude → Nat
normSquared amplitude =
  amplitude q0 * amplitude q0 +
  amplitude q1 * amplitude q1 +
  amplitude q2 * amplitude q2

basisNormSquaredIsOne :
  (q : Qutrit) → normSquared (basisAmplitude q) ≡ 1
basisNormSquaredIsOne q0 = refl
basisNormSquaredIsOne q1 = refl
basisNormSquaredIsOne q2 = refl

bornWeight : Amplitude → Qutrit → Nat
bornWeight amplitude q = amplitude q * amplitude q

basisBornWeightAtSelfIsOne :
  (q : Qutrit) → bornWeight (basisAmplitude q) q ≡ 1
basisBornWeightAtSelfIsOne q0 = refl
basisBornWeightAtSelfIsOne q1 = refl
basisBornWeightAtSelfIsOne q2 = refl

record FiniteBornReceipt : Set where
  constructor finite-born-receipt
  field
    basisNormalization :
      (q : Qutrit) → normSquared (basisAmplitude q) ≡ 1
    selfOutcomeWeight :
      (q : Qutrit) → bornWeight (basisAmplitude q) q ≡ 1
open FiniteBornReceipt public

canonicalFiniteBornReceipt : FiniteBornReceipt
canonicalFiniteBornReceipt =
  finite-born-receipt basisNormSquaredIsOne basisBornWeightAtSelfIsOne

------------------------------------------------------------------------
-- Continuum completion target.  A producer must supply this proof payload;
-- finite Weyl noncommutativity alone does not synthesize [X,P] = i hbar.

record TreeToContinuumCCR : Set₁ where
  field
    finiteTreeReceipt : TreeShiftReceipt
    finiteBornReceipt : FiniteBornReceipt
    scalingFamily : Set
    operatorTopology : Set
    continuumLimitExists : Set
    limitingCommutatorIsCentral : Set
    heisenbergCCR : Set
    waveLiftProof : WaveLiftCCRProof
open TreeToContinuumCCR public

finiteCCRBoundaryText : String
finiteCCRBoundaryText =
  "The finite qutrit tree proves a project/refine asymmetry and an exact Weyl shift law.  Exact Heisenberg CCR, Hilbert completion, and the value of hbar remain proposition-valued continuum-limit obligations."
