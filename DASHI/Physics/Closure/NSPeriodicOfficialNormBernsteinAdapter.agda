module DASHI.Physics.Closure.NSPeriodicOfficialNormBernsteinAdapter where

open import Agda.Primitive using (Level; lsuc)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import DASHI.Physics.Closure.NSCompactGammaReplenishmentAbsorption
import DASHI.Physics.Closure.NSCompactGammaConcretePotentialInstantiation as Potential
import DASHI.Physics.Closure.NSCompactGammaAnalyticLeafCompletion as Leaves
import DASHI.Physics.Closure.NSCompactGammaConcreteBernsteinEnvelopeDomain as Bernstein
import DASHI.Physics.Closure.NSPeriodicOfficialNormIdentification as Official

------------------------------------------------------------------------
-- Carrier-faithful adapter from the repository's BE1--BE8 Bernstein leaves to
-- the official periodic norm-identification surface.
--
-- All Fourier normalization, Parseval, Leray and Biot--Savart facts remain
-- explicit inputs.  The shell curl, five-halves Bernstein and vorticity
-- reconstruction fields are supplied by the existing concrete Bernstein chain,
-- not repeated as new assumptions.
------------------------------------------------------------------------

record OfficialNormBernsteinAdapterInputs
    {t : Level}
    (A : AbsorptionArithmetic)
    {Time : Set t}
    (C : Potential.ThreeWayAdditiveCalculus A)
    (R : Leaves.ConcreteReserveLeaves A Time)
    (F : Leaves.RealFundamentalTheoremRealization A C R) : Set (lsuc t) where
  field
    bernstein : Bernstein.ConcreteBernsteinEnvelopeLeaves A C R F

    coefficientL2 physicalL2 hSobolevNorm :
      Time → Bernstein.ShellState bernstein → Scalar A

    shellCoefficientL2 shellPhysicalL2 :
      Time → Nat → Bernstein.ShellState bernstein → Scalar A

    lerayInputL2 lerayOutputL2 :
      Time → Bernstein.ShellState bernstein → Scalar A

    biotSavartVorticityL2 biotSavartVelocityH1 :
      Time → Bernstein.ShellState bernstein → Scalar A

    parsevalPlancherel : ∀ τ state →
      coefficientL2 τ state ≡ physicalL2 τ state

    shellParsevalPlancherel : ∀ τ shell state →
      shellCoefficientL2 τ shell state ≡ shellPhysicalL2 τ shell state

    lerayProjectionBounded : ∀ τ state →
      _≤_ A (lerayOutputL2 τ state) (lerayInputL2 τ state)

    biotSavartBounded : ∀ τ state →
      _≤_ A
        (biotSavartVelocityH1 τ state)
        (biotSavartVorticityL2 τ state)

    CutoffUniform : Set t
    cutoffUniform : CutoffUniform

open OfficialNormBernsteinAdapterInputs public

selectedBernsteinStateAdmissible :
  ∀ {t} {A : AbsorptionArithmetic} {Time : Set t}
    {C : Potential.ThreeWayAdditiveCalculus A}
    {R : Leaves.ConcreteReserveLeaves A Time}
    {F : Leaves.RealFundamentalTheoremRealization A C R} →
  (I : OfficialNormBernsteinAdapterInputs A C R F) →
  Time → Bernstein.ShellState (bernstein I) → Set t
selectedBernsteinStateAdmissible I τ state =
  state ≡ Bernstein.shellState (bernstein I) τ

shellCurlFromConcreteBernstein :
  ∀ {t} {A : AbsorptionArithmetic} {Time : Set t}
    {C : Potential.ThreeWayAdditiveCalculus A}
    {R : Leaves.ConcreteReserveLeaves A Time}
    {F : Leaves.RealFundamentalTheoremRealization A C R} →
  (I : OfficialNormBernsteinAdapterInputs A C R F) →
  ∀ τ shell state →
  selectedBernsteinStateAdmissible I τ state →
  _≤_ A
    (Bernstein.shellVorticityL2 (bernstein I) shell state)
    (Bernstein.curlWeightedShell (bernstein I) shell state)
shellCurlFromConcreteBernstein {A = A} I τ shell state stateMeaning =
  subst
    (λ selected →
      _≤_ A
        (Bernstein.shellVorticityL2 (bernstein I) shell selected)
        (Bernstein.curlWeightedShell (bernstein I) shell selected))
    (sym stateMeaning)
    (Bernstein.BE1-shell-curl (bernstein I) shell τ)

shellBernsteinFromConcreteLeaves :
  ∀ {t} {A : AbsorptionArithmetic} {Time : Set t}
    {C : Potential.ThreeWayAdditiveCalculus A}
    {R : Leaves.ConcreteReserveLeaves A Time}
    {F : Leaves.RealFundamentalTheoremRealization A C R} →
  (I : OfficialNormBernsteinAdapterInputs A C R F) →
  ∀ τ shell state →
  selectedBernsteinStateAdmissible I τ state →
  _≤_ A
    (Bernstein.shellVorticityLInfinity (bernstein I) shell state)
    (Bernstein.curlWeightedShell (bernstein I) shell state)
shellBernsteinFromConcreteLeaves {A = A} I τ shell state stateMeaning =
  subst
    (λ selected →
      _≤_ A
        (Bernstein.shellVorticityLInfinity (bernstein I) shell selected)
        (Bernstein.curlWeightedShell (bernstein I) shell selected))
    (sym stateMeaning)
    (Bernstein.BE2-shell-Bernstein-five-halves (bernstein I) shell τ)

vorticityReconstructionFromConcreteLeaves :
  ∀ {t} {A : AbsorptionArithmetic} {Time : Set t}
    {C : Potential.ThreeWayAdditiveCalculus A}
    {R : Leaves.ConcreteReserveLeaves A Time}
    {F : Leaves.RealFundamentalTheoremRealization A C R} →
  (I : OfficialNormBernsteinAdapterInputs A C R F) →
  ∀ τ state →
  selectedBernsteinStateAdmissible I τ state →
  _≤_ A
    (Bernstein.vorticityLInfinity (bernstein I) state)
    (Bernstein.weightedShellSum (bernstein I) state)
vorticityReconstructionFromConcreteLeaves {A = A} I τ state stateMeaning =
  subst
    (λ selected →
      _≤_ A
        (Bernstein.vorticityLInfinity (bernstein I) selected)
        (Bernstein.weightedShellSum (bernstein I) selected))
    (sym stateMeaning)
    (Bernstein.BE3-vorticity-reconstruction (bernstein I) τ)

concreteBernsteinToOfficialNormIdentification :
  ∀ {t} {A : AbsorptionArithmetic} {Time : Set t}
    {C : Potential.ThreeWayAdditiveCalculus A}
    {R : Leaves.ConcreteReserveLeaves A Time}
    {F : Leaves.RealFundamentalTheoremRealization A C R} →
  (I : OfficialNormBernsteinAdapterInputs A C R F) →
  Official.OfficialPeriodicNormIdentification
    A Time Nat (Bernstein.ShellState (bernstein I))
concreteBernsteinToOfficialNormIdentification I = record
  { Admissible = selectedBernsteinStateAdmissible I
  ; coefficientL2 = coefficientL2 I
  ; physicalL2 = physicalL2 I
  ; hSobolevNorm = hSobolevNorm I
  ; shellCoefficientL2 = shellCoefficientL2 I
  ; shellPhysicalL2 = shellPhysicalL2 I
  ; lerayInputL2 = lerayInputL2 I
  ; lerayOutputL2 = lerayOutputL2 I
  ; biotSavartVorticityL2 = biotSavartVorticityL2 I
  ; biotSavartVelocityH1 = biotSavartVelocityH1 I
  ; shellVelocityL2 = Bernstein.shellVelocityL2 (bernstein I)
  ; shellVorticityL2 = Bernstein.shellVorticityL2 (bernstein I)
  ; curlWeightedShell = Bernstein.curlWeightedShell (bernstein I)
  ; shellVorticityLInfinity = Bernstein.shellVorticityLInfinity (bernstein I)
  ; weightedFiveHalvesShellSum =
      λ τ state → Bernstein.weightedShellSum (bernstein I) state
  ; vorticityLInfinity =
      λ τ state → Bernstein.vorticityLInfinity (bernstein I) state
  ; parsevalPlancherel = parsevalPlancherel I
  ; shellParsevalPlancherel = shellParsevalPlancherel I
  ; lerayProjectionBounded = λ τ state admissible →
      lerayProjectionBounded I τ state
  ; biotSavartBounded = λ τ state admissible →
      biotSavartBounded I τ state
  ; shellCurlEstimate = shellCurlFromConcreteBernstein I
  ; shellBernsteinFiveHalves = shellBernsteinFromConcreteLeaves I
  ; curlWeightedShellMeaning = λ τ shell state →
      Bernstein.curlWeightedShellMeaning (bernstein I) shell state
  ; literalHatAgreesWithOfficialShell = shellParsevalPlancherel I
  ; weightedShellReconstructsVorticity =
      vorticityReconstructionFromConcreteLeaves I
  ; CutoffUniform = CutoffUniform I
  ; cutoffUniform = cutoffUniform I
  }
