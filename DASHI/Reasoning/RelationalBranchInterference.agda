module DASHI.Reasoning.RelationalBranchInterference where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Integer using (ℤ; +_; _+_; _-_; _*_)
open import Data.List.Base using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (cong; trans)

import Data.Integer.Tactic.RingSolver as IntRS
import Tactic.RingSolver.NonReflective as NR

import DASHI.Physics.ShiftDiscreteWaveStep as Wave
import DASHI.Physics.ShiftPhaseTableInterference as Phase
import DASHI.Physics.ShiftUnitaryLikeConstraint as Norm

------------------------------------------------------------------------
-- Exact finite double-/n-slit algebra on the repository's integer-pair wave
-- carrier.  This is a non-additive branch-interaction model, not a claim that
-- decisions or relationships are literal quantum systems.
------------------------------------------------------------------------

module RingZ = NR IntRS.ring
open RingZ using (Expr; Κ; Ι; _⊕_; _⊗_; ⊝_; _⊜_; solve)

BranchWave : Set
BranchWave = Wave.DiscreteWave

zeroWave : BranchWave
zeroWave = Wave.mkDiscreteWave (+ 0) (+ 0)

sumWaves : List BranchWave → BranchWave
sumWaves [] = zeroWave
sumWaves (ψ ∷ ψs) = Wave.waveAdd ψ (sumWaves ψs)

coherentIntensity : List BranchWave → ℤ
coherentIntensity ψs = Norm.waveNormSq (sumWaves ψs)

waveDot : BranchWave → BranchWave → ℤ
waveDot ψ χ =
  (Wave.DiscreteWave.re ψ * Wave.DiscreteWave.re χ)
  +
  (Wave.DiscreteWave.im ψ * Wave.DiscreteWave.im χ)

pairInterference : BranchWave → BranchWave → ℤ
pairInterference ψ χ = (+ 2) * waveDot ψ χ

------------------------------------------------------------------------
-- Double-slit polarization identity.
------------------------------------------------------------------------

doubleSlitLaw :
  (ψ χ : BranchWave) →
  Norm.waveNormSq (Wave.waveAdd ψ χ)
  ≡
  (Norm.waveNormSq ψ + Norm.waveNormSq χ)
  + pairInterference ψ χ
doubleSlitLaw
  (Wave.mkDiscreteWave xr xi)
  (Wave.mkDiscreteWave yr yi) =
  RingZ.solve 4
    (λ xr xi yr yi →
      ( (((xr ⊕ yr) ⊗ (xr ⊕ yr))
          ⊕ ((xi ⊕ yi) ⊗ (xi ⊕ yi)))
      , ((((xr ⊗ xr) ⊕ (xi ⊗ xi))
          ⊕ ((yr ⊗ yr) ⊕ (yi ⊗ yi)))
          ⊕ ((Κ (+ 2)) ⊗ ((xr ⊗ yr) ⊕ (xi ⊗ yi)))) ))
    refl xr xi yr yi

pairInterferenceDistributesRight :
  (ψ χ ω : BranchWave) →
  pairInterference ψ (Wave.waveAdd χ ω)
  ≡
  pairInterference ψ χ + pairInterference ψ ω
pairInterferenceDistributesRight
  (Wave.mkDiscreteWave xr xi)
  (Wave.mkDiscreteWave yr yi)
  (Wave.mkDiscreteWave zr zi) =
  RingZ.solve 6
    (λ xr xi yr yi zr zi →
      ( ((Κ (+ 2))
          ⊗ ((xr ⊗ (yr ⊕ zr)) ⊕ (xi ⊗ (yi ⊕ zi))))
      , (((Κ (+ 2)) ⊗ ((xr ⊗ yr) ⊕ (xi ⊗ yi)))
          ⊕
         ((Κ (+ 2)) ⊗ ((xr ⊗ zr) ⊕ (xi ⊗ zi)))) ))
    refl xr xi yr yi zr zi

pairInterferenceWith : BranchWave → List BranchWave → ℤ
pairInterferenceWith ψ [] = + 0
pairInterferenceWith ψ (χ ∷ χs) =
  pairInterference ψ χ + pairInterferenceWith ψ χs

pairInterferenceWithSum :
  (ψ : BranchWave) →
  (ψs : List BranchWave) →
  pairInterference ψ (sumWaves ψs)
  ≡
  pairInterferenceWith ψ ψs
pairInterferenceWithSum ψ [] = refl
pairInterferenceWithSum ψ (χ ∷ χs) =
  trans
    (pairInterferenceDistributesRight ψ χ (sumWaves χs))
    (cong
      (λ z → pairInterference ψ χ + z)
      (pairInterferenceWithSum ψ χs))

------------------------------------------------------------------------
-- Generic n-slit decomposition.
--
-- `nSlitExpansion` is the diagonal intensity plus every pairwise cross term.
-- The theorem proves that the coherent intensity of any finite branch list is
-- exactly this expansion on the integer-pair carrier.
------------------------------------------------------------------------

nSlitExpansion : List BranchWave → ℤ
nSlitExpansion [] = + 0
nSlitExpansion (ψ ∷ ψs) =
  (Norm.waveNormSq ψ + nSlitExpansion ψs)
  + pairInterferenceWith ψ ψs

nSlitDecomposition :
  (ψs : List BranchWave) →
  coherentIntensity ψs ≡ nSlitExpansion ψs
nSlitDecomposition [] = refl
nSlitDecomposition (ψ ∷ ψs) =
  trans
    (doubleSlitLaw ψ (sumWaves ψs))
    (trans
      (cong
        (λ z →
          (Norm.waveNormSq ψ + z)
          + pairInterference ψ (sumWaves ψs))
        (nSlitDecomposition ψs))
      (cong
        (λ z →
          (Norm.waveNormSq ψ + nSlitExpansion ψs) + z)
        (pairInterferenceWithSum ψ ψs)))

diagonalIntensity : List BranchWave → ℤ
diagonalIntensity [] = + 0
diagonalIntensity (ψ ∷ ψs) =
  Norm.waveNormSq ψ + diagonalIntensity ψs

allPairwiseInterference : List BranchWave → ℤ
allPairwiseInterference [] = + 0
allPairwiseInterference (ψ ∷ ψs) =
  pairInterferenceWith ψ ψs + allPairwiseInterference ψs

rearrangeExpansion :
  (a b c d : ℤ) →
  (a + (b + c)) + d ≡ (a + b) + (d + c)
rearrangeExpansion a b c d =
  RingZ.solve 4
    (λ a b c d →
      ( ((a ⊕ (b ⊕ c)) ⊕ d)
      , ((a ⊕ b) ⊕ (d ⊕ c)) ))
    refl a b c d

nSlitSeparatesDiagonalAndPairs :
  (ψs : List BranchWave) →
  nSlitExpansion ψs
  ≡
  diagonalIntensity ψs + allPairwiseInterference ψs
nSlitSeparatesDiagonalAndPairs [] = refl
nSlitSeparatesDiagonalAndPairs (ψ ∷ ψs) =
  trans
    (cong
      (λ z →
        (Norm.waveNormSq ψ + z)
        + pairInterferenceWith ψ ψs)
      (nSlitSeparatesDiagonalAndPairs ψs))
    (rearrangeExpansion
      (Norm.waveNormSq ψ)
      (diagonalIntensity ψs)
      (allPairwiseInterference ψs)
      (pairInterferenceWith ψ ψs))

exactNSlitLaw :
  (ψs : List BranchWave) →
  coherentIntensity ψs
  ≡
  diagonalIntensity ψs + allPairwiseInterference ψs
exactNSlitLaw ψs =
  trans
    (nSlitDecomposition ψs)
    (nSlitSeparatesDiagonalAndPairs ψs)

------------------------------------------------------------------------
-- Third-order residual.
--
-- On an ordinary amplitude-squared carrier, the three-slit intensity contains
-- diagonal and pairwise terms only.  The Sorkin-style third-order residual is
-- therefore exactly zero.
------------------------------------------------------------------------

thirdOrderResidual :
  BranchWave → BranchWave → BranchWave → ℤ
thirdOrderResidual ψ χ ω =
  (((coherentIntensity (ψ ∷ χ ∷ ω ∷ [])
      - coherentIntensity (ψ ∷ χ ∷ []))
      - coherentIntensity (ψ ∷ ω ∷ []))
      - coherentIntensity (χ ∷ ω ∷ []))
      + Norm.waveNormSq ψ
      + Norm.waveNormSq χ
      + Norm.waveNormSq ω

thirdOrderResidualZero :
  (ψ χ ω : BranchWave) →
  thirdOrderResidual ψ χ ω ≡ + 0
thirdOrderResidualZero
  (Wave.mkDiscreteWave xr xi)
  (Wave.mkDiscreteWave yr yi)
  (Wave.mkDiscreteWave zr zi) =
  RingZ.solve 6
    (λ xr xi yr yi zr zi →
      let
        nx = (xr ⊗ xr) ⊕ (xi ⊗ xi)
        ny = (yr ⊗ yr) ⊕ (yi ⊗ yi)
        nz = (zr ⊗ zr) ⊕ (zi ⊗ zi)
        nxy =
          ((xr ⊕ yr) ⊗ (xr ⊕ yr))
          ⊕
          ((xi ⊕ yi) ⊗ (xi ⊕ yi))
        nxz =
          ((xr ⊕ zr) ⊗ (xr ⊕ zr))
          ⊕
          ((xi ⊕ zi) ⊗ (xi ⊕ zi))
        nyz =
          ((yr ⊕ zr) ⊗ (yr ⊕ zr))
          ⊕
          ((yi ⊕ zi) ⊗ (yi ⊕ zi))
        nxyz =
          (((xr ⊕ yr) ⊕ zr) ⊗ ((xr ⊕ yr) ⊕ zr))
          ⊕
          (((xi ⊕ yi) ⊕ zi) ⊗ ((xi ⊕ yi) ⊕ zi))
      in
      ( ((((((nxyz ⊝ nxy) ⊝ nxz) ⊝ nyz) ⊕ nx) ⊕ ny) ⊕ nz)
      , Κ (+ 0) ))
    refl xr xi yr yi zr zi

------------------------------------------------------------------------
-- Canonical exact diffraction witnesses.
------------------------------------------------------------------------

phase0 phase1 phase2 phase3 : BranchWave
phase0 = Wave.encodePhase4 Phase.φ0
phase1 = Wave.encodePhase4 Phase.φ1
phase2 = Wave.encodePhase4 Phase.φ2
phase3 = Wave.encodePhase4 Phase.φ3

doubleInPhaseIntensityIsFour :
  coherentIntensity (phase0 ∷ phase0 ∷ []) ≡ + 4
doubleInPhaseIntensityIsFour = refl

doubleOppositeCancels :
  coherentIntensity (phase0 ∷ phase2 ∷ []) ≡ + 0
doubleOppositeCancels = refl

doubleQuadratureIsIncoherentMass :
  coherentIntensity (phase0 ∷ phase1 ∷ []) ≡ + 2
doubleQuadratureIsIncoherentMass = refl

threeInPhaseIntensityIsNine :
  coherentIntensity (phase0 ∷ phase0 ∷ phase0 ∷ []) ≡ + 9
threeInPhaseIntensityIsNine = refl

fourQuarterTurnsCancel :
  coherentIntensity (phase0 ∷ phase1 ∷ phase2 ∷ phase3 ∷ []) ≡ + 0
fourQuarterTurnsCancel = refl

record BranchInterferenceAuthorityBoundary : Set where
  field
    exactFiniteIntegerPairAlgebra : Bool
    allFiniteCrossTermsRetained : Bool
    thirdOrderResidualZeroOnCarrier : Bool
    literalQuantumDecisionDynamicsClaimed : Bool
    bornRuleOrPhysicalProbabilityClaimed : Bool
    phaseHasUniquePsychologicalMeaning : Bool
    boundaryNote : String

canonicalBranchInterferenceAuthorityBoundary :
  BranchInterferenceAuthorityBoundary
canonicalBranchInterferenceAuthorityBoundary = record
  { exactFiniteIntegerPairAlgebra = true
  ; allFiniteCrossTermsRetained = true
  ; thirdOrderResidualZeroOnCarrier = true
  ; literalQuantumDecisionDynamicsClaimed = false
  ; bornRuleOrPhysicalProbabilityClaimed = false
  ; phaseHasUniquePsychologicalMeaning = false
  ; boundaryNote =
      "The exact theorems concern the repository's finite integer-pair wave carrier. Relational phase denotes path compatibility or conflict by analogy; no Hilbert-space, Born-rule, quantum-cognition or physical-collapse claim is made."
  }
