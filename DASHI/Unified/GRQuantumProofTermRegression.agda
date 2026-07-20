module DASHI.Unified.GRQuantumProofTermRegression where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([])
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Unit using (tt)

open import DASHI.Unified.GRQuantumProofTerms
import DASHI.Core.FiniteQuadraticMultiscale as Quadratic
import DASHI.Geometry.FiniteCausalDiamond as Diamond
import DASHI.Geometry.FiniteCausalDiamondClosed as DiamondClosed
import DASHI.Algebra.Quantum.FiniteTreeWeyl as Tree
import DASHI.Physics.Closure.PropositionEinsteinBridge as Einstein
import DASHI.Physics.Closure.PropositionConstraintAlgebra as Constraints
import DASHI.Physics.Closure.FiniteRegionalSpectrum as UV
import DASHI.Unified.GRQuantumProofAdapters as Adapters

------------------------------------------------------------------------
-- Compact import and exact-proof regression surface.

quadraticCanonicalUnique :
  Quadratic.finiteQuadraticEnergyUnique
    Quadratic.canonicalQuadraticEnergy
    Quadratic.canonicalEnergySatisfiesLaws
  ≡ Quadratic.canonicalQuadraticEnergy
quadraticCanonicalUnique = refl

finiteSpatialDimensionIsThree :
  ChainAntichainLorentzProof.spatialDimension
    Diamond.finiteCausalDiamondProof
  ≡ 3
finiteSpatialDimensionIsThree =
  ChainAntichainLorentzProof.spatialDimensionIsThree
    Diamond.finiteCausalDiamondProof

finiteCausalClosureExists :
  ChainAntichainLorentzClosed Diamond.finiteCausalDiamondProof
finiteCausalClosureExists = DiamondClosed.finiteCausalDiamondClosed

treeProjectRefineEmpty : Tree.project (Tree.refine []) ≡ []
treeProjectRefineEmpty = refl

qutritShiftThreeIdentity : Tree.shift (Tree.shift (Tree.shift Tree.q0)) ≡ Tree.q0
qutritShiftThreeIdentity = refl

flatConstraintMomentumClosure :
  ConstraintAlgebraProof.momentumMomentumClosure
    Constraints.flatConstraintSurface
flatConstraintMomentumClosure =
  ConstraintAlgebraClosed.momentumMomentumClosureProof
    Constraints.flatConstraintClosed

regulatedHamiltonianSpectrumEnumeration :
  UV.FiniteEnumeration
    (UV.regulatedSpectrum UV.regulatedHamiltonian)
regulatedHamiltonianSpectrumEnumeration =
  UV.regulatedSpectrumFinite UV.regulatedHamiltonian

exactFlatEinsteinProducerExists : Einstein.ExactFlatEinsteinProducer
exactFlatEinsteinProducerExists = Einstein.canonicalExactFlatEinsteinProducer

exactFiniteBundleExists : Adapters.ExactFiniteGRQuantumBundle
exactFiniteBundleExists = Adapters.canonicalExactFiniteGRQuantumBundle

terminalBoundaryText : String
terminalBoundaryText =
  "Regression proves the finite/model bundle composes.  No TerminalGRQuantumProof is synthesized without continuum, anomaly, low-energy, and empirical proof inhabitants."
