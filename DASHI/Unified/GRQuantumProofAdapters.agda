module DASHI.Unified.GRQuantumProofAdapters where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (suc)
open import Agda.Builtin.String using (String)

open import DASHI.Unified.GRQuantumProofTerms
open import DASHI.Unified.GRQuantumStrictProofTerms using (StrictSpinDoubleCoverProof)
import DASHI.Core.MultiscaleMDL as MDL
import DASHI.Core.FiniteQuadraticMultiscale as Quadratic
import DASHI.Geometry.FiniteCausalDiamond as Diamond
import DASHI.Geometry.FiniteCausalDiamondClosed as DiamondClosed
import DASHI.Geometry.FiniteCausalDiamondMinimality as DiamondMinimality
import DASHI.Algebra.ConstructiveClifford as Clifford
import DASHI.Algebra.FiniteQuaternionDoubleCover as QuaternionCover
import DASHI.Algebra.FiniteQuaternionStrictCover as QuaternionStrict
import DASHI.Algebra.FiniteQuaternionGroupReceipts as QuaternionUnits
import DASHI.Algebra.Quantum.FiniteTreeWeyl as Tree
import DASHI.Algebra.Quantum.FiniteQutritBornAdditivity as BornAdditivity
import DASHI.Physics.Closure.PropositionEinsteinBridge as Einstein
import DASHI.Physics.Closure.PropositionConstraintAlgebra as Constraints
import DASHI.Physics.Closure.FiniteRegionalSpectrum as UV
import DASHI.Physics.Closure.FiniteQuantumGRFlatModel as FlatQGR
import DASHI.Unified.GRQuantumFiniteDiagnosticReceipt as Diagnostic

------------------------------------------------------------------------
-- Exact adapter from the existing multiscale residual theorem.

residualReconstructionAdapter :
  ∀ {tower : MDL.MultiscaleCarrier}
    (codec : MDL.ResidualCodec tower)
    {j}
    (state : MDL.Carrier tower (suc j)) →
  MDL.join codec (MDL.split codec state) ≡ state
residualReconstructionAdapter = MDL.join-split

------------------------------------------------------------------------
-- Proof ledger.


data ProofGate : Set where
  quadraticGate : ProofGate
  chainAntichainGate : ProofGate
  cliffordSpinGate : ProofGate
  waveCCRAndBornGate : ProofGate
  tensorEinsteinGate : ProofGate
  constraintAlgebraGate : ProofGate
  uvSpectrumGate : ProofGate
  empiricalCorrespondenceGate : ProofGate


data GateStatus : Set where
  exactFiniteProof : GateStatus
  propositionInterfaceWithFiniteProducer : GateStatus
  conditionalContinuumAuthorityRequired : GateStatus
  empiricalValidationRequired : GateStatus

currentGateStatus : ProofGate → GateStatus
currentGateStatus quadraticGate = exactFiniteProof
currentGateStatus chainAntichainGate = exactFiniteProof
currentGateStatus cliffordSpinGate = propositionInterfaceWithFiniteProducer
currentGateStatus waveCCRAndBornGate = propositionInterfaceWithFiniteProducer
currentGateStatus tensorEinsteinGate = propositionInterfaceWithFiniteProducer
currentGateStatus constraintAlgebraGate = propositionInterfaceWithFiniteProducer
currentGateStatus uvSpectrumGate = propositionInterfaceWithFiniteProducer
currentGateStatus empiricalCorrespondenceGate = empiricalValidationRequired

currentProofGates : List ProofGate
currentProofGates =
  quadraticGate
  ∷ chainAntichainGate
  ∷ cliffordSpinGate
  ∷ waveCCRAndBornGate
  ∷ tensorEinsteinGate
  ∷ constraintAlgebraGate
  ∷ uvSpectrumGate
  ∷ empiricalCorrespondenceGate
  ∷ []

------------------------------------------------------------------------
-- The exact finite tranche that can be assembled today.

record ExactFiniteGRQuantumBundle : Set₁ where
  constructor exact-finite-gr-quantum-bundle
  field
    quadraticUniqueness : QuadraticUniquenessProof
    causalDiamond : ChainAntichainLorentzProof
    causalDiamondClosed : ChainAntichainLorentzClosed causalDiamond
    causalMinimality : DiamondMinimality.FiniteChainAntichainMinimalityReceipt
    cliffordSyntax : Set
    finiteSpinDoubleCover : SpinDoubleCoverProof
    strictFiniteSpinDoubleCover : StrictSpinDoubleCoverProof
    quaternionUnitLaws : QuaternionUnits.FiniteQuaternionUnitReceipt
    treeShift : Tree.TreeShiftReceipt
    finiteBorn : Tree.FiniteBornReceipt
    finiteBornAdditivity : BornAdditivity.FiniteQutritBornAdditivityReceipt
    flatEinstein : Einstein.ExactFlatEinsteinProducer
    flatConstraints : ConstraintAlgebraProof
    flatConstraintsClosed : ConstraintAlgebraClosed flatConstraints
    regulatedUV : UV.RegulatedUVReceipt
    regulatedUVPartial : UV.RegulatedUVPartialClosure
    flatQuantumGR : FlatQGR.FlatQuantumGRInterfaceReceipt
    executableDiagnostic : Diagnostic.GRQuantumFiniteDiagnosticReceipt
    scope : String
open ExactFiniteGRQuantumBundle public

canonicalExactFiniteGRQuantumBundle : ExactFiniteGRQuantumBundle
canonicalExactFiniteGRQuantumBundle =
  exact-finite-gr-quantum-bundle
    Quadratic.finiteQuadraticUniquenessProof
    Diamond.finiteCausalDiamondProof
    DiamondClosed.finiteCausalDiamondClosed
    DiamondMinimality.canonicalFiniteChainAntichainMinimalityReceipt
    Clifford.constructiveCliffordScope
    QuaternionCover.finiteQuaternionSpinCover
    QuaternionStrict.finiteQuaternionStrictSpinCover
    QuaternionUnits.canonicalFiniteQuaternionUnitReceipt
    Tree.canonicalTreeShiftReceipt
    Tree.canonicalFiniteBornReceipt
    BornAdditivity.canonicalFiniteQutritBornAdditivityReceipt
    Einstein.canonicalExactFlatEinsteinProducer
    Constraints.flatConstraintSurface
    Constraints.flatConstraintClosed
    UV.canonicalRegulatedUVReceipt
    UV.canonicalRegulatedUVPartialClosure
    FlatQGR.flatQuantumGRInterfaceReceipt
    Diagnostic.canonicalGRQuantumFiniteDiagnosticReceipt
    "exact finite/model tranche only; strict Q8 -> V4 is the finite Spin subgroup cover, not the full continuum cover"

------------------------------------------------------------------------
-- Compatibility-level terminal assembly.

assembleTerminalGRQuantumProof :
  (quadratic : QuadraticUniquenessProof) →
  (causal : ChainAntichainLorentzProof) →
  ChainAntichainLorentzClosed causal →
  (clifford : CliffordUniversalProof) →
  (spin : SpinDoubleCoverProof) →
  (wave : WaveLiftCCRProof) →
  WaveLiftCCRClosed wave →
  (einstein : EinsteinTensorProof) →
  EinsteinTensorClosed einstein →
  (constraints : ConstraintAlgebraProof) →
  ConstraintAlgebraClosed constraints →
  (uv : UVSpectralProof) →
  UVSpectralClosed uv →
  (oneSubstrate : Set) → oneSubstrate →
  (quantumRecovered : Set) → quantumRecovered →
  (grRecovered : Set) → grRecovered →
  (empirical : Set) → empirical →
  TerminalGRQuantumProof
assembleTerminalGRQuantumProof
  quadratic causal causalClosed clifford spin wave waveClosed
  einstein einsteinClosed constraints constraintsClosed uv uvClosed
  oneSubstrate oneSubstrateProof
  quantumRecovered quantumRecoveredProof
  grRecovered grRecoveredProof
  empirical empiricalProof =
  record
    { quadratic = quadratic
    ; causalLorentz = causal
    ; causalLorentzClosed = causalClosed
    ; clifford = clifford
    ; spinCover = spin
    ; waveCCR = wave
    ; waveCCRClosed = waveClosed
    ; einstein = einstein
    ; einsteinClosed = einsteinClosed
    ; constraints = constraints
    ; constraintsClosed = constraintsClosed
    ; uvSpectrum = uv
    ; uvSpectrumClosed = uvClosed
    ; oneUnderlyingSubstrate = oneSubstrate
    ; oneUnderlyingSubstrateProof = oneSubstrateProof
    ; quantumReadingRecovered = quantumRecovered
    ; quantumReadingRecoveredProof = quantumRecoveredProof
    ; generalRelativisticReadingRecovered = grRecovered
    ; generalRelativisticReadingRecoveredProof = grRecoveredProof
    ; empiricalCorrespondenceSupplied = empirical
    ; empiricalCorrespondenceSuppliedProof = empiricalProof
    }

------------------------------------------------------------------------
-- Human-readable exact blockers.

remainingAuthority : ProofGate → String
remainingAuthority quadraticGate =
  "Generalize finite four-state uniqueness to the selected complete linear/Hilbert carrier using the parallelogram-law characterization."
remainingAuthority chainAntichainGate =
  "Prove continuum/large-poset dimensional uniqueness rather than only the exact five-event 1+3 diamond."
remainingAuthority cliffordSpinGate =
  "Lift the exact strict Q8 -> V4 subgroup cover to the Clifford quotient universal theorem, twisted-adjoint metric preservation, and continuous Spin(3,1) -> SO+(3,1) cover."
remainingAuthority waveCCRAndBornGate =
  "Supply Hilbert completion, operator topology, tree scaling limit, central commutator, and general Born additivity."
remainingAuthority tensorEinsteinGate =
  "Supply metric selection, discrete-to-continuum Riemann/Ricci convergence, general Bianchi/Noether conservation, and spin-two bootstrap."
remainingAuthority constraintAlgebraGate =
  "Replace the exact trivial flat algebra by the nontrivial metric-dependent hypersurface-deformation representation and prove quantum anomaly freedom."
remainingAuthority uvSpectrumGate =
  "Prove renormalized amplitude convergence and identify the regulated low-energy limit with required GR/QFT observables."
remainingAuthority empiricalCorrespondenceGate =
  "Define measured observables, recover constants and known limits, benchmark numerically, state a falsifiable deviation, and obtain independent review."
