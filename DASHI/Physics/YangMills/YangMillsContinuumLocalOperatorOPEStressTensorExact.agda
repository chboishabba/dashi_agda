module DASHI.Physics.YangMills.YangMillsContinuumLocalOperatorOPEStressTensorExact where

------------------------------------------------------------------------
-- ROUND64 MASTER THEOREM 7: LOCAL OPERATORS, OPE, AND STRESS TENSOR
--
-- PRIMARY SOURCES / CALIBRATION
--
-- Arthur Jaffe and Edward Witten,
-- "Quantum Yang-Mills Theory", Clay Mathematics Institute Millennium problem
-- description, in The Millennium Prize Problems.  No DOI assigned.
--
-- Stefan Hollands and Christoph Kopper,
-- "The Operator Product Expansion Converges in Perturbative Field Theory",
-- Communications in Mathematical Physics 313 (2012), 257--290.
-- DOI: 10.1007/s00220-012-1457-4.
--
-- Jan Holland, Stefan Hollands and Christoph Kopper,
-- "The Operator Product Expansion Converges in Massless phi^4_4-Theory",
-- Communications in Mathematical Physics 342 (2016), 385--440.
-- DOI: 10.1007/s00220-015-2486-6.
--
-- Alexander N. Efremov, Riccardo Guida and Christoph Kopper,
-- "Renormalization of SU(2) Yang-Mills Theory with Flow Equations",
-- Journal of Mathematical Physics 58 (2017), 093503.
-- DOI: 10.1063/1.5000041.
--
-- IMPORTANT AUTHORITY BOUNDARY
--
-- Hollands/Kopper prove perturbative-loop OPE convergence for scalar phi^4;
-- Efremov/Guida/Kopper prove perturbative SU(2) Yang-Mills renormalizability by
-- flow equations.  Neither source constructs the nonperturbative continuum
-- Yang-Mills local-operator/OPE package required here.  They calibrate a viable
-- analytic mechanism; they do not discharge this master theorem by citation.
--
-- DASHI CONTRIBUTION
--
-- Round63 could reach an abstract SU2ClayConclusion without explicitly carrying
-- the local curvature operators, short-distance OPE/asymptotic-freedom data,
-- and a local conserved stress tensor whose time-translation generator is the
-- reconstructed Hamiltonian.  That was too weak.
--
-- This module makes the missing content one typed theorem package on the SAME
-- continuum Schwinger family.  It also isolates a concrete high-alpha analytic
-- reduction: a dyadic composite-field OPE remainder estimate is the exact
-- quantitative object that a flow-equation/RG proof should produce.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _*_; _≤_)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanTraceKoteckyPreissGeometricExact as Geo

------------------------------------------------------------------------
-- Quantitative OPE remainder target.
------------------------------------------------------------------------

record DyadicOPERemainderMajorant : Set₁ where
  field
    coefficient : ℚ
    coefficientNonnegative : 0ℚ ≤ coefficient
    remainderMagnitude : Nat → ℚ
    remainderNonnegative : ∀ depth → 0ℚ ≤ remainderMagnitude depth
    remainderBelowDyadic : ∀ depth →
      remainderMagnitude depth ≤ coefficient * Geo.halfPower depth

open DyadicOPERemainderMajorant public

-- The theorem is intentionally transparent: once the physical composite-field
-- flow equation gives the dyadic bound, the OPE remainder already carries an
-- explicit vanishing scale modulus.  No additional qualitative "OPE exists"
-- receipt is allowed to replace this quantitative producer.
explicitOPERemainderModulus :
  (dataSet : DyadicOPERemainderMajorant) → ∀ depth →
  remainderMagnitude dataSet depth
  ≤ coefficient dataSet * Geo.halfPower depth
explicitOPERemainderModulus dataSet = remainderBelowDyadic dataSet

------------------------------------------------------------------------
-- Literal continuum-YM target carried by one and the same continuum family.
------------------------------------------------------------------------

record ContinuumLocalOperatorOPEStressTensor
    (ContinuumFamily CurvaturePolynomial LocalOperator Position
     OPECoefficient StressTensor Hamiltonian : Set) : Set₁ where
  field
    continuumFamily : ContinuumFamily

    -- Gauge-invariant curvature-polynomial correspondence.
    localOperator : CurvaturePolynomial → LocalOperator
    GaugeInvariant : LocalOperator → Set
    LocalAt : LocalOperator → Position → Set
    curvatureOperatorsGaugeInvariant : ∀ polynomial →
      GaugeInvariant (localOperator polynomial)
    curvatureOperatorsLocal : ∀ polynomial position →
      LocalAt (localOperator polynomial) position

    -- Same-family short-distance/OPE data.
    OPEAdmissible : LocalOperator → LocalOperator → Set
    coefficient :
      LocalOperator → LocalOperator → LocalOperator → Position → OPECoefficient
    OPERemainder :
      LocalOperator → LocalOperator → Position → Nat → ℚ
    opeRemainderMajorant :
      ∀ left right position → OPEAdmissible left right →
      DyadicOPERemainderMajorant
    opeRemainderIsPhysicalRemainder :
      ∀ left right position admissible depth →
      OPERemainder left right position depth
      ≡ remainderMagnitude
          (opeRemainderMajorant left right position admissible) depth

    -- Short-distance matching to the asymptotically-free renormalized theory.
    ShortDistanceAFMatching : Set
    shortDistanceAFMatching : ShortDistanceAFMatching

    -- Local stress tensor and conservation.
    stressTensor : StressTensor
    Symmetric : StressTensor → Set
    ConservedInCorrelators : StressTensor → Set
    LocalStressTensor : StressTensor → Set
    stressTensorSymmetric : Symmetric stressTensor
    stressTensorConserved : ConservedInCorrelators stressTensor
    stressTensorLocal : LocalStressTensor stressTensor

    -- The reconstructed Hamiltonian must be the generator obtained from the
    -- local T00 density, not merely some abstract positive semigroup generator.
    reconstructedHamiltonian : Hamiltonian
    SpatialIntegralT00Generates : StressTensor → Hamiltonian → Set
    stressTensorGeneratesHamiltonian :
      SpatialIntegralT00Generates stressTensor reconstructedHamiltonian

open ContinuumLocalOperatorOPEStressTensor public

------------------------------------------------------------------------
-- Proof-level classification.
------------------------------------------------------------------------

operemainderModulusCompilerLevel : ProofLevel
operemainderModulusCompilerLevel = machineChecked

phi4OPEFlowEquationPrecedentLevel : ProofLevel
phi4OPEFlowEquationPrecedentLevel = standardImported

su2PerturbativeFlowEquationRenormalizationPrecedentLevel : ProofLevel
su2PerturbativeFlowEquationRenormalizationPrecedentLevel = standardImported

-- The nonperturbative same-family Yang-Mills construction above is genuinely
-- physical and remains a master frontier theorem.
physicalContinuumLocalOperatorOPEStressTensorLevel : ProofLevel
physicalContinuumLocalOperatorOPEStressTensorLevel = conditional
