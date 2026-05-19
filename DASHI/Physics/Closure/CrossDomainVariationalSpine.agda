module DASHI.Physics.Closure.CrossDomainVariationalSpine where

open import Agda.Primitive using (Set; Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- Cross-domain variational spine.
--
-- This module records the common typed object shared by the physics,
-- chemistry, biology, and perception surfaces:
--
--   (X, delta, pi, defect, gate, observation, symmetry)
--
-- It is a normalized theorem target and paper boundary, not a quantitative
-- calibration or empirical-prediction proof for chemistry/biology/perception.

data CrossDomain : Set where
  physicsDomain :
    CrossDomain

  molecularDomain :
    CrossDomain

  bondingDomain :
    CrossDomain

  biologicalDomain :
    CrossDomain

  perceptualDomain :
    CrossDomain

data OrbitClassInvariant : Set where
  transportOrbitInvariant :
    OrbitClassInvariant

  projectionDefectInvariant :
    OrbitClassInvariant

  symmetryQuotientInvariant :
    OrbitClassInvariant

  observableScaleInvariant :
    OrbitClassInvariant

  nonCollapseIntermediateInvariant :
    OrbitClassInvariant

record TypedVariationalObject : Setω where
  field
    X :
      Set

    Complexity :
      Set

    Observable :
      Set

    Defect :
      Set

    Symmetry :
      Set

    delta :
      X →
      Complexity

    projection :
      X →
      X

    defect :
      X →
      Defect

    admissibleGate :
      X →
      X →
      Set

    observationQuotient :
      X →
      Observable

    symmetryAction :
      Symmetry →
      X →
      X

    localMinimum :
      X →
      Set

    stableScientificObject :
      X →
      Set

    stableImpliesLocalMinimum :
      (x : X) →
      stableScientificObject x →
      localMinimum x

    admissibleDescent :
      (x y : X) →
      admissibleGate x y →
      Set

    projectionDefectDecomposition :
      (x : X) →
      Set

    symmetryOrbitStructure :
      (x : X) →
      Set

    scaleSensitiveObservability :
      (x : X) →
      Set

    nonCollapseIntermediateState :
      (x : X) →
      Set

open TypedVariationalObject public

record DomainSpineTarget : Setω where
  field
    domain :
      CrossDomain

    carrierName :
      String

    functionalName :
      String

    projectionName :
      String

    defectName :
      String

    fixedPointName :
      String

    orbitInvariant :
      OrbitClassInvariant

    typedObjectName :
      String

    theoremTarget :
      String

    promotionBoundary :
      List String

open DomainSpineTarget public

record MolecularPESProjectionTarget : Setω where
  field
    NuclearConfiguration :
      Set

    Energy :
      Set

    V :
      NuclearConfiguration →
      Energy

    promotedMinimum :
      NuclearConfiguration →
      Set

    pesDescent :
      NuclearConfiguration →
      NuclearConfiguration →
      Set

    fixedPointIsPESMinimum :
      String

record BondingProjectionDefectTarget : Setω where
  field
    Density :
      Set

    EnergyFunctional :
      Set

    bondProjection :
      Density →
      Density

    bondDefect :
      Density →
      Density

    bondingDensity :
      Density →
      Set

    antibondingResidual :
      Density →
      Set

    projectionDefectLawName :
      String

record ResonanceMDLProjectionTarget : Setω where
  field
    ResonanceForm :
      Set

    Weight :
      Set

    Density :
      Set

    weightedHybrid :
      List ResonanceForm →
      List Weight →
      Density

    mdlWeightSelection :
      List ResonanceForm →
      List Weight →
      Set

    resonanceAsCompressionLawName :
      String

record BiologicalAttractorTarget : Setω where
  field
    BiologicalState :
      Set

    BiologicalModel :
      Set

    BiologicalCost :
      BiologicalState →
      BiologicalModel →
      Set

    foldOrQuasispeciesAttractor :
      BiologicalState →
      Set

    gradientDescentLawName :
      String

record PerceptualOrbitClassTarget : Setω where
  field
    PhaseCarrier :
      Set

    PerceptualReadout :
      Set

    PhaseSymmetry :
      Set

    phaseAction :
      PhaseSymmetry →
      PhaseCarrier →
      PhaseCarrier

    kluverClass :
      PhaseCarrier →
      PerceptualReadout

    tunnel spiral lattice cobweb :
      PerceptualReadout

    orbitQuotientLawName :
      String

data CrossDomainBridgeStatus : Set where
  spineTypedNonPromoting :
    CrossDomainBridgeStatus

data CrossDomainFirstMissing : Set where
  missingQuantitativeCalibration :
    CrossDomainFirstMissing

  missingUniversalityProof :
    CrossDomainFirstMissing

  missingComputationalTractabilityProof :
    CrossDomainFirstMissing

  missingChemistryEmpiricalPredictionReceipt :
    CrossDomainFirstMissing

  missingBiologyEmpiricalPredictionReceipt :
    CrossDomainFirstMissing

  missingPerceptionEmpiricalPredictionReceipt :
    CrossDomainFirstMissing

  missingCrossDomainRecoveryEquivalence :
    CrossDomainFirstMissing

record CrossDomainVariationalSpineBoundary : Set where
  field
    status :
      CrossDomainBridgeStatus

    commonTypedObjectName :
      String

    commonTypedObjectFields :
      List String

    sharedLawfulStructure :
      List String

    domainRows :
      List String

    molecularInterpretation :
      List String

    bondingInterpretation :
      List String

    resonanceInterpretation :
      List String

    biologicalInterpretation :
      List String

    perceptualInterpretation :
      List String

    physicsStatement :
      String

    stableObjectStatement :
      String

    fixedPointClaimIsStructural :
      Bool

    quantitativeCalibrationClosed :
      Bool

    universalityProofClosed :
      Bool

    empiricalPredictionDepthClosed :
      Bool

    exactFirstMissing :
      List CrossDomainFirstMissing

    allowedClaim :
      List String

    forbiddenClaim :
      List String

open CrossDomainVariationalSpineBoundary public

canonicalCrossDomainVariationalSpineBoundary :
  CrossDomainVariationalSpineBoundary
canonicalCrossDomainVariationalSpineBoundary =
  record
    { status =
        spineTypedNonPromoting
    ; commonTypedObjectName =
        "(X, delta, pi, defect, gate, observation, symmetry)"
    ; commonTypedObjectFields =
        "X : carrier"
        ∷ "delta : MDL / Lyapunov / variational functional"
        ∷ "pi : promoted projection"
        ∷ "defect : residual d = x - pi(x), represented by the domain carrier"
        ∷ "gate : admissibility relation on transitions"
        ∷ "observation : quotient/readout of promoted observables"
        ∷ "symmetry : action whose orbit classes define invariants"
        ∷ []
    ; sharedLawfulStructure =
        "admissible descent"
        ∷ "projection-defect decomposition"
        ∷ "symmetry-orbit structure"
        ∷ "scale-sensitive observability"
        ∷ "non-collapse intermediate states"
        ∷ "orbit-class invariants"
        ∷ []
    ; domainRows =
        "Molecular: X = nuclear configuration, delta = potential-energy surface V(R), fixed point = R*"
        ∷ "Bonding: X = density carrier, delta = density functional V[rho], fixed point = promoted bonding density rho*"
        ∷ "Biological: X = biological sequence/fold/state, delta = -log P(s | M) or free-energy/MDL functional, fixed point = folded/quasispecies attractor"
        ∷ "Perceptual: X = phase carrier Phi, delta = perceptual compression/orbit cost, fixed point = Kluver orbit attractor"
        ∷ []
    ; molecularInterpretation =
        "PES minima are local minima of the domain variational functional"
        ∷ "Molecular relaxation is admissible descent on the same typed spine"
        ∷ "No molecular prediction accuracy is claimed by this boundary alone"
        ∷ []
    ; bondingInterpretation =
        "bonding density is the promoted projection"
        ∷ "antibonding density is residual defect relative to the projection"
        ∷ "rho = pi_AB rho + d_AB rho is recorded as a theorem target, not a closed density-functional derivation"
        ∷ []
    ; resonanceInterpretation =
        "resonance hybrid is constrained compression over admissible projection families"
        ∷ "weights are selected by MDL minimization in the target theorem"
        ∷ "no resonance energy or spectrum prediction is promoted here"
        ∷ []
    ; biologicalInterpretation =
        "folding funnels, quasispecies equilibria, and RG/MDL descent share the local-minimum schema"
        ∷ "biology enters as a carrier change, not as a metaphorical analogy"
        ∷ "no protein, molecular, or evolutionary prediction receipt is constructed here"
        ∷ []
    ; perceptualInterpretation =
        "Kluver form constants are orbit classes of a phase carrier under a symmetry quotient"
        ∷ "tunnels, spirals, lattices, and cobwebs are readouts of orbit-class invariants"
        ∷ "no cortical mechanism or perceptual empirical fit is claimed here"
        ∷ []
    ; physicsStatement =
        "Physics is lawful change under scale, symmetry, and observation"
    ; stableObjectStatement =
        "A stable scientific object is represented as a local minimum of a typed MDL/variational functional"
    ; fixedPointClaimIsStructural =
        true
    ; quantitativeCalibrationClosed =
        false
    ; universalityProofClosed =
        false
    ; empiricalPredictionDepthClosed =
        false
    ; exactFirstMissing =
        missingQuantitativeCalibration
        ∷ missingUniversalityProof
        ∷ missingComputationalTractabilityProof
        ∷ missingChemistryEmpiricalPredictionReceipt
        ∷ missingBiologyEmpiricalPredictionReceipt
        ∷ missingPerceptionEmpiricalPredictionReceipt
        ∷ missingCrossDomainRecoveryEquivalence
        ∷ []
    ; allowedClaim =
        "Physics, chemistry, biology, and perception now share a typed projection-defect / MDL spine as a formal theorem target"
        ∷ "The cross-domain extension is structural and compositional"
        ∷ "Stable objects across the named domains can be represented by the same local-minimum schema"
        ∷ "Kluver form constants can be stated as a symmetry-orbit quotient target"
        ∷ []
    ; forbiddenClaim =
        "No chemistry closure theorem follows from this boundary"
        ∷ "No molecular spectrum, bonding-energy, protein-folding, biology, or perception prediction is promoted"
        ∷ "No universal TOE closure follows from this bridge without the missing universality and empirical receipts"
        ∷ "No claim is made that molecules, brains, DNA, and wavefunctions are literally the same object"
        ∷ []
    }
