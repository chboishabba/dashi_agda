module DASHI.Physics.YangMills.BalabanSU2ClayBackwardsCompilerExact where

------------------------------------------------------------------------
-- BACKWARDS-COMPILED SU(2) CLAY PROOF SHAPE
--
-- Development policy:
--
--   assume the genuinely unfinished physical producers are supplied,
--   then require the rest of the SU(2) construction to compile all the way
--   to the final Clay-facing conclusion.
--
-- This is deliberately stronger than a prose frontier list.  The thirteen
-- current physical obligations occur as proposition TYPES first and as
-- WITNESSES second.  Every construction stage consumes exactly the witnesses
-- assigned to that stage.  Consequently a future change of quantifiers,
-- carrier, cutoff uniformity, scale dependence, or positivity must occur in
-- the producer type itself and is exposed immediately at the compiler edge.
--
-- No final theorem is postulated here.  The only hypothetical inputs are the
-- explicitly named physical producer witnesses.  The remaining arrows are the
-- theorem graph that must be instantiated from already-proved repository
-- compilers / standard imported mathematics.
--
-- PRIMARY ENDPOINT SOURCES
--
-- Konrad Osterwalder and Robert Schrader,
-- "Axioms for Euclidean Green's Functions",
-- Communications in Mathematical Physics 31 (1973), 83--112.
-- DOI: 10.1007/BF01645738.
--
-- Konrad Osterwalder and Robert Schrader,
-- "Axioms for Euclidean Green's Functions II",
-- Communications in Mathematical Physics 42 (1975), 281--305.
-- DOI: 10.1007/BF01608978.
--
-- Arthur Jaffe and Edward Witten,
-- "Quantum Yang-Mills Theory", Clay Mathematics Institute Millennium Problem
-- description, 2000.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; _+_)
open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- 1. The authoritative physical frontier is a family of proposition TYPES.
--
-- We separate these from witnesses so a proposition can later be strengthened
-- without changing the shape of the proof compiler.  For example, replacing
-- a pointwise transfer-gap proposition by a cutoff-uniform one changes E1's
-- type and forces every dependent edge to re-typecheck.
------------------------------------------------------------------------

record SU2PhysicalProducerTypes : Set₁ where
  field
    -- A. Literal G2, kept signed until the physical enclosure boundary.
    G2CorrelatedDegreeOneBound : Set
    G2RawHigherDegreeBound : Set

    -- B. Literal Wilson + ghost + Haar one-loop coefficient.
    LiteralOneLoopCoefficientPositive : Set

    -- C. Nonlinear physical RG.
    PhysicalQuarticRemainderUniform : Set

    -- D. Literal transfer squares.
    LiteralWilsonKernelNaturality : Set
    LiteralTemporalTraceNaturality : Set

    -- E. Uniform lattice spectral gap / Schur-Feshbach loss.
    TerminalPhysicalWilsonTransferGap : Set
    CutoffUniformPhysicalFeshbachLossBudget : Set

    -- F. Continuum construction.
    PhysicalRenormalizedSchwingerScaleIncrementUniform : Set
    RenormalizedYangMillsSchwingerTightness : Set
    YangMillsContinuumOSUniqueLimit : Set

    -- G. Continuum interaction and physical mass scale.
    PhysicalContinuumFourthCumulantLowerBound : Set
    PhysicalUniformExponentialClustering : Set

open SU2PhysicalProducerTypes public

record SU2PhysicalProducers (types : SU2PhysicalProducerTypes) : Set₁ where
  field
    g2CorrelatedDegreeOneBound : G2CorrelatedDegreeOneBound types
    g2RawHigherDegreeBound : G2RawHigherDegreeBound types

    literalOneLoopCoefficientPositive :
      LiteralOneLoopCoefficientPositive types

    physicalQuarticRemainderUniform :
      PhysicalQuarticRemainderUniform types

    literalWilsonKernelNaturality :
      LiteralWilsonKernelNaturality types
    literalTemporalTraceNaturality :
      LiteralTemporalTraceNaturality types

    terminalPhysicalWilsonTransferGap :
      TerminalPhysicalWilsonTransferGap types
    cutoffUniformPhysicalFeshbachLossBudget :
      CutoffUniformPhysicalFeshbachLossBudget types

    physicalRenormalizedSchwingerScaleIncrementUniform :
      PhysicalRenormalizedSchwingerScaleIncrementUniform types
    renormalizedYangMillsSchwingerTightness :
      RenormalizedYangMillsSchwingerTightness types
    yangMillsContinuumOSUniqueLimit :
      YangMillsContinuumOSUniqueLimit types

    physicalContinuumFourthCumulantLowerBound :
      PhysicalContinuumFourthCumulantLowerBound types
    physicalUniformExponentialClustering :
      PhysicalUniformExponentialClustering types

open SU2PhysicalProducers public

------------------------------------------------------------------------
-- 2. End-to-end theorem graph.
--
-- The stage types are intentionally semantic rather than receipt-shaped:
--
--   physical local/RG input
--        -> renormalized lattice family
--        -> cutoff-uniform transfer theory
--        -> unique continuum Schwinger family
--        -> interacting clustered continuum YM
--        -> OS/Wightman endpoint
--        -> SU(2) Clay conclusion.
--
-- Each arrow consumes ONLY the physical producers belonging to that campaign.
-- Thus a hidden cross-campaign dependency cannot be introduced without
-- changing a type here.
------------------------------------------------------------------------

record SU2BackwardsTheoremGraph (types : SU2PhysicalProducerTypes) : Set₁ where
  field
    RenormalizedLatticeFamily : Set
    UniformTransferTheory : Set
    ContinuumSchwingerFamily : Set
    InteractingClusteredContinuumYM : Set
    OSWightmanEndpoint : Set
    SU2ClayConclusion : Set

    -- A+B+C: local background / one-loop / nonlinear RG close the literal
    -- renormalized lattice construction.
    compileRenormalizedLatticeFamily :
      G2CorrelatedDegreeOneBound types →
      G2RawHigherDegreeBound types →
      LiteralOneLoopCoefficientPositive types →
      PhysicalQuarticRemainderUniform types →
      RenormalizedLatticeFamily

    -- D+E: exact transfer squares plus terminal gap and uniform loss budget
    -- produce the cutoff-uniform lattice transfer theory.
    compileUniformTransferTheory :
      RenormalizedLatticeFamily →
      LiteralWilsonKernelNaturality types →
      LiteralTemporalTraceNaturality types →
      TerminalPhysicalWilsonTransferGap types →
      CutoffUniformPhysicalFeshbachLossBudget types →
      UniformTransferTheory

    -- F: scale increment + tightness + uniqueness produce one actual continuum
    -- family, rather than an untracked collection of subsequences.
    compileContinuumSchwingerFamily :
      UniformTransferTheory →
      PhysicalRenormalizedSchwingerScaleIncrementUniform types →
      RenormalizedYangMillsSchwingerTightness types →
      YangMillsContinuumOSUniqueLimit types →
      ContinuumSchwingerFamily

    -- G: the same continuum family must carry both the non-Gaussian witness
    -- and the physical clustering estimate.  This prevents two unrelated
    -- continuum limits from discharging nontriviality and mass scale.
    compileInteractingClusteredContinuumYM :
      ContinuumSchwingerFamily →
      PhysicalContinuumFourthCumulantLowerBound types →
      PhysicalUniformExponentialClustering types →
      InteractingClusteredContinuumYM

    -- These final two arrows are intended to be instantiated entirely by
    -- already-proved OS reconstruction / spectral closure / Clay-facing
    -- identification.  They are not additional physical producer slots.
    reconstructOSWightmanEndpoint :
      InteractingClusteredContinuumYM → OSWightmanEndpoint

    identifySU2ClayConclusion :
      OSWightmanEndpoint → SU2ClayConclusion

open SU2BackwardsTheoremGraph public

------------------------------------------------------------------------
-- 3. Compile the hypothetical finished proof forwards from the explicit
-- physical producer package.  This is the single term future work must keep
-- typechecking while producer fields are progressively eliminated.
------------------------------------------------------------------------

renormalizedLatticeFromProducers :
  ∀ {types}
    (graph : SU2BackwardsTheoremGraph types) →
    SU2PhysicalProducers types →
  RenormalizedLatticeFamily graph
renormalizedLatticeFromProducers graph producers =
  compileRenormalizedLatticeFamily graph
    (g2CorrelatedDegreeOneBound producers)
    (g2RawHigherDegreeBound producers)
    (literalOneLoopCoefficientPositive producers)
    (physicalQuarticRemainderUniform producers)

uniformTransferFromProducers :
  ∀ {types}
    (graph : SU2BackwardsTheoremGraph types) →
    (producers : SU2PhysicalProducers types) →
  UniformTransferTheory graph
uniformTransferFromProducers graph producers =
  compileUniformTransferTheory graph
    (renormalizedLatticeFromProducers graph producers)
    (literalWilsonKernelNaturality producers)
    (literalTemporalTraceNaturality producers)
    (terminalPhysicalWilsonTransferGap producers)
    (cutoffUniformPhysicalFeshbachLossBudget producers)

continuumSchwingerFromProducers :
  ∀ {types}
    (graph : SU2BackwardsTheoremGraph types) →
    (producers : SU2PhysicalProducers types) →
  ContinuumSchwingerFamily graph
continuumSchwingerFromProducers graph producers =
  compileContinuumSchwingerFamily graph
    (uniformTransferFromProducers graph producers)
    (physicalRenormalizedSchwingerScaleIncrementUniform producers)
    (renormalizedYangMillsSchwingerTightness producers)
    (yangMillsContinuumOSUniqueLimit producers)

interactingClusteredContinuumFromProducers :
  ∀ {types}
    (graph : SU2BackwardsTheoremGraph types) →
    (producers : SU2PhysicalProducers types) →
  InteractingClusteredContinuumYM graph
interactingClusteredContinuumFromProducers graph producers =
  compileInteractingClusteredContinuumYM graph
    (continuumSchwingerFromProducers graph producers)
    (physicalContinuumFourthCumulantLowerBound producers)
    (physicalUniformExponentialClustering producers)

osWightmanEndpointFromProducers :
  ∀ {types}
    (graph : SU2BackwardsTheoremGraph types) →
    (producers : SU2PhysicalProducers types) →
  OSWightmanEndpoint graph
osWightmanEndpointFromProducers graph producers =
  reconstructOSWightmanEndpoint graph
    (interactingClusteredContinuumFromProducers graph producers)

su2ClayFromPhysicalProducers :
  ∀ {types}
    (graph : SU2BackwardsTheoremGraph types) →
    SU2PhysicalProducers types →
  SU2ClayConclusion graph
su2ClayFromPhysicalProducers graph producers =
  identifySU2ClayConclusion graph
    (osWightmanEndpointFromProducers graph producers)

------------------------------------------------------------------------
-- 4. Frontier arithmetic remains executable, but it is now secondary.
-- The compiler term above is authoritative: if a producer disappears, splits,
-- or needs stronger uniformity, its type changes and the graph must recompile.
------------------------------------------------------------------------

g2ProducerCount oneLoopProducerCount nonlinearRGProducerCount
  transferProducerCount latticeGapProducerCount continuumProducerCount
  endpointProducerCount : Nat
g2ProducerCount = 2
oneLoopProducerCount = 1
nonlinearRGProducerCount = 1
transferProducerCount = 2
latticeGapProducerCount = 2
continuumProducerCount = 3
endpointProducerCount = 2

backwardsCompilerPhysicalProducerCount : Nat
backwardsCompilerPhysicalProducerCount =
  g2ProducerCount + oneLoopProducerCount + nonlinearRGProducerCount
  + transferProducerCount + latticeGapProducerCount + continuumProducerCount
  + endpointProducerCount

backwardsCompilerPhysicalProducerCountExact :
  backwardsCompilerPhysicalProducerCount ≡ 13
backwardsCompilerPhysicalProducerCountExact = refl

su2BackwardsCompilerDefinitionLevel : ProofLevel
su2BackwardsCompilerDefinitionLevel = machineChecked

-- The theorem graph must next be instantiated from the concrete Round61/62
-- repository carriers.  Until that wiring is complete, the graph itself is a
-- typed target rather than evidence for the Clay theorem.
concreteSU2BackwardsTheoremGraphInstantiationLevel : ProofLevel
concreteSU2BackwardsTheoremGraphInstantiationLevel = conditional

-- The thirteen witnesses remain exactly the physical frontier inputs.
physicalSU2ProducerPackageLevel : ProofLevel
physicalSU2ProducerPackageLevel = conditional
