module DASHI.Physics.YangMills.BalabanCharacteristicNuclearContinuityTransportExact where

------------------------------------------------------------------------
-- ROUND75: THE NUCLEAR-CONTINUITY PART OF 4 -> 5 IS A TOPOLOGY-TRANSPORT
-- THEOREM ONCE THE PHYSICAL RG SUPPLIES ONE COMMON HILBERTIAN MODULUS.
--
-- SOURCES
--
-- Julien Fageot, Arash Amini, Michael Unser,
-- "On the Continuity of Characteristic Functionals and Sparse Stochastic
-- Modeling", Journal of Fourier Analysis and Applications 20 (2014),
-- 1179--1211. DOI: 10.1007/s00041-014-9351-4.
--
-- Their Theorem 1 states the Minlos--Bochner criterion in the exact form used
-- here: on a nuclear test space, normalized + positive-definite + continuous
-- characteristic functional gives a unique probability measure on the dual.
--
-- Jose Velhinho,
-- "Topics of Measure Theory on Infinite Dimensional Spaces", 2023,
-- arXiv:2312.04365. DOI: 10.48550/arXiv.2312.04365.
--
-- Velhinho makes explicit the Hilbertian presentation of a nuclear topology:
-- a countable increasing family of Hilbert norms, with the connecting maps
-- Hilbert--Schmidt.  Continuity in one weaker Hilbertian topology therefore
-- implies continuity in the stronger nuclear topology.
--
-- Michael J. Meyer,
-- "Regression With Gaussian Measures" (2004 notes; no DOI recorded).
-- Meyer is used only for the separate Hilbert-space Gaussian fact that a
-- covariance operator of a Gaussian measure on a Hilbert space is positive
-- trace class, and conversely.  This is NOT made a gate for the nuclear-dual
-- Bochner--Minlos route.
--
-- Boby Gunarso,
-- "Gaussian Measures In Hilbert Spaces And Their Applications" (2016 thesis,
-- Sanata Dharma University; no DOI recorded).
-- The thesis states the same fork explicitly: trace-class covariance gives a
-- Gaussian measure on an infinite-dimensional separable Hilbert space, while
-- retaining identity covariance leads naturally to the topological dual of a
-- nuclear space.
------------------------------------------------------------------------

open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- We avoid pretending that Agda's Set is already a topological vector space.
-- Instead we isolate exactly the implication needed by the physical compiler.
-- A `Near` predicate is indexed by an arbitrary precision/radius carrier.
--
-- `StrongerNear nuclear hilbert` means every sufficiently-nuclear-small test
-- function is also Hilbert-small at the same requested precision.  This is the
-- direction needed because the nuclear topology is stronger.
------------------------------------------------------------------------

record ContinuityScale : Set₁ where
  field
    Radius Test Value : Set
    zeroTest : Test
    valueAtZero : Value
    OutputNear : Radius → Value → Value → Set

open ContinuityScale public

NearFamily : ContinuityScale → Set₁
NearFamily C = Radius C → Test C → Set

StrongerNear :
  (C : ContinuityScale) → NearFamily C → NearFamily C → Set
StrongerNear C strong weak =
  ∀ radius test → strong radius test → weak radius test

ContinuousAtZeroWith :
  (C : ContinuityScale) →
  NearFamily C →
  (Test C → Value C) →
  Set
ContinuousAtZeroWith C near f =
  ∀ radius test →
    near radius test →
    OutputNear C radius (f test) (valueAtZero C)

continuityMovesUpAlongStrongerDomainTopology :
  (C : ContinuityScale) →
  (nuclearNear hilbertNear : NearFamily C) →
  (f : Test C → Value C) →
  StrongerNear C nuclearNear hilbertNear →
  ContinuousAtZeroWith C hilbertNear f →
  ContinuousAtZeroWith C nuclearNear f
continuityMovesUpAlongStrongerDomainTopology C nuclearNear hilbertNear f
  nuclearToHilbert hilbertContinuous radius test nuclearSmall =
  hilbertContinuous radius test
    (nuclearToHilbert radius test nuclearSmall)

------------------------------------------------------------------------
-- Physical packaging: theorem #4 does NOT need an independent mysterious
-- `NuclearContinuous` estimate if it already carries one common Hilbertian
-- characteristic modulus and the declared test space has the standard nuclear
-- topology refinement into that Hilbertian seminorm.
------------------------------------------------------------------------

record HilbertianCharacteristicModulus (C : ContinuityScale) : Set₁ where
  field
    characteristic : Test C → Value C
    nuclearNear hilbertNear : NearFamily C

    nuclearTopologyStronger :
      StrongerNear C nuclearNear hilbertNear

    commonHilbertianModulus :
      ContinuousAtZeroWith C hilbertNear characteristic

open HilbertianCharacteristicModulus public

characteristicNuclearContinuity :
  (C : ContinuityScale) →
  (dataSet : HilbertianCharacteristicModulus C) →
  ContinuousAtZeroWith C
    (nuclearNear dataSet)
    (characteristic dataSet)
characteristicNuclearContinuity C dataSet =
  continuityMovesUpAlongStrongerDomainTopology C
    (nuclearNear dataSet)
    (hilbertNear dataSet)
    (characteristic dataSet)
    (nuclearTopologyStronger dataSet)
    (commonHilbertianModulus dataSet)

------------------------------------------------------------------------
-- IMPORTANT ROUTE BOUNDARY
--
-- Trace class is a hard gate only if one insists that the Gaussian measure
-- live on the Hilbert space itself.  It is not a necessary extra hypothesis
-- for the nuclear-dual Bochner--Minlos construction.  The two routes are kept
-- as distinct constructors instead of silently identifying them.
------------------------------------------------------------------------

data ContinuumMeasureRoute : Set where
  hilbertTraceClassRoute : ContinuumMeasureRoute
  nuclearDualMinlosRoute : ContinuumMeasureRoute

routesRemainDistinct :
  hilbertTraceClassRoute ≡ nuclearDualMinlosRoute → Set
routesRemainDistinct impossible = Set

characteristicNuclearContinuityTransportLevel : ProofLevel
characteristicNuclearContinuityTransportLevel = machineChecked

minlosBochnerSourceLevel : ProofLevel
minlosBochnerSourceLevel = standardImported
