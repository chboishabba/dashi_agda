{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YMClayVoyager2026CoverageExact where

-- SOURCE-CALIBRATED CHAPTER CROSSWALK (Voyager, 29 September 2026).
--
-- This module DOES NOT import a video as mathematical proof authority.
-- Its only mathematical theorems reuse the existing native Wilson and
-- Route-S owners, and a generic quantified uniform-gap implication.
-- Research results in 3D Yang--Mills--Higgs, classical 4D instantons,
-- and numerical lattice evidence are NOT 4D quantum-YM constructions.
--
-- Primary scientific owners and exact dates/DOIs are in
-- Docs/physics/YMClayVoyager20260929CoverageAudit.md.

open import Agda.Builtin.Bool using (false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Physics.YangMills.BalabanLiteralRationalSU2WilsonBoundedAlgebraExact as Literal
import DASHI.Physics.YangMills.YMClayDirectSourceOSMassGapFrontierExact as RouteS
import DASHI.Physics.YangMills.YMClayLiteralWilsonP2NativeMeasureExact as NativeP2

------------------------------------------------------------------------
-- Exact classification. A row is a scoped coverage receipt, never a
-- proof of the scientific claim named by that row.
------------------------------------------------------------------------

data CoverageState : Set where
  historicalContext : CoverageState
  existingFiniteTheorem : CoverageState
  existingConditionalCompiler : CoverageState
  existingCandidateReceipt : CoverageState
  externalResearchNotImported : CoverageState
  physicalSourceUnpaid : CoverageState

data PhysicalSector : Set where
  perturbativeRunning : PhysicalSector
  euclideanLattice : PhysicalSector
  continuumPureYM4D : PhysicalSector
  stochasticYMH3D : PhysicalSector
  stochasticYM2D : PhysicalSector
  classicalInstanton4D : PhysicalSector
  historicalBiographical : PhysicalSector

record ChapterReceipt : Set where
  constructor chapterReceipt
  field
    chapterSecond : Nat
    sector : PhysicalSector
    status : CoverageState
    existingOwnerOrOriginalSource : String
    exactBoundary : String

chapterReceipts : List ChapterReceipt
chapterReceipts =
  chapterReceipt 48 historicalBiographical historicalContext
    "Landau/Kapitza 1938-39 biography; historical primary sources"
    "Biographical facts do not create mathematical obligations"
  ∷ chapterReceipt 191 perturbativeRunning existingCandidateReceipt
    "DASHI/Physics/YangMills/BalabanClayOneLoopFlowRemainderExact.agda"
    "Landau pole belongs to QED's perturbative beta and is not an SU(N) YM no-go"
  ∷ chapterReceipt 364 perturbativeRunning existingFiniteTheorem
    "BalabanClayOneLoopFlowRemainderExact; Gross-Wilczek/Politzer 1973"
    "One-loop signed asymptotic running is not nonperturbative 4D existence"
  ∷ chapterReceipt 637 continuumPureYM4D existingConditionalCompiler
    "YMClayDirectSourceOSMassGapFrontierExact; Jaffe-Witten Clay"
    "Require a single actual nontrivial OS theory on R4 and a physical gap"
  ∷ chapterReceipt 823 euclideanLattice existingCandidateReceipt
    "Balaban dyadic/RG owners; Wilson 1974"
    "Finite blocking does not identify the weak-coupling continuum"
  ∷ chapterReceipt 1051 euclideanLattice existingFiniteTheorem
    "CompactLieLatticeGauge; BalabanLiteralRationalSU2WilsonBoundedAlgebraExact"
    "Gauge invariant Wilson loops require selected path/trace source equality"
  ∷ chapterReceipt 1288 euclideanLattice existingCandidateReceipt
    "CarrierAreaLawTheoremReceipt; StrongCouplingExpansionReceipt"
    "Strong-coupling area law is not pure-YM 4D Clay mass gap"
  ∷ chapterReceipt 1682 euclideanLattice existingCandidateReceipt
    "Wilson SU(N) finite lattice; Creutz 1979 numerical computations"
    "Monte Carlo finite numerical evidence is not a continuum theorem"
  ∷ chapterReceipt 1815 continuumPureYM4D physicalSourceUnpaid
    "BalabanClayT5PhysicalMeasureGramContinuityExact; R445 native P2"
    "Need selected a-to-zero same-measure limit, OS and nontriviality"
  ∷ chapterReceipt 2006 continuumPureYM4D existingConditionalCompiler
    "Balaban RG source owners; YMUniversalityClassReceipt"
    "Balaban UV bounds and infrared volume limit are separate obligations"
  ∷ chapterReceipt 2263 stochasticYMH3D externalResearchNotImported
    "Parisi-Wu 1981; Chandra-Chevyrev-Hairer-Shen 2024"
    "Local-in-stochastic-time gauge-orbit dynamics is not equilibrium"
  ∷ chapterReceipt 2432 stochasticYMH3D externalResearchNotImported
    "Chevyrev-Shen 2026, DOI 10.1007/s00205-025-02163-3"
    "Unique gauge-covariant mass counterterm does not give global 3D/4D measure"
  ∷ chapterReceipt 2432 stochasticYM2D externalResearchNotImported
    "Chevyrev-Shen 2026, invariant 2D YM Langevin measure"
    "2D established stationary measure is not 4D existence"
  ∷ chapterReceipt 2611 classicalInstanton4D externalResearchNotImported
    "Donaldson 1983; Freedman 1982; Hodge and instanton classical sector"
    "Classical anti-self-duality/moduli and exotic smooth R4 are not quantum YM gap"
  ∷ []

------------------------------------------------------------------------
-- REUSE ACTUAL SOURCE, NO DUPLICATED WILSON TRACE PROOF.
------------------------------------------------------------------------

nativeRationalWilsonBound :
  ∀ {n} (path : Literal.RationalWilsonPath n) →
  Literal.PointwiseUnitBounded (Literal.literalWilsonPathObservable path)
nativeRationalWilsonBound = Literal.literalWilsonPathPointwiseUnitBounded

nativeP2NeedsNoSupportDistance :
  NativeP2.p2SupportDistanceGeometryRequired ≡ false
nativeP2NeedsNoSupportDistance = refl

routeSStillNotClay :
  RouteS.clayPromotion ≡ false
routeSStillNotClay = RouteS.clayPromotionIsFalse

------------------------------------------------------------------------
-- A UNIFORM PHYSICAL GAP IMPLIES EVERY FINITE-VOLUME LOWER BOUND.
-- The reverse implication is invalid without a volume-uniform delta.
--
-- This abstract theorem cannot manufacture that delta, a common physical
-- Hamiltonian, or a continuum/infinite-volume spectral convergence.
------------------------------------------------------------------------

record UniformGap
    {Volume Energy : Set}
    (_≤_ : Energy → Energy → Set)
    (Positive : Energy → Set)
    (gap : Volume → Energy) : Set where
  field
    delta : Energy
    deltaPositive : Positive delta
    deltaBelowEveryGap : ∀ volume → _≤_ delta (gap volume)

uniformGapImpliesFinitePositivity :
  ∀ {Volume Energy : Set}
    (_≤_ : Energy → Energy → Set)
    (Positive : Energy → Set)
    (gap : Volume → Energy)
    (positiveMonotone : ∀ {x y} → _≤_ x y → Positive x → Positive y)
    (u : UniformGap _≤_ Positive gap) →
  ∀ volume → Positive (gap volume)
uniformGapImpliesFinitePositivity _≤_ Positive gap positiveMonotone u volume =
  positiveMonotone
    (UniformGap.deltaBelowEveryGap u volume)
    (UniformGap.deltaPositive u)

------------------------------------------------------------------------
-- STOCHASTIC-QUANTIZATION GATES. Local existence, global existence,
-- invariance and selection of a physical 4D measure are distinct DATA.
-- An arbitrary field named stationarity is not a proof of equilibrium:
-- it must state a law for an actual evolution of an actual distribution.
------------------------------------------------------------------------

record LocalStochasticFlow (Time State : Set) : Set₁ where
  field
    admissibleTime : Time → Set
    run : ∀ time → admissibleTime time → State → State

record InvariantStochasticMeasure
    {Time State : Set}
    (flow : LocalStochasticFlow Time State) : Set₁ where
  field
    globalTime : ∀ time → LocalStochasticFlow.admissibleTime flow time
    Distribution : Set
    pushForward : Time → Distribution → Distribution
    stationaryDistribution : Distribution
    invariantUnderEveryTime : ∀ time →
      pushForward time stationaryDistribution ≡ stationaryDistribution
    -- The law of pushForward must be identified with the SAME flow.
    sameFlowLaw : Set
    sameFlowLawWitness : sameFlowLaw

globalFromInvariantMeasure :
  ∀ {Time State}
    {flow : LocalStochasticFlow Time State} →
    (eq : InvariantStochasticMeasure flow) →
    ∀ time → LocalStochasticFlow.admissibleTime flow time
globalFromInvariantMeasure eq =
  InvariantStochasticMeasure.globalTime eq
