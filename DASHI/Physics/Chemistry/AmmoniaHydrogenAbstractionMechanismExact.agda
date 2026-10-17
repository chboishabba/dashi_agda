module DASHI.Physics.Chemistry.AmmoniaHydrogenAbstractionMechanismExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.List using (List; []; _∷_)
import DASHI.Core.AttributedSourceCore as Source
import DASHI.Physics.Chemistry.AtomicPeriodicTable369GenerativeExact as Atomic369

------------------------------------------------------------------------
-- 14NH3 + 1H -> 14NH2 + 1H2
--
-- This reaction is chosen because the literature pays substantially more than
-- a stoichiometric label: an analytical full-dimensional PES, stationary
-- points/reaction-path topology, VTST kinetics, and full-dimensional quantum
-- time-dependent wave-packet dynamics all exist for the same reaction family.
------------------------------------------------------------------------

espinosaCorchado2010PES : Source.AttributedSource
espinosaCorchado2010PES =
  Source.mkDOISource
    "Joaquin Espinosa-Garcia; Jose C. Corchado"
    "Analytical Potential Energy Surface and Kinetics of the NH3 + H -> NH2 + H2 Hydrogen Abstraction and the Ammonia Inversion Reactions"
    "Journal of Physical Chemistry A 114 (2010) 4455-4463"
    "2010"
    "10.1021/jp1001513"
    "https://doi.org/10.1021/jp1001513"
    Source.academicArticleSource
    "primary authority for the fitted analytical PES-2009, CCSD(T)/cc-pVTZ stationary-point/reaction-path input, abstraction/inversion path topology and VTST kinetics; not authority for DASHI atomic indexing"
    Source.publicAttribution

corchadoEspinosaYang2011Dynamics : Source.AttributedSource
corchadoEspinosaYang2011Dynamics =
  Source.mkDOISource
    "Jose C. Corchado; Joaquin Espinosa-Garcia; Minghui Yang"
    "Kinetics and dynamics of the NH3 + H -> NH2 + H2 reaction using transition state methods, quasi-classical trajectories, and quantum-mechanical scattering"
    "Journal of Chemical Physics 135 (2011) 014303"
    "2011"
    "10.1063/1.3605242"
    "https://doi.org/10.1063/1.3605242"
    Source.academicArticleSource
    "primary authority for full-dimensional initial-state-selected time-dependent wave-packet dynamics, quantum reaction probabilities, QCT/VTST comparison and thermal rates on the published PES; not a unique classical trajectory theorem"
    Source.publicAttribution

------------------------------------------------------------------------
-- Literal 369 atomic identities for a selected isotopologue model.
------------------------------------------------------------------------

protium : Atomic369.AtomicIndex
protium = Atomic369.atomicIndex 1 0 1

nitrogen14 : Atomic369.AtomicIndex
nitrogen14 = Atomic369.atomicIndex 7 7 7

reactantAtomicInventory369 : List Atomic369.AtomicIndex
reactantAtomicInventory369 =
  nitrogen14 ∷ protium ∷ protium ∷ protium ∷ protium ∷ []

productAtomicInventory369 : List Atomic369.AtomicIndex
productAtomicInventory369 =
  nitrogen14 ∷ protium ∷ protium ∷ protium ∷ protium ∷ []

data AbstractionStage : Set where
  separatedReactants entranceApproach saddleRegion exitSeparation separatedProducts : AbstractionStage

record AbstractionMechanism : Set where
  constructor abstractionMechanism
  field
    reaction : String
    reactants : String
    products : String
    transferredAtom : String
    brokenBond : String
    formedBond : String
    stageOrder : List AbstractionStage
    potentialEnergySurfaceAuthority : Source.AttributedSource
    dynamicsAuthority : Source.AttributedSource
    electronicStructureLevel : String
    kineticsMethod : String
    quantumDynamicsMethod : String
    permutationSymmetryReference : String

open AbstractionMechanism public

canonicalAbstractionMechanism : AbstractionMechanism
canonicalAbstractionMechanism =
  abstractionMechanism
    "14NH3 + 1H -> 14NH2 + 1H2"
    "NH3 + H"
    "NH2 + H2"
    "one ammonia H atom"
    "one N-H bond"
    "one H-H bond"
    (separatedReactants ∷ entranceApproach ∷ saddleRegion ∷ exitSeparation ∷ separatedProducts ∷ [])
    espinosaCorchado2010PES
    corchadoEspinosaYang2011Dynamics
    "PES fitted to high-level CCSD(T)/cc-pVTZ stationary points, reaction paths and reaction swaths"
    "variational transition-state theory with semiclassical transmission coefficients; QCT comparison"
    "full-dimensional initial-state-selected time-dependent wave-packet quantum scattering"
    "PES-2009 is symmetric under permutation of the ammonia H atoms"

record AbstractionBookkeeping : Set where
  constructor abstractionBookkeeping
  field
    nitrogenAtomsReactant nitrogenAtomsProduct : Nat
    hydrogenAtomsReactant hydrogenAtomsProduct : Nat
    neutralElectronCountReactant neutralElectronCountProduct : Nat
    reactant369Atoms product369Atoms : List Atomic369.AtomicIndex
    brokenNHBonds : Nat
    formedHHBonds : Nat

open AbstractionBookkeeping public

canonicalAbstractionBookkeeping : AbstractionBookkeeping
canonicalAbstractionBookkeeping =
  abstractionBookkeeping
    1 1
    4 4
    11 11
    reactantAtomicInventory369 productAtomicInventory369
    1 1

record ReactionWavepacketCarrier : Set₁ where
  constructor reactionWavepacketCarrier
  field
    Configuration : Set
    Amplitude : Set
    Time : Set
    initialState : Configuration
    propagate : Time → Configuration → Configuration
    amplitude : Configuration → Amplitude
    reactionProbabilityObservable : Configuration → Set
    sourceMethodReference : String

-- DASHI literal carrier for the source-described time-dependent wave-packet
-- method.  It records the mathematical job without pretending the paper's
-- numerical grid/coefficient arrays have been imported into this repository.
canonicalReactionWavepacketCarrier : ReactionWavepacketCarrier
canonicalReactionWavepacketCarrier =
  reactionWavepacketCarrier
    String String Nat
    "NH3 vibrational initial state + incoming H scattering state"
    (λ _ state → state)
    (λ state → state)
    (λ _ → ⊤)
    "Corchado-Espinosa-Garcia-Yang 2011 full-dimensional initial-state-selected time-dependent wave-packet calculation"

record AbstractionBoundary : Set where
  constructor abstractionBoundary
  field
    sourceBackedReactionIdentityPaid : Bool
    sourceBackedReactionIdentityPaidIsTrue : sourceBackedReactionIdentityPaid ≡ true
    sourceBackedAnalyticalPESPaid : Bool
    sourceBackedAnalyticalPESPaidIsTrue : sourceBackedAnalyticalPESPaid ≡ true
    sourceBackedReactionPathTopologyPaid : Bool
    sourceBackedReactionPathTopologyPaidIsTrue : sourceBackedReactionPathTopologyPaid ≡ true
    sourceBackedTimeDependentWavepacketDynamicsPaid : Bool
    sourceBackedTimeDependentWavepacketDynamicsPaidIsTrue :
      sourceBackedTimeDependentWavepacketDynamicsPaid ≡ true
    literal369AtomicReactionBindingPaid : Bool
    literal369AtomicReactionBindingPaidIsTrue : literal369AtomicReactionBindingPaid ≡ true
    atomChargeElectronBookkeepingPaid : Bool
    atomChargeElectronBookkeepingPaidIsTrue : atomChargeElectronBookkeepingPaid ≡ true
    uniqueMicroscopicTrajectoryDetermined : Bool
    uniqueMicroscopicTrajectoryDeterminedIsFalse : uniqueMicroscopicTrajectoryDetermined ≡ false
    sourceWavepacketCoefficientsImported : Bool
    sourceWavepacketCoefficientsImportedIsFalse : sourceWavepacketCoefficientsImported ≡ false
    PESIsExactBornOppenheimerSurface : Bool
    PESIsExactBornOppenheimerSurfaceIsFalse : PESIsExactBornOppenheimerSurface ≡ false

open AbstractionBoundary public

canonicalAbstractionBoundary : AbstractionBoundary
canonicalAbstractionBoundary =
  abstractionBoundary
    true refl true refl true refl true refl true refl true refl
    false refl false refl false refl
