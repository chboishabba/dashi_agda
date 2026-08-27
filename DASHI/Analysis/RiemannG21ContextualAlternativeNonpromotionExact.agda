module DASHI.Analysis.RiemannG21ContextualAlternativeNonpromotionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- SOURCE
--
-- Xinhe Jiang, Armin Hochrainer, Jaroslav Kysela, Manuel Erhard,
-- Xuemei Gu, Ya Yu, Anton Zeilinger,
-- "Subjective nature of path information in quantum mechanics",
-- Nature Communications 17, 2433 (2026).
-- DOI: 10.1038/s41467-026-69034-7.
--
-- BOUNDED ROLE
--
-- The experiment uses three indistinguishable SPDC sources and shows that the
-- same objective coherent-amplitude description admits different valid
-- groupings into alternatives.  The resulting which-source narratives can be
-- incompatible even though each grouping obeys the same duality formalism.
-- The paper also warns that zero amplitude assigned to a grouped alternative
-- must not automatically be interpreted as absence of all underlying source
-- contributions in the larger coherent system.
--
-- G21 uses this only as an observer/decomposition NONPROMOTION boundary:
-- a chosen decomposition, quotient coordinate, or channel grouping is not by
-- itself a privileged ontology of underlying contributions.  Nothing in this
-- module supplies a Riemann-zeta theorem, a pole-rank theorem, an explicit-
-- formula identity, or an RH implication.
------------------------------------------------------------------------

record SourceReference : Set where
  constructor sourceReference
  field
    authors : String
    title : String
    venue : String
    year : Nat
    doi : String
    boundedRole : String

open SourceReference public

jiangEtAl2026 : SourceReference
jiangEtAl2026 =
  sourceReference
    "Xinhe Jiang; Armin Hochrainer; Jaroslav Kysela; Manuel Erhard; Xuemei Gu; Ya Yu; Anton Zeilinger"
    "Subjective nature of path information in quantum mechanics"
    "Nature Communications 17:2433"
    2026
    "10.1038/s41467-026-69034-7"
    "Experimental source for contextual decomposition of coherent alternatives and the nonpromotion from grouped amplitude/path-information coordinates to unique physical origin."

------------------------------------------------------------------------
-- Generic context-indexed decomposition interface.
------------------------------------------------------------------------

record ContextualAlternativeDescription : Set₁ where
  field
    PhysicalSystem Context Alternative Amplitude Observation : Set
    system : PhysicalSystem
    alternatives : Context → Alternative → Set
    amplitude : Context → Alternative → Amplitude
    aggregateObservation : Context → Observation

    SamePhysicalDescription : Context → Context → Set
    IncompatibleOriginNarrative : Context → Context → Set

    sameObjectiveSystemAcrossContexts :
      (c₁ c₂ : Context) → SamePhysicalDescription c₁ c₂ → Set

    incompatibleNarrativesCanShareObjectiveDescription :
      (c₁ c₂ : Context) →
      SamePhysicalDescription c₁ c₂ →
      IncompatibleOriginNarrative c₁ c₂ →
      Set

open ContextualAlternativeDescription public

------------------------------------------------------------------------
-- Finite exact witness mirroring the source's grouping logic.
--
-- Context AB|C groups NL1+NL2 as one alternative and NL3 as the other.
-- Context A|BC groups NL1 as one alternative and NL2+NL3 as the other.
-- At the balanced phase setting phi_A = phi_C = pi, the paper's grouped
-- amplitudes alpha = a exp(i phi_A)+b and beta=b+c exp(i phi_C) can both
-- vanish.  If one illegitimately promotes each grouped zero to a unique-origin
-- narrative, the first partition points to NL3 while the second points to NL1.
-- We encode only that finite incompatibility pattern, not the optical numbers.
------------------------------------------------------------------------

data ThreeSourceSetup : Set where
  sameThreeCrystalExperiment : ThreeSourceSetup

data GroupingContext : Set where
  groupingABGivenC groupingAGivenBC : GroupingContext

data GroupedAlternative : Set where
  groupedAB sourceC sourceA groupedBC : GroupedAlternative

data AmplitudeStatus : Set where
  groupedAmplitudeZero remainingAmplitudeNonzero : AmplitudeStatus

data OriginNarrative : Set where
  naiveOriginNL3 naiveOriginNL1 : OriginNarrative

contextAlternative : GroupingContext → GroupedAlternative → Set
contextAlternative groupingABGivenC groupedAB = ⊤
contextAlternative groupingABGivenC sourceC = ⊤
contextAlternative groupingABGivenC _ = ⊥
contextAlternative groupingAGivenBC sourceA = ⊤
contextAlternative groupingAGivenBC groupedBC = ⊤
contextAlternative groupingAGivenBC _ = ⊥

contextAmplitude : GroupingContext → GroupedAlternative → AmplitudeStatus
contextAmplitude groupingABGivenC groupedAB = groupedAmplitudeZero
contextAmplitude groupingABGivenC sourceC = remainingAmplitudeNonzero
contextAmplitude groupingABGivenC _ = groupedAmplitudeZero
contextAmplitude groupingAGivenBC sourceA = remainingAmplitudeNonzero
contextAmplitude groupingAGivenBC groupedBC = groupedAmplitudeZero
contextAmplitude groupingAGivenBC _ = groupedAmplitudeZero

naiveNarrative : GroupingContext → OriginNarrative
naiveNarrative groupingABGivenC = naiveOriginNL3
naiveNarrative groupingAGivenBC = naiveOriginNL1

naiveNarrativesDiffer :
  naiveNarrative groupingABGivenC ≡ naiveNarrative groupingAGivenBC → ⊥
naiveNarrativesDiffer ()

contextGroupingsDiffer : groupingABGivenC ≡ groupingAGivenBC → ⊥
contextGroupingsDiffer ()

firstGroupingHasZeroCombinedAmplitude :
  contextAmplitude groupingABGivenC groupedAB ≡ groupedAmplitudeZero
firstGroupingHasZeroCombinedAmplitude = refl

secondGroupingHasZeroCombinedAmplitude :
  contextAmplitude groupingAGivenBC groupedBC ≡ groupedAmplitudeZero
secondGroupingHasZeroCombinedAmplitude = refl

record ThreeSourceContextualWitness : Set where
  constructor threeSourceContextualWitness
  field
    physicalSetup : ThreeSourceSetup
    firstContext secondContext : GroupingContext
    firstContextIsABGivenC : firstContext ≡ groupingABGivenC
    secondContextIsAGivenBC : secondContext ≡ groupingAGivenBC
    samePhysicalSetupAcrossGroupings : physicalSetup ≡ sameThreeCrystalExperiment
    firstGroupedZero :
      contextAmplitude firstContext groupedAB ≡ groupedAmplitudeZero
    secondGroupedZero :
      contextAmplitude secondContext groupedBC ≡ groupedAmplitudeZero
    naiveOriginInterpretationsIncompatible :
      naiveNarrative firstContext ≡ naiveNarrative secondContext → ⊥

canonicalThreeSourceContextualWitness : ThreeSourceContextualWitness
canonicalThreeSourceContextualWitness =
  threeSourceContextualWitness
    sameThreeCrystalExperiment
    groupingABGivenC
    groupingAGivenBC
    refl
    refl
    refl
    refl
    refl
    naiveNarrativesDiffer

------------------------------------------------------------------------
-- Nonpromotion ledger used by G21.
------------------------------------------------------------------------

record AlternativeNonpromotionBoundary : Set where
  constructor alternativeNonpromotionBoundary
  field
    decompositionDependsOnSpecifiedContext : Bool
    decompositionDependsOnSpecifiedContextIsTrue :
      decompositionDependsOnSpecifiedContext ≡ true

    multipleValidAlternativeGroupingsCanExist : Bool
    multipleValidAlternativeGroupingsCanExistIsTrue :
      multipleValidAlternativeGroupingsCanExist ≡ true

    exactThreeSourceContextualWitnessConstructed : Bool
    exactThreeSourceContextualWitnessConstructedIsTrue :
      exactThreeSourceContextualWitnessConstructed ≡ true

    zeroGroupedAmplitudeImpliesNoUnderlyingContribution : Bool
    zeroGroupedAmplitudeImpliesNoUnderlyingContributionIsFalse :
      zeroGroupedAmplitudeImpliesNoUnderlyingContribution ≡ false

    sampledChannelIsPrivilegedUnderlyingOntology : Bool
    sampledChannelIsPrivilegedUnderlyingOntologyIsFalse :
      sampledChannelIsPrivilegedUnderlyingOntology ≡ false

    quotientCoordinateIsUniquePhysicalOrigin : Bool
    quotientCoordinateIsUniquePhysicalOriginIsFalse :
      quotientCoordinateIsUniquePhysicalOrigin ≡ false

    paperProvesG21PoleRank : Bool
    paperProvesG21PoleRankIsFalse : paperProvesG21PoleRank ≡ false

    paperProvesRiemannHypothesis : Bool
    paperProvesRiemannHypothesisIsFalse : paperProvesRiemannHypothesis ≡ false

canonicalAlternativeNonpromotionBoundary : AlternativeNonpromotionBoundary
canonicalAlternativeNonpromotionBoundary =
  alternativeNonpromotionBoundary
    true refl
    true refl
    true refl
    false refl
    false refl
    false refl
    false refl
    false refl
