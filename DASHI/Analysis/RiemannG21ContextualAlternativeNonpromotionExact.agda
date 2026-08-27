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
    false refl
    false refl
    false refl
    false refl
    false refl
