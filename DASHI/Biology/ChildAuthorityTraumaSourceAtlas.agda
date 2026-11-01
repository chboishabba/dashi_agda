module DASHI.Biology.ChildAuthorityTraumaSourceAtlas where

open import DASHI.Core.Prelude

import DASHI.Physics.Foundations.Round5SourceAtlas as Sources

------------------------------------------------------------------------
-- Bounded source atlas for child/caregiver/authority, institutional betrayal,
-- learning, predictive processing, decision control, and attractor geometry.
-- Each record states both the imported role and the promotion that is blocked.

unConventionSource : Sources.SourceRecord
unConventionSource =
  Sources.sourceRecord
    "United Nations General Assembly"
    "Convention on the Rights of the Child"
    "United Nations Treaty Series 1577, 3"
    1989
    "No DOI assigned; UN General Assembly resolution 44/25"
    "Supports the child's rights to be heard, freedom of thought/conscience/religion, evolving capacities, protection, and development."
    "The Convention is not promoted to a complete decision procedure for every conflict between child welfare, family responsibility, and religious freedom."

smithFreydInstitutionalBetrayalSource : Sources.SourceRecord
smithFreydInstitutionalBetrayalSource =
  Sources.sourceRecord
    "Carly Parnitzke Smith; Jennifer J. Freyd"
    "Institutional Betrayal"
    "American Psychologist 69(6), 575-587"
    2014
    "10.1037/a0037564"
    "Supports modelling harm amplification when a trusted or depended-upon institution fails to prevent, acknowledge, investigate, or repair wrongdoing."
    "Institutional betrayal theory is not promoted to proof that any named institution or disputed event satisfies the predicate without case-specific evidence."

maierSeligmanHelplessnessSource : Sources.SourceRecord
maierSeligmanHelplessnessSource =
  Sources.sourceRecord
    "Steven F. Maier; Martin E. P. Seligman"
    "Learned Helplessness at Fifty: Insights from Neuroscience"
    "Psychological Review 123(4), 349-367"
    2016
    "10.1037/rev0000033"
    "Supports treating controllability, available escape transitions, and later policy learning as distinct from the observed surface response alone."
    "Learned helplessness is not promoted to a diagnosis of a person or a universal explanation of compliance, silence, or non-action."

fristonFreeEnergySource : Sources.SourceRecord
fristonFreeEnergySource =
  Sources.sourceRecord
    "Karl Friston"
    "The Free-Energy Principle: A Unified Brain Theory?"
    "Nature Reviews Neuroscience 11, 127-138"
    2010
    "10.1038/nrn2787"
    "Supports a candidate bridge among prediction, action, learning, attention, and trajectories through state space."
    "The free-energy principle is not promoted to a completed clinical theory of trauma or to literal storage of propositions in body tissue."

bellmanDecisionSource : Sources.SourceRecord
bellmanDecisionSource =
  Sources.sourceRecord
    "Richard Bellman"
    "A Markovian Decision Process"
    "Indiana University Mathematics Journal 6(4), 679-684"
    1957
    "10.1512/iumj.1957.6.56038"
    "Supports sequential state-dependent policy selection rather than one-shot maximisation of raw option count."
    "The finite branch portfolio is not assumed Markovian unless the chosen state carrier actually preserves all decision-relevant history."

crauelFlandoliAttractorSource : Sources.SourceRecord
crauelFlandoliAttractorSource =
  Sources.sourceRecord
    "Hans Crauel; Franco Flandoli"
    "Attractors for Random Dynamical Systems"
    "Probability Theory and Related Fields 100(3), 365-393"
    1994
    "10.1007/BF01193705"
    "Supports treating attractors, invariant long-run structure, and stochastic transition dynamics as mathematically distinct from local activity."
    "The relational attractor vocabulary is not promoted to a calibrated stochastic dynamical system without an explicit state space and transition kernel."

canonicalChildAuthorityTraumaSources : List Sources.SourceRecord
canonicalChildAuthorityTraumaSources =
  unConventionSource
  ∷ smithFreydInstitutionalBetrayalSource
  ∷ maierSeligmanHelplessnessSource
  ∷ fristonFreeEnergySource
  ∷ bellmanDecisionSource
  ∷ crauelFlandoliAttractorSource
  ∷ []

sourceCount : List Sources.SourceRecord → Nat
sourceCount [] = 0
sourceCount (_ ∷ xs) = suc (sourceCount xs)

canonicalChildAuthorityTraumaSourceCount : Nat
canonicalChildAuthorityTraumaSourceCount =
  sourceCount canonicalChildAuthorityTraumaSources

canonicalChildAuthorityTraumaSourceCountIsSix :
  canonicalChildAuthorityTraumaSourceCount ≡ 6
canonicalChildAuthorityTraumaSourceCountIsSix = refl
