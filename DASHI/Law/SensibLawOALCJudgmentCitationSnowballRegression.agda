module DASHI.Law.SensibLawOALCJudgmentCitationSnowballRegression where

open import DASHI.Core.Prelude
open import Data.Empty using (⊥)

import DASHI.Law.SensibLawOALCJudgmentCitationSnowballExact as Snowball
import DASHI.Law.SensibLawProviderNeutralLegalQueryAlgebraExact as Query

boundaryExists : Set
boundaryExists = Snowball.OalcJudgmentCitationSnowballBoundary

boundaryPaid : boundaryExists
boundaryPaid = Snowball.canonicalOalcJudgmentCitationSnowballBoundary

waltonsUsesInverseCitedBy :
  Query.operation Snowball.waltonsCitedByTraversal
    ≡
  Query.citedByTraversalOperation
waltonsUsesInverseCitedBy =
  Snowball.waltonsCitedByUsesGraphTraversal

citationTraversalStillDoesNotProveFollowing :
  Query.CitationTraversalAutomaticallyMeansFollowing → ⊥
citationTraversalStillDoesNotProveFollowing =
  Query.citationTraversalDoesNotProveFollowing
