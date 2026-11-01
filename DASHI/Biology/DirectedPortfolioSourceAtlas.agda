module DASHI.Biology.DirectedPortfolioSourceAtlas where

open import DASHI.Core.Prelude

import DASHI.Physics.Foundations.Round5SourceAtlas as Sources

------------------------------------------------------------------------
-- Sources for information gain, submodular portfolio value, and finite
-- tail-risk adjustment.  Each citation is attached to a bounded formal role.

shannonInformationSource : Sources.SourceRecord
shannonInformationSource =
  Sources.sourceRecord
    "Claude E. Shannon"
    "A Mathematical Theory of Communication"
    "Bell System Technical Journal 27(3), 379-423"
    1948
    "10.1002/j.1538-7305.1948.tb01338.x"
    "Supports entropy and information gain as reductions in uncertainty rather than as synonyms for activity or novelty."
    "The finite Nat-valued information witnesses are not promoted to calibrated Shannon entropies without an explicit probability model and logarithmic measure."

nemhauserWolseySource : Sources.SourceRecord
nemhauserWolseySource =
  Sources.sourceRecord
    "George L. Nemhauser; Laurence A. Wolsey"
    "Best Algorithms for Approximating the Maximum of a Submodular Set Function"
    "Mathematics of Operations Research 3(3), 177-188"
    1978
    "10.1287/moor.3.3.177"
    "Supports distinguishing diminishing marginal returns from raw option count and motivates submodular portfolio structure."
    "No greedy approximation guarantee is imported unless monotonicity, submodularity, cardinality constraints, and oracle assumptions are separately proved."

rockafellarUryasevSource : Sources.SourceRecord
rockafellarUryasevSource =
  Sources.sourceRecord
    "R. Tyrrell Rockafellar; Stanislav Uryasev"
    "Optimization of Conditional Value-at-Risk"
    "The Journal of Risk 2(3), 21-41"
    2000
    "10.21314/jor.2000.038"
    "Supports retaining severe-loss or tail-risk information rather than ranking branches by expected or ordinary burden alone."
    "The finite tail-loss witness is not promoted to CVaR without a loss distribution, confidence level, and the required optimisation construction."

canonicalDirectedPortfolioSources : List Sources.SourceRecord
canonicalDirectedPortfolioSources =
  shannonInformationSource
  ∷ nemhauserWolseySource
  ∷ rockafellarUryasevSource
  ∷ []

sourceCount : List Sources.SourceRecord → Nat
sourceCount [] = 0
sourceCount (_ ∷ xs) = suc (sourceCount xs)

canonicalDirectedPortfolioSourceCount : Nat
canonicalDirectedPortfolioSourceCount =
  sourceCount canonicalDirectedPortfolioSources

canonicalDirectedPortfolioSourceCountIsThree :
  canonicalDirectedPortfolioSourceCount ≡ 3
canonicalDirectedPortfolioSourceCountIsThree = refl
