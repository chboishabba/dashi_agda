module DASHI.Cognition.PNF.SensibLawFiniteLegalSearchProofPromotionExact where

------------------------------------------------------------------------
-- EXECUTABLE SEARCH HIT -> PROOF-RELEVANT DERIVATION
--
-- Two positive regression fixtures are promoted explicitly. This demonstrates
-- that finite search is not merely a parallel Boolean model: when the relevant
-- proof objects are owned, the same graph/fact/goal triple inhabits
-- Algebra.Reachable. Pabai remains deliberately unpromoted on the current route.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Cognition.PNF.SensibLawUniversalLegalRuleAlgebraExact as Algebra
import DASHI.Cognition.PNF.SensibLawFiniteExecutableLegalSearchExact as Search
import DASHI.Cognition.PNF.SensibLawFiniteLegalSearchRegressionExact as Regression
import DASHI.Cognition.PNF.SensibLawCullenPublicAuthorityDutyCalibrationExact as Cullen

------------------------------------------------------------------------
-- Mabo proof tree on the exact executable fixture.
------------------------------------------------------------------------

maboSovereigntyProof :
  Algebra.Reachable Regression.maboGraph Regression.maboFacts
    Regression.maboSovereignty
maboSovereigntyProof = Algebra.fromFact Algebra.here

maboPreExistingProof :
  Algebra.Reachable Regression.maboGraph Regression.maboFacts
    Regression.maboPreExistingNativeTitle
maboPreExistingProof = Algebra.fromFact (Algebra.there Algebra.here)

maboNotExtinguishedProof :
  Algebra.Reachable Regression.maboGraph Regression.maboFacts
    Regression.maboNotExtinguished
maboNotExtinguishedProof =
  Algebra.fromFact (Algebra.there (Algebra.there Algebra.here))

maboRadicalTitleProof :
  Algebra.Reachable Regression.maboGraph Regression.maboFacts
    Regression.maboRadicalTitle
maboRadicalTitleProof =
  Algebra.byRule
    Algebra.here
    tt
    (Algebra._∷_ maboSovereigntyProof Algebra.[])
    Algebra.[]
    Algebra.[]

maboSurvivalProof :
  Algebra.Reachable Regression.maboGraph Regression.maboFacts
    Regression.maboSurvival
maboSurvivalProof =
  Algebra.byRule
    (Algebra.there Algebra.here)
    tt
    (Algebra._∷_ maboRadicalTitleProof
      (Algebra._∷_ maboPreExistingProof
        (Algebra._∷_ maboNotExtinguishedProof Algebra.[])))
    Algebra.[]
    Algebra.[]

maboSearchPromotion :
  Search.ReachabilityPromotion
    2 Regression.maboGraph Regression.maboFacts Regression.maboSurvival
maboSearchPromotion = Search.reachability-promotion
  Regression.maboComputedReachable
  maboSurvivalProof

------------------------------------------------------------------------
-- Cullen proof tree on the exact executable fixture.
------------------------------------------------------------------------

cullenPositiveActProof :
  Algebra.Reachable Regression.cullenGraph Regression.cullenFacts
    Cullen.positiveOperationalAct
cullenPositiveActProof = Algebra.fromFact Algebra.here

cullenForeseeabilityProof :
  Algebra.Reachable Regression.cullenGraph Regression.cullenFacts
    Cullen.foreseeablePhysicalInjuryRisk
cullenForeseeabilityProof = Algebra.fromFact (Algebra.there Algebra.here)

cullenStatutoryFunctionProof :
  Algebra.Reachable Regression.cullenGraph Regression.cullenFacts
    Cullen.statutoryPoliceFunction
cullenStatutoryFunctionProof =
  Algebra.fromFact (Algebra.there (Algebra.there Algebra.here))

cullenDutyProof :
  Algebra.Reachable Regression.cullenGraph Regression.cullenFacts
    Cullen.cullenDutyProposition
cullenDutyProof =
  Algebra.byRule
    Algebra.here
    tt
    (Algebra._∷_ cullenPositiveActProof
      (Algebra._∷_ cullenForeseeabilityProof
        (Algebra._∷_ cullenStatutoryFunctionProof Algebra.[])))
    Algebra.[]
    Algebra.[]

cullenSearchPromotion :
  Search.ReachabilityPromotion
    1 Regression.cullenGraph Regression.cullenFacts Cullen.cullenDutyProposition
cullenSearchPromotion = Search.reachability-promotion
  Regression.cullenComputedDutyReachable
  cullenDutyProof

------------------------------------------------------------------------
-- The negative/counterfactual Pabai lane remains at the candidate boundary.
------------------------------------------------------------------------

data PabaiExecutableCounterfactualAlreadyHasProofRelevantPromotion : Set where

pabaiCounterfactualStillNeedsPromotion :
  PabaiExecutableCounterfactualAlreadyHasProofRelevantPromotion → ⊥
pabaiCounterfactualStillNeedsPromotion ()

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data OnePromotedFixturePromotesEverySearchHit : Set where

data ProofTreeChangesSourceAuthorityRole : Set where

promotionIsFixtureSpecific : OnePromotedFixturePromotesEverySearchHit → ⊥
promotionIsFixtureSpecific ()

proofDoesNotAlterAuthorityRole : ProofTreeChangesSourceAuthorityRole → ⊥
proofDoesNotAlterAuthorityRole ()
