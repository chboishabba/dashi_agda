module DASHI.Ontology.ConsumerRelativeRepresentationParityValidation where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Core.QueryFactorisationSufficiency as Factor
import DASHI.Core.ConsumerRelativeRepresentationParityExact as Parity
import DASHI.Core.ExpressiveComplexityNonAuthorityExact as Expressive
import DASHI.Core.SemanticPerturbationConsumerAdequacyExact as Perturb

------------------------------------------------------------------------
-- RED-FIRST VALIDATION SURFACE
--
-- These fixtures are deliberately domain-neutral.  Simple/full language,
-- multilingual renderings, child/adult rhetorical asymmetry, and Sophontic-
-- style semantic perturbations instantiate the same generic contracts.
------------------------------------------------------------------------

data State : Set where
  simpleSurface : State
  elaborateSurface : State
  changedFact : State

data Meaning : Set where
  baseMeaning : Meaning
  changedMeaning : Meaning

data Complexity : Set where
  lowComplexity : Complexity
  highComplexity : Complexity

data Query : Set where
  meaningQuery : Query

data Answer : Set where
  baseAnswer : Answer
  changedAnswer : Answer

meaning : State → Meaning
meaning simpleSurface = baseMeaning
meaning elaborateSurface = baseMeaning
meaning changedFact = changedMeaning

complexity : State → Complexity
complexity simpleSurface = lowComplexity
complexity elaborateSurface = highComplexity
complexity changedFact = lowComplexity

askMeaning : Query → State → Answer
askMeaning meaningQuery simpleSurface = baseAnswer
askMeaning meaningQuery elaborateSurface = baseAnswer
askMeaning meaningQuery changedFact = changedAnswer

questions : Factor.InquiryQuestionFamily State Query
questions = Factor.inquiryQuestionFamily (λ _ → Answer) askMeaning

meaningFactors : Factor.FactorsThrough questions meaning meaningQuery
meaningFactors = Factor.factorsThrough quotient proof
  where
    quotient : Meaning → Answer
    quotient baseMeaning = baseAnswer
    quotient changedMeaning = changedAnswer

    proof : (state : State) →
      Factor.ask questions meaningQuery state ≡ quotient (meaning state)
    proof simpleSurface = refl
    proof elaborateSurface = refl
    proof changedFact = refl

semanticSufficiency : Factor.StaticSufficient questions meaning
semanticSufficiency = Factor.staticSufficient λ { meaningQuery → meaningFactors }

sameMeaningDifferentExpression :
  Expressive.ExpressiveAsymmetryWitness meaning complexity
sameMeaningDifferentExpression =
  Expressive.expressiveAsymmetryWitness
    simpleSurface elaborateSurface refl (λ ())

eloquenceCannotChangeMeaningConsumer :
  Factor.ask questions meaningQuery simpleSurface
  ≡ Factor.ask questions meaningQuery elaborateSurface
eloquenceCannotChangeMeaningConsumer =
  Expressive.expressiveAsymmetryCannotChangeQuery
    meaningFactors sameMeaningDifferentExpression

semanticRepresentationIsConsumerParityWithItself :
  Parity.ConsumerParity questions meaning meaning
semanticRepresentationIsConsumerParityWithItself =
  Parity.consumerParity semanticSufficiency semanticSufficiency

changeMeaningPerturbation :
  Perturb.ConsumerPerturbation questions meaningQuery
changeMeaningPerturbation =
  Perturb.consumerPerturbation
    (λ { simpleSurface → changedFact
       ; elaborateSurface → changedFact
       ; changedFact → changedFact })
    (λ { baseAnswer → changedAnswer
       ; changedAnswer → changedAnswer })
    (λ { simpleSurface → refl
       ; elaborateSurface → refl
       ; changedFact → refl })

semanticChangeMovesConsumer :
  Factor.ask questions meaningQuery
    (Perturb.actState changeMeaningPerturbation simpleSurface)
  ≡ Perturb.actAnswer changeMeaningPerturbation
      (Factor.ask questions meaningQuery simpleSurface)
semanticChangeMovesConsumer =
  Perturb.commutes changeMeaningPerturbation simpleSurface
