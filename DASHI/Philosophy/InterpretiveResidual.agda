module DASHI.Philosophy.InterpretiveResidual where

open import Agda.Primitive using (Set₁)

------------------------------------------------------------------------
-- Translation and reconstruction are separated from the residual they leave.

record InterpretiveTranslation
       (Source Target Residual : Set) : Set₁ where
  field
    translate :
      Source →
      Target

    reconstruct :
      Target →
      Source

    residual :
      Source →
      Residual

    preservationWitness :
      Set

    lossWitness :
      Set

open InterpretiveTranslation public

record PhilosophicalResidualReceipt
       (HistoricalContext EmotionalForce Voice Ontology Evidence : Set) : Set₁ where
  field
    lostHistoricalContext :
      HistoricalContext

    alteredEmotionalForce :
      EmotionalForce

    excludedOrUntranslatedVoice :
      Voice

    incompatibleOntologicalAssumption :
      Ontology

    evidenceNotSurvivingTargetGrammar :
      Evidence

    incompletenessDeclared :
      Set

open PhilosophicalResidualReceipt public

record ResidualAwarePromotion
       (Admissibility ResidualReceipt Boundary Authority : Set) : Set₁ where
  field
    admissible :
      Admissibility

    residualRecorded :
      ResidualReceipt

    boundaryDeclared :
      Boundary

    authorityPresent :
      Authority

open ResidualAwarePromotion public
