module DASHI.Core.PortableSemanticTranslationRealisationRegression where

import DASHI.Core.ConsumerIndexedTranslationRealisationExact as Translation
import DASHI.Core.PortableLoopInterpretationExact as Loop
import DASHI.Core.PortableSemanticTranslationRealisationBridgeExact as Bridge

jsTranslationAdequate :
  Translation.AdequateFor
    (Bridge.asTranslationRealisationSystem Loop.loopProblem Loop.jsSequential)
    Loop.canonicalInput
    tt
jsTranslationAdequate =
  Bridge.refinementGivesAdequateFor Loop.jsRefinesLogicalResult
