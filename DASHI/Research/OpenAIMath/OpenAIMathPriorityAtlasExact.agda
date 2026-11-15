module DASHI.Research.OpenAIMath.OpenAIMathPriorityAtlasExact where

open import Agda.Builtin.Bool using (Bool; false)
open import DASHI.Research.OpenAIMath.OpenAIMathUpstreamReceiptExact

data DASHIProgramme : Set where
  riemannHypothesis : DASHIProgramme
  birchSwinnertonDyer : DASHIProgramme
  hodge : DASHIProgramme
  yangMills : DASHIProgramme
  navierStokes : DASHIProgramme
  pVersusNP : DASHIProgramme
  ellipticCM : DASHIProgramme
  exceptionalRepresentation : DASHIProgramme
  quantumMathematics : DASHIProgramme
  fourierHarmonic : DASHIProgramme
  finiteCombinatorics : DASHIProgramme

data RelevanceClass : Set where
  directFrontier : RelevanceClass
  lemmaDonor : RelevanceClass
  independentCrossCheck : RelevanceClass
  backgroundOnly : RelevanceClass

priorityClass : DASHIProgramme → RelevanceClass
priorityClass riemannHypothesis = directFrontier
priorityClass birchSwinnertonDyer = directFrontier
priorityClass hodge = directFrontier
priorityClass yangMills = independentCrossCheck
priorityClass navierStokes = directFrontier
priorityClass pVersusNP = independentCrossCheck
priorityClass ellipticCM = directFrontier
priorityClass exceptionalRepresentation = lemmaDonor
priorityClass quantumMathematics = lemmaDonor
priorityClass fourierHarmonic = lemmaDonor
priorityClass finiteCombinatorics = lemmaDonor

priorityAtlasPromotesTheorems : Bool
priorityAtlasPromotesTheorems = false

priorityAtlasPaysSameObjectTransport : Bool
priorityAtlasPaysSameObjectTransport = false
