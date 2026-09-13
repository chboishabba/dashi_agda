module DASHI.GameTheory.GameTheorySourceAtlasExact where

open import DASHI.Core.Prelude

import DASHI.Biology.ConsciousAccessRound4SourceAtlas as R4
import DASHI.Biology.ConsciousAccessRound5SourceAtlas as Existing

------------------------------------------------------------------------
-- GAME THEORY SOURCE ATLAS
--
-- Source records identify the external mathematical/evolutionary result being
-- used or transcribed.  They do not themselves inhabit the formal theorem.
------------------------------------------------------------------------

nash1950Source : R4.SourceRecord
nash1950Source =
  R4.sourceRecord
    "John F. Nash Jr."
    "Equilibrium Points in n-Person Games"
    "Proceedings of the National Academy of Sciences"
    1950
    "10.1073/pnas.36.1.48"
    "Supports finite mixed-strategy equilibrium existence and the best-response fixed-point formulation."
    "A source citation does not itself inhabit the repo's finite mixed-Nash existence theorem."

kuhn1953Source : R4.SourceRecord
kuhn1953Source =
  R4.sourceRecord
    "Harold W. Kuhn"
    "Extensive Games and the Problem of Information"
    "Contributions to the Theory of Games II"
    1953
    "10.2307/j.ctv173f1fh.11"
    "Supports extensive-form histories, information structure and the distinction between extensive and normal forms."
    "The DASHI sequential carrier does not by itself prove perfect recall, behavioural-strategy equivalence, or subgame-perfect existence."

harsanyi1967Source : R4.SourceRecord
harsanyi1967Source =
  R4.sourceRecord
    "John C. Harsanyi"
    "Games with Incomplete Information Played by Bayesian Players, I-III Part I: The Basic Model"
    "Management Science"
    1967
    "10.1287/mnsc.14.3.159"
    "Supports incomplete-information games represented through a basic probability distribution, nature's draw, and player-partial information."
    "The finite common-prior DASHI carrier does not create posterior conditioning, infinite type hierarchies, or empirical truth authority."

harsanyi1968BayesianEquilibriumSource : R4.SourceRecord
harsanyi1968BayesianEquilibriumSource =
  R4.sourceRecord
    "John C. Harsanyi"
    "Games with Incomplete Information Played by Bayesian Players Part II: Bayesian Equilibrium Points"
    "Management Science"
    1968
    "10.1287/mnsc.14.5.320"
    "Supports the equilibrium relation between an incomplete-information game and its Bayes-equivalent representation."
    "A finite Bayesian-equilibrium carrier is not an existence or application theorem without the appropriate source-aligned hypotheses."

maynardSmithPrice1973Source : R4.SourceRecord
maynardSmithPrice1973Source =
  R4.sourceRecord
    "John Maynard Smith; George R. Price"
    "The Logic of Animal Conflict"
    "Nature"
    1973
    "10.1038/246015a0"
    "Supports evolutionary game analysis of strategy stability under biological competition."
    "Strategic equilibrium is not identified with moral value, observed historical fixation, or universal evolutionary optimality."

taylorJonker1978Source : R4.SourceRecord
taylorJonker1978Source =
  R4.sourceRecord
    "Peter D. Taylor; Leo B. Jonker"
    "Evolutionary Stable Strategies and Game Dynamics"
    "Mathematical Biosciences"
    1978
    "10.1016/0025-5564(78)90077-9"
    "Supports continuous and discrete population-frequency dynamics connecting reproductive success to evolving strategy mixtures."
    "The abstract DASHI invasion/frequency carriers do not become a calibrated biological trajectory or historical fixation theorem."

conwayFRACTRANSource : R4.SourceRecord
conwayFRACTRANSource = Existing.conwayFRACTRANSource

wolframMultiwaySource : R4.SourceRecord
wolframMultiwaySource = Existing.wolframMultiwaySource

canonicalGameTheorySources : List R4.SourceRecord
canonicalGameTheorySources =
  nash1950Source
  ∷ kuhn1953Source
  ∷ harsanyi1967Source
  ∷ harsanyi1968BayesianEquilibriumSource
  ∷ maynardSmithPrice1973Source
  ∷ taylorJonker1978Source
  ∷ conwayFRACTRANSource
  ∷ wolframMultiwaySource
  ∷ []

canonicalGameTheorySourceCount : Nat
canonicalGameTheorySourceCount = R4.listCount canonicalGameTheorySources

canonicalGameTheorySourceCountIsEight : canonicalGameTheorySourceCount ≡ 8
canonicalGameTheorySourceCountIsEight = refl
