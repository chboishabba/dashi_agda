module DASHI.Foundations.TernaryThirteenOriginalPantsObserverPunctureExact where

------------------------------------------------------------------------
-- Finite operational no-descent on the original TernaryPantsFrontier
-- 13-path carrier, plus preservation of the selected nonneutral
-- central trit under the *existing* cylinder/pants address iso.
--
-- This is a genuine pants-path observer theorem; it is NOT yet
-- the independently selected world-model or 144-site observer.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
import DASHI.Topology.TernaryPantsFrontierExact as Frontier
import DASHI.Foundations.TernaryThirteenFibreSplitExact as Word
import DASHI.Foundations.TernaryThirteenFibrePunctureExact as Puncture
import DASHI.Foundations.TernaryThirteenFibreObserverNonDescentExact as OriginalWord
import DASHI.Foundations.TernaryThirteenOriginalPantsFrontierBridgeExact as Pants
import DASHI.Core.ConsumerDescentMinimalObserverExact as Descent

pantsTwelvePrefix :
  Frontier.PantsPath 13 → Word.TritWord 12
pantsTwelvePrefix path =
  OriginalWord.prefixObserver (Pants.pantsToWord 13 path)

pantsThirteenthConsumer :
  Frontier.PantsPath 13 → Word.Trit
pantsThirteenthConsumer path =
  Puncture.lastTrit (Pants.pantsToWord 13 path)

neutralPants13 positivePants13 : Frontier.PantsPath 13
neutralPants13 = Pants.wordToPants 13 OriginalWord.neutralExtension
positivePants13 = Pants.wordToPants 13 OriginalWord.positiveExtension

neutralPantsPrefix :
  pantsTwelvePrefix neutralPants13 ≡ OriginalWord.baseTwelve
neutralPantsPrefix =
  trans
    (cong OriginalWord.prefixObserver
      (Pants.wordPantsRoundTrip 13 OriginalWord.neutralExtension))
    OriginalWord.neutralPrefixIsBase

positivePantsPrefix :
  pantsTwelvePrefix positivePants13 ≡ OriginalWord.baseTwelve
positivePantsPrefix =
  trans
    (cong OriginalWord.prefixObserver
      (Pants.wordPantsRoundTrip 13 OriginalWord.positiveExtension))
    OriginalWord.positivePrefixIsBase

neutralPantsLast :
  pantsThirteenthConsumer neutralPants13 ≡ Word.neutral
neutralPantsLast =
  trans
    (cong Puncture.lastTrit
      (Pants.wordPantsRoundTrip 13 OriginalWord.neutralExtension))
    OriginalWord.neutralLastIsNeutral

positivePantsLast :
  pantsThirteenthConsumer positivePants13 ≡ Word.positive
positivePantsLast =
  trans
    (cong Puncture.lastTrit
      (Pants.wordPantsRoundTrip 13 OriginalWord.positiveExtension))
    OriginalWord.positiveLastIsPositive

originalPantsCentralNonDescentWitness :
  Descent.ConsumerNonDescentWitness
    pantsTwelvePrefix pantsThirteenthConsumer
originalPantsCentralNonDescentWitness =
  Descent.consumerNonDescentWitness
    neutralPants13
    positivePants13
    (trans neutralPantsPrefix (sym positivePantsPrefix))
    (λ eq →
      OriginalWord.neutralIsNotPositive
        (trans
          (sym neutralPantsLast)
          (trans eq positivePantsLast)))

originalPantsCentralCannotFactor :
  Descent.FactorsThrough pantsTwelvePrefix pantsThirteenthConsumer →
  ⊥
originalPantsCentralCannotFactor =
  Descent.nonDescentWitnessBlocksFactorization
    originalPantsCentralNonDescentWitness

originalPantsCentralObserverInsufficient :
  Descent.ConsumerSufficient pantsTwelvePrefix
    pantsThirteenthConsumer → ⊥
originalPantsCentralObserverInsufficient =
  Descent.nonDescentWitnessBlocksSufficiency
    originalPantsCentralNonDescentWitness

pantsLastPuncture :
  Frontier.PantsPath 13 → Set
pantsLastPuncture path =
  ¬ (pantsThirteenthConsumer path ≡ Word.neutral)

pantsPunctureFromWord :
  (word : Word.TritWord 13) →
  ¬ (Puncture.lastTrit word ≡ Word.neutral) →
  pantsLastPuncture (Pants.wordToPants 13 word)
pantsPunctureFromWord word nonzero eq =
  nonzero
    (trans
      (sym
        (cong Puncture.lastTrit
          (Pants.wordPantsRoundTrip 13 word)))
      eq)

pantsPunctureToWord :
  (path : Frontier.PantsPath 13) →
  pantsLastPuncture path →
  ¬ (Puncture.lastTrit (Pants.pantsToWord 13 path)
    ≡ Word.neutral)
pantsPunctureToWord path punctured = punctured

-- At depth thirteen, the ORIGINAL cylinder/pants isomorphism
-- therefore transports the puncture with no cardinality assumption.
pantsPuncturePreservedUnderCylinder :
  (path : Frontier.PantsPath 13) →
  pantsLastPuncture path →
  pantsLastPuncture
    (Frontier.addressToPantsPath
      (Frontier.pantsPathToAddress path))
pantsPuncturePreservedUnderCylinder path punctured
  rewrite Frontier.pantsPathAddressRoundTrip path =
  punctured
