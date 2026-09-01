module DASHI.Computation.SSSPThreeFrontierLinearExtensionQuotientBidiExact where

-- Finite BIDI model of the sorting-barrier mechanism on a three-element
-- frontier.  There are six total linear orders (the S3-sized orbit), while
-- their full pair-relation observation is naturally a 3x3 = 9-cell ternary
-- sheet.  A consumer may inspect only a quotient of that sheet.
--
-- Important firewall: cardinality six does NOT identify this permutation
-- carrier with Base369.HexTruth/C6.  Likewise a nine-cell relation sheet is
-- not identified with Base369.NonaryTruth/C9.  Only proved symmetry shapes
-- are reused.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Nullary using (¬_)
open import DASHI.Algebra.Trit using (Trit; neg; zer; pos)
import DASHI.Foundations.BalancedTernaryStageSymmetryExact as BT

------------------------------------------------------------------------
-- 1. Three frontier vertices and all six linear extensions.
------------------------------------------------------------------------

data Frontier3 : Set where
  a b c : Frontier3

data LinearOrder3 : Set where
  abc acb bac bca cab cba : LinearOrder3

abc≠acb : ¬ (abc ≡ acb)
abc≠acb ()

------------------------------------------------------------------------
-- 2. Exact pair comparison supplied by each linear extension.
------------------------------------------------------------------------

compareIn : LinearOrder3 → Frontier3 → Frontier3 → Trit

compareIn abc a a = zer
compareIn abc a b = neg
compareIn abc a c = neg
compareIn abc b a = pos
compareIn abc b b = zer
compareIn abc b c = neg
compareIn abc c a = pos
compareIn abc c b = pos
compareIn abc c c = zer

compareIn acb a a = zer
compareIn acb a b = neg
compareIn acb a c = neg
compareIn acb b a = pos
compareIn acb b b = zer
compareIn acb b c = pos
compareIn acb c a = pos
compareIn acb c b = neg
compareIn acb c c = zer

compareIn bac a a = zer
compareIn bac a b = pos
compareIn bac a c = neg
compareIn bac b a = neg
compareIn bac b b = zer
compareIn bac b c = neg
compareIn bac c a = pos
compareIn bac c b = pos
compareIn bac c c = zer

compareIn bca a a = zer
compareIn bca a b = pos
compareIn bca a c = pos
compareIn bca b a = neg
compareIn bca b b = zer
compareIn bca b c = neg
compareIn bca c a = neg
compareIn bca c b = pos
compareIn bca c c = zer

compareIn cab a a = zer
compareIn cab a b = neg
compareIn cab a c = pos
compareIn cab b a = pos
compareIn cab b b = zer
compareIn cab b c = pos
compareIn cab c a = neg
compareIn cab c b = neg
compareIn cab c c = zer

compareIn cba a a = zer
compareIn cba a b = pos
compareIn cba a c = pos
compareIn cba b a = neg
compareIn cba b b = zer
compareIn cba b c = pos
compareIn cba c a = neg
compareIn cba c b = neg
compareIn cba c c = zer

------------------------------------------------------------------------
-- 3. Full nine-cell ternary relation sheet.
------------------------------------------------------------------------

record RelationSheet3x3 : Set where
  constructor relationSheet3x3
  field
    aa ab ac
      ba bb bc
      ca cb cc : Trit

open RelationSheet3x3 public

relationSheet : LinearOrder3 → RelationSheet3x3
relationSheet o =
  relationSheet3x3
    (compareIn o a a) (compareIn o a b) (compareIn o a c)
    (compareIn o b a) (compareIn o b b) (compareIn o b c)
    (compareIn o c a) (compareIn o c b) (compareIn o c c)

abcSheet : relationSheet abc ≡
  relationSheet3x3 zer neg neg pos zer neg pos pos zer
abcSheet = refl

acbSheet : relationSheet acb ≡
  relationSheet3x3 zer neg neg pos zer pos pos neg zer
acbSheet = refl

------------------------------------------------------------------------
-- 4. Consumer quotient: "is a certified before both other frontier points?"
--
-- The consumer requires a<b and a<c, but does not require b versus c.
-- Therefore abc and acb are distinct total orders with the same required
-- observation.  This is the first nontrivial finite frontier analogue of
-- avoiding a full sort.
------------------------------------------------------------------------

record AFrontierObservation : Set where
  constructor aFrontierObservation
  field
    aBeforeB : Trit
    aBeforeC : Trit

open AFrontierObservation public

observeAFrontier : LinearOrder3 → AFrontierObservation
observeAFrontier o =
  aFrontierObservation (compareIn o a b) (compareIn o a c)

abcAObservation :
  observeAFrontier abc ≡ aFrontierObservation neg neg
abcAObservation = refl

acbAObservation :
  observeAFrontier acb ≡ aFrontierObservation neg neg
acbAObservation = refl

linearExtensionsCollapseForAConsumer :
  observeAFrontier abc ≡ observeAFrontier acb
linearExtensionsCollapseForAConsumer = refl

------------------------------------------------------------------------
-- 5. The erased b/c coordinate is still present in the full nine-cell sheet.
------------------------------------------------------------------------

abcBC : bc (relationSheet abc) ≡ neg
abcBC = refl

acbBC : bc (relationSheet acb) ≡ pos
acbBC = refl

fullSheetStillSeparatesTailOrder :
  relationSheet abc ≡ relationSheet acb →
  neg ≡ pos
fullSheetStillSeparatesTailOrder refl = refl

neg≠pos : ¬ (neg ≡ pos)
neg≠pos ()

fullSheetsDistinct : ¬ (relationSheet abc ≡ relationSheet acb)
fullSheetsDistinct eq = neg≠pos (fullSheetStillSeparatesTailOrder eq)

------------------------------------------------------------------------
-- 6. Explicit tail-label symmetry exchanging the two collapsed extensions.
------------------------------------------------------------------------

swapBC : LinearOrder3 → LinearOrder3
swapBC abc = acb
swapBC acb = abc
swapBC bac = cab
swapBC cab = bac
swapBC bca = cba
swapBC cba = bca

swapBC-involutive : (o : LinearOrder3) → swapBC (swapBC o) ≡ o
swapBC-involutive abc = refl
swapBC-involutive acb = refl
swapBC-involutive bac = refl
swapBC-involutive cab = refl
swapBC-involutive bca = refl
swapBC-involutive cba = refl

AConsumerInvariantOnCanonicalTailSwap :
  observeAFrontier abc ≡ observeAFrontier (swapBC abc)
AConsumerInvariantOnCanonicalTailSwap = refl

------------------------------------------------------------------------
-- 7. Cross-pollination with the existing symmetry classifier.
--
-- The repository's canonical "two equal, one open" triad has S2 stabiliser.
-- We use it as the exact symmetry-shape witness for one unresolved exchange,
-- not as an identification of algorithm states with dialectical semantics.
------------------------------------------------------------------------

unresolvedTailPattern : BT.TriadPattern
unresolvedTailPattern = BT.twoPositiveOneOpen

unresolvedTailPatternHasS2 :
  BT.patternStabiliser unresolvedTailPattern ≡ BT.pairStabiliserS2
unresolvedTailPatternHasS2 = BT.stage2PatternHasS2

------------------------------------------------------------------------
-- 8. BIDI summary.
--
-- Forward: six total extensions -> nine-cell relation sheet -> consumer slice.
-- Reverse: the consumer slice reopens a residual two-element tail-order fibre.
------------------------------------------------------------------------

data TailOrderResidual : Set where
  bBeforeC cBeforeB : TailOrderResidual

recoverTailFromFullSheet : LinearOrder3 → TailOrderResidual
recoverTailFromFullSheet abc = bBeforeC
recoverTailFromFullSheet acb = cBeforeB
recoverTailFromFullSheet bac = bBeforeC
recoverTailFromFullSheet bca = bBeforeC
recoverTailFromFullSheet cab = cBeforeB
recoverTailFromFullSheet cba = cBeforeB

abcTailResidual : recoverTailFromFullSheet abc ≡ bBeforeC
abcTailResidual = refl

acbTailResidual : recoverTailFromFullSheet acb ≡ cBeforeB
acbTailResidual = refl

record AConsumerQuotientReceipt : Set where
  constructor aConsumerQuotientReceipt
  field
    sourceOrdersDistinct : ¬ (abc ≡ acb)
    consumerObservationsEqual : observeAFrontier abc ≡ observeAFrontier acb
    fullRelationsRemainDistinct : ¬ (relationSheet abc ≡ relationSheet acb)
    unresolvedTailCarriesS2Shape :
      BT.patternStabiliser unresolvedTailPattern ≡ BT.pairStabiliserS2

canonicalAConsumerQuotientReceipt : AConsumerQuotientReceipt
canonicalAConsumerQuotientReceipt =
  aConsumerQuotientReceipt
    abc≠acb
    linearExtensionsCollapseForAConsumer
    fullSheetsDistinct
    unresolvedTailPatternHasS2
