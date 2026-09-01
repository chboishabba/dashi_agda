module DASHI.Computation.SSSPThreeFrontierMinimumOrbitQuotientExact where

-- Exact finite Pull(M=1) model.
--
-- A three-element frontier has six linear extensions.  If the consumer asks
-- only for the minimum element, the order of the remaining two elements is a
-- two-element residual symmetry fibre.  The six extensions therefore collapse
-- into three minimum classes.  This is a genuine 6 -> 3 quotient arising from
-- consumer demand / orbit structure, not an identification of S3 with C6.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Nullary using (¬_)
open import DASHI.Algebra.Trit using (Trit; neg; zer; pos)

import DASHI.Computation.SSSPThreeFrontierLinearExtensionQuotientBidiExact as F3

------------------------------------------------------------------------
-- 1. Pull-one consumer: expose the minimum only.
------------------------------------------------------------------------

minimumOf : F3.LinearOrder3 → F3.Frontier3
minimumOf F3.abc = F3.a
minimumOf F3.acb = F3.a
minimumOf F3.bac = F3.b
minimumOf F3.bca = F3.b
minimumOf F3.cab = F3.c
minimumOf F3.cba = F3.c

minA-fibre : minimumOf F3.abc ≡ minimumOf F3.acb
minA-fibre = refl

minB-fibre : minimumOf F3.bac ≡ minimumOf F3.bca
minB-fibre = refl

minC-fibre : minimumOf F3.cab ≡ minimumOf F3.cba
minC-fibre = refl

abc≠acb : ¬ (F3.abc ≡ F3.acb)
abc≠acb ()

bac≠bca : ¬ (F3.bac ≡ F3.bca)
bac≠bca ()

cab≠cba : ¬ (F3.cab ≡ F3.cba)
cab≠cba ()

------------------------------------------------------------------------
-- 2. Three quotient classes admit an exact balanced-ternary codec.
--
-- The labels are a consumer codec only:
--   a-minimum -> neg, b-minimum -> zer, c-minimum -> pos.
-- No algorithmic meaning is assigned to the sign beyond this finite chart.
------------------------------------------------------------------------

minimumTrit : F3.Frontier3 → Trit
minimumTrit F3.a = neg
minimumTrit F3.b = zer
minimumTrit F3.c = pos

tritMinimum : Trit → F3.Frontier3
tritMinimum neg = F3.a
tritMinimum zer = F3.b
tritMinimum pos = F3.c

minimumCodecRoundTrip :
  (x : F3.Frontier3) → tritMinimum (minimumTrit x) ≡ x
minimumCodecRoundTrip F3.a = refl
minimumCodecRoundTrip F3.b = refl
minimumCodecRoundTrip F3.c = refl

tritCodecRoundTrip :
  (t : Trit) → minimumTrit (tritMinimum t) ≡ t
tritCodecRoundTrip neg = refl
tritCodecRoundTrip zer = refl
tritCodecRoundTrip pos = refl

pullOneObservation : F3.LinearOrder3 → Trit
pullOneObservation o = minimumTrit (minimumOf o)

pullOne-abc-acb :
  pullOneObservation F3.abc ≡ pullOneObservation F3.acb
pullOne-abc-acb = refl

pullOne-bac-bca :
  pullOneObservation F3.bac ≡ pullOneObservation F3.bca
pullOne-bac-bca = refl

pullOne-cab-cba :
  pullOneObservation F3.cab ≡ pullOneObservation F3.cba
pullOne-cab-cba = refl

------------------------------------------------------------------------
-- 3. The quotient retains three distinct consumer outcomes.
------------------------------------------------------------------------

neg≠zer : ¬ (neg ≡ zer)
neg≠zer ()

zer≠pos : ¬ (zer ≡ pos)
zer≠pos ()

neg≠pos : ¬ (neg ≡ pos)
neg≠pos ()

minimumClassesRemainSeparatedAB :
  ¬ (pullOneObservation F3.abc ≡ pullOneObservation F3.bac)
minimumClassesRemainSeparatedAB = neg≠zer

minimumClassesRemainSeparatedBC :
  ¬ (pullOneObservation F3.bac ≡ pullOneObservation F3.cab)
minimumClassesRemainSeparatedBC = zer≠pos

minimumClassesRemainSeparatedAC :
  ¬ (pullOneObservation F3.abc ≡ pullOneObservation F3.cab)
minimumClassesRemainSeparatedAC = neg≠pos

------------------------------------------------------------------------
-- 4. BIDI reading.
--
-- Forward: six total orders -> three minimum observations.
-- Reverse: a minimum observation reopens a two-element residual tail-order
-- fibre.  Pull(M=1) therefore exposes exactly what its consumer requests and
-- retains the tail linear extension as residual information.
------------------------------------------------------------------------

data MinAResidual : Set where
  aThenBC aThenCB : MinAResidual

data MinBResidual : Set where
  bThenAC bThenCA : MinBResidual

data MinCResidual : Set where
  cThenAB cThenBA : MinCResidual

record MinimumOrbitQuotientBoundary : Set where
  constructor minimumOrbitQuotientBoundary
  field
    sixLinearExtensionsNeedNotRemainSeparated : Set
    threeMinimumClassesRemainSeparated : Set
    eachMinimumClassRetainsBinaryTailResidual : Set
    sourceSixCarrierIdentifiedWithC6 : Set

canonicalMinimumOrbitQuotientBoundary : MinimumOrbitQuotientBoundary
canonicalMinimumOrbitQuotientBoundary =
  minimumOrbitQuotientBoundary
    (F3.abc ≡ F3.acb → pullOneObservation F3.abc ≡ pullOneObservation F3.acb)
    (¬ (pullOneObservation F3.abc ≡ pullOneObservation F3.bac))
    MinAResidual
    (¬ (F3.LinearOrder3 ≡ F3.Frontier3))
