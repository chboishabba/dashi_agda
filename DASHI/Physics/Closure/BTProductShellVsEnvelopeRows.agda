module DASHI.Physics.Closure.BTProductShellVsEnvelopeRows where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; length; _∷_; [])

import DASHI.Physics.Closure.BTProductDiagonalGrowthArithmetic as Growth
import DASHI.Physics.Closure.BTGaussianDiagonalInputRows as Input

------------------------------------------------------------------------
-- Product-shell versus envelope bookkeeping rows.
--
-- The exactSphere and exactBall columns are exact diagonal product-tree
-- counts.  The envelope and shellWeightSurrogate columns are the
-- Gaussian-surface surrogate 8 * 42^r.  The relation tag below is
-- deliberately non-order-theoretic: this module records a finite ledger
-- for r=0..3 and asserts no inequality or convergence statement.

data RelationKind : Set where
  bookkeepingOnlyNoInequality :
    RelationKind

relationKindText :
  RelationKind →
  String
relationKindText bookkeepingOnlyNoInequality =
  "bookkeepingOnlyNoInequality"

record BTProductShellVsEnvelopeRow : Set where
  field
    radius :
      Nat

    sourceInputRow :
      Input.BTGaussianDiagonalInputRow

    radiusMatchesSource :
      radius ≡ Input.radius sourceInputRow

    exactSphere :
      Nat

    exactSphereMatchesGrowth :
      exactSphere ≡ Growth.diagonalProductSphereCount radius

    exactSphereMatchesSource :
      exactSphere ≡ Input.exactSphere sourceInputRow

    exactBall :
      Nat

    exactBallMatchesGrowth :
      exactBall ≡ Growth.diagonalProductBallCount radius

    exactBallMatchesSource :
      exactBall ≡ Input.exactBall sourceInputRow

    envelope :
      Nat

    envelopeMatchesGrowth :
      envelope ≡ Growth.diagonalEnvelope radius

    envelopeMatchesSource :
      envelope ≡ Input.envelope sourceInputRow

    shellWeightSurrogate :
      Nat

    shellWeightSurrogateMatchesSource :
      shellWeightSurrogate ≡ Input.shellWeightSurrogate sourceInputRow

    envelopeMatchesShellWeightSurrogate :
      envelope ≡ shellWeightSurrogate

    relationKind :
      RelationKind

    relationKindIsBookkeepingOnly :
      relationKind ≡ bookkeepingOnlyNoInequality

open BTProductShellVsEnvelopeRow public

shellVsEnvelopeRow0 :
  BTProductShellVsEnvelopeRow
shellVsEnvelopeRow0 =
  record
    { radius =
        0
    ; sourceInputRow =
        Input.diagonalInputRow0
    ; radiusMatchesSource =
        refl
    ; exactSphere =
        1
    ; exactSphereMatchesGrowth =
        refl
    ; exactSphereMatchesSource =
        refl
    ; exactBall =
        1
    ; exactBallMatchesGrowth =
        refl
    ; exactBallMatchesSource =
        refl
    ; envelope =
        8
    ; envelopeMatchesGrowth =
        refl
    ; envelopeMatchesSource =
        refl
    ; shellWeightSurrogate =
        8
    ; shellWeightSurrogateMatchesSource =
        refl
    ; envelopeMatchesShellWeightSurrogate =
        refl
    ; relationKind =
        bookkeepingOnlyNoInequality
    ; relationKindIsBookkeepingOnly =
        refl
    }

shellVsEnvelopeRow1 :
  BTProductShellVsEnvelopeRow
shellVsEnvelopeRow1 =
  record
    { radius =
        1
    ; sourceInputRow =
        Input.diagonalInputRow1
    ; radiusMatchesSource =
        refl
    ; exactSphere =
        96
    ; exactSphereMatchesGrowth =
        refl
    ; exactSphereMatchesSource =
        refl
    ; exactBall =
        180
    ; exactBallMatchesGrowth =
        refl
    ; exactBallMatchesSource =
        refl
    ; envelope =
        336
    ; envelopeMatchesGrowth =
        refl
    ; envelopeMatchesSource =
        refl
    ; shellWeightSurrogate =
        336
    ; shellWeightSurrogateMatchesSource =
        refl
    ; envelopeMatchesShellWeightSurrogate =
        refl
    ; relationKind =
        bookkeepingOnlyNoInequality
    ; relationKindIsBookkeepingOnly =
        refl
    }

shellVsEnvelopeRow2 :
  BTProductShellVsEnvelopeRow
shellVsEnvelopeRow2 =
  record
    { radius =
        2
    ; sourceInputRow =
        Input.diagonalInputRow2
    ; radiusMatchesSource =
        refl
    ; exactSphere =
        4032
    ; exactSphereMatchesGrowth =
        refl
    ; exactSphereMatchesSource =
        refl
    ; exactBall =
        11050
    ; exactBallMatchesGrowth =
        refl
    ; exactBallMatchesSource =
        refl
    ; envelope =
        14112
    ; envelopeMatchesGrowth =
        refl
    ; envelopeMatchesSource =
        refl
    ; shellWeightSurrogate =
        14112
    ; shellWeightSurrogateMatchesSource =
        refl
    ; envelopeMatchesShellWeightSurrogate =
        refl
    ; relationKind =
        bookkeepingOnlyNoInequality
    ; relationKindIsBookkeepingOnly =
        refl
    }

shellVsEnvelopeRow3 :
  BTProductShellVsEnvelopeRow
shellVsEnvelopeRow3 =
  record
    { radius =
        3
    ; sourceInputRow =
        Input.diagonalInputRow3
    ; radiusMatchesSource =
        refl
    ; exactSphere =
        169344
    ; exactSphereMatchesGrowth =
        refl
    ; exactSphereMatchesSource =
        refl
    ; exactBall =
        532862
    ; exactBallMatchesGrowth =
        refl
    ; exactBallMatchesSource =
        refl
    ; envelope =
        592704
    ; envelopeMatchesGrowth =
        refl
    ; envelopeMatchesSource =
        refl
    ; shellWeightSurrogate =
        592704
    ; shellWeightSurrogateMatchesSource =
        refl
    ; envelopeMatchesShellWeightSurrogate =
        refl
    ; relationKind =
        bookkeepingOnlyNoInequality
    ; relationKindIsBookkeepingOnly =
        refl
    }

canonicalBTProductShellVsEnvelopeRows :
  List BTProductShellVsEnvelopeRow
canonicalBTProductShellVsEnvelopeRows =
  shellVsEnvelopeRow0
  ∷ shellVsEnvelopeRow1
  ∷ shellVsEnvelopeRow2
  ∷ shellVsEnvelopeRow3
  ∷ []

canonicalBTProductShellVsEnvelopeRowCountIs4 :
  length canonicalBTProductShellVsEnvelopeRows ≡ 4
canonicalBTProductShellVsEnvelopeRowCountIs4 =
  refl

row0RelationIsBookkeepingOnly :
  relationKind shellVsEnvelopeRow0 ≡ bookkeepingOnlyNoInequality
row0RelationIsBookkeepingOnly =
  refl

row1RelationIsBookkeepingOnly :
  relationKind shellVsEnvelopeRow1 ≡ bookkeepingOnlyNoInequality
row1RelationIsBookkeepingOnly =
  refl

row2RelationIsBookkeepingOnly :
  relationKind shellVsEnvelopeRow2 ≡ bookkeepingOnlyNoInequality
row2RelationIsBookkeepingOnly =
  refl

row3RelationIsBookkeepingOnly :
  relationKind shellVsEnvelopeRow3 ≡ bookkeepingOnlyNoInequality
row3RelationIsBookkeepingOnly =
  refl
