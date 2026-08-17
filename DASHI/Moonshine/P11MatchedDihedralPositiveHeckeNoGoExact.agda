module DASHI.Moonshine.P11MatchedDihedralPositiveHeckeNoGoExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Toshitsune Miyake,
-- "Modular Forms", Springer Monographs in Mathematics, Springer, 2006.
-- DOI: 10.1007/3-540-29593-3.
--
-- Fred Diamond and Jerry Shurman,
-- "A First Course in Modular Forms", Graduate Texts in Mathematics 228,
-- Springer, 2005.
-- DOI: 10.1007/978-0-387-27226-9.
--
-- DASHI CONTRIBUTION
--
-- Finite positivity no-go for the natural test lens
--
--   {epsilon} versus {rho1,...,rho5}.
--
-- A nonnegative six-state ell=2 correspondence descending to
-- B_11(2)=[[0,3],[2,1]] has only three epsilon->rho edges across five rho
-- sectors, hence misses at least one rho_i.  Each rho row has quotient
-- multiplicity two back to epsilon and total rho-block multiplicity one, so the
-- rho-block two-step return at a fixed rho_i is at most one.  At a missed rho_i
-- the diagonal of R2^2 is therefore <=1, whereas
--
--   R2^2 = R4 + 2 I
--
-- with nonnegative R4 forces every diagonal to be >=2.  Contradiction.
--
-- The record stores only necessary numerical consequences of a positive
-- correspondence; no adjacency matrix is fabricated.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

data FiveIndex : Set where
  i1 i2 i3 i4 i5 : FiveIndex

zeroAmongFiveWithSumThree :
  (a b c d e : Nat) →
  a + b + c + d + e ≡ 3 →
  FiveIndex
zeroAmongFiveWithSumThree 0 b c d e sumEq = i1
zeroAmongFiveWithSumThree (suc a) 0 c d e sumEq = i2
zeroAmongFiveWithSumThree (suc a) (suc b) 0 d e sumEq = i3
zeroAmongFiveWithSumThree (suc a) (suc b) (suc c) 0 e sumEq = i4
zeroAmongFiveWithSumThree (suc a) (suc b) (suc c) (suc d) 0 sumEq = i5
zeroAmongFiveWithSumThree
  (suc a) (suc b) (suc c) (suc d) (suc e) ()

------------------------------------------------------------------------
-- Definitionally normalized form of "<=1 cannot equal >=2".
------------------------------------------------------------------------

atMostOneCannotBePlusTwo :
  (r r4 : Nat) →
  r ≤ 1 →
  r ≡ 2 + r4 →
  ⊥
atMostOneCannotBePlusTwo 0 r4 bound ()
atMostOneCannotBePlusTwo 1 r4 bound ()
atMostOneCannotBePlusTwo (suc (suc r)) r4 () equality

record PositiveOneVsFiveR2SquareData : Set where
  field
    e1 e2 e3 e4 e5 : Nat
    epsilonRowDegree : e1 + e2 + e3 + e4 + e5 ≡ 3

    return1 return2 return3 return4 return5 : Nat
    return1AtMostOne : return1 ≤ 1
    return2AtMostOne : return2 ≤ 1
    return3AtMostOne : return3 ≤ 1
    return4AtMostOne : return4 ≤ 1
    return5AtMostOne : return5 ≤ 1

    r4diag1 r4diag2 r4diag3 r4diag4 r4diag5 : Nat

    -- Use 2+r4 rather than r4+2 so the lower-bound constructor shape is
    -- definitionally visible to Agda without invoking Nat commutativity.
    square1 : 2 * e1 + return1 ≡ 2 + r4diag1
    square2 : 2 * e2 + return2 ≡ 2 + r4diag2
    square3 : 2 * e3 + return3 ≡ 2 + r4diag3
    square4 : 2 * e4 + return4 ≡ 2 + r4diag4
    square5 : 2 * e5 + return5 ≡ 2 + r4diag5

open PositiveOneVsFiveR2SquareData public

missedIndexImpossible :
  (data : PositiveOneVsFiveR2SquareData) →
  (missed : FiveIndex) →
  ((missed ≡ i1 → e1 data ≡ 0)
   × (missed ≡ i2 → e2 data ≡ 0)
   × (missed ≡ i3 → e3 data ≡ 0)
   × (missed ≡ i4 → e4 data ≡ 0)
   × (missed ≡ i5 → e5 data ≡ 0)) →
  ⊥
missedIndexImpossible data i1 zeroProofs
  rewrite proj₁ zeroProofs refl =
    atMostOneCannotBePlusTwo
      (return1 data) (r4diag1 data)
      (return1AtMostOne data) (square1 data)
missedIndexImpossible data i2 zeroProofs
  rewrite proj₁ (proj₂ zeroProofs) refl =
    atMostOneCannotBePlusTwo
      (return2 data) (r4diag2 data)
      (return2AtMostOne data) (square2 data)
missedIndexImpossible data i3 zeroProofs
  rewrite proj₁ (proj₂ (proj₂ zeroProofs)) refl =
    atMostOneCannotBePlusTwo
      (return3 data) (r4diag3 data)
      (return3AtMostOne data) (square3 data)
missedIndexImpossible data i4 zeroProofs
  rewrite proj₁ (proj₂ (proj₂ (proj₂ zeroProofs))) refl =
    atMostOneCannotBePlusTwo
      (return4 data) (r4diag4 data)
      (return4AtMostOne data) (square4 data)
missedIndexImpossible data i5 zeroProofs
  rewrite proj₂ (proj₂ (proj₂ (proj₂ zeroProofs))) refl =
    atMostOneCannotBePlusTwo
      (return5 data) (r4diag5 data)
      (return5AtMostOne data) (square5 data)

record MissedRhoWitness (a b c d e : Nat) : Set where
  constructor missedRho
  field
    index : FiveIndex
    i1Zero : index ≡ i1 → a ≡ 0
    i2Zero : index ≡ i2 → b ≡ 0
    i3Zero : index ≡ i3 → c ≡ 0
    i4Zero : index ≡ i4 → d ≡ 0
    i5Zero : index ≡ i5 → e ≡ 0

missedRhoFromSumThree :
  (a b c d e : Nat) →
  a + b + c + d + e ≡ 3 →
  MissedRhoWitness a b c d e
missedRhoFromSumThree 0 b c d e eq =
  missedRho i1 refl (λ ()) (λ ()) (λ ()) (λ ())
missedRhoFromSumThree (suc a) 0 c d e eq =
  missedRho i2 (λ ()) refl (λ ()) (λ ()) (λ ())
missedRhoFromSumThree (suc a) (suc b) 0 d e eq =
  missedRho i3 (λ ()) (λ ()) refl (λ ()) (λ ())
missedRhoFromSumThree (suc a) (suc b) (suc c) 0 e eq =
  missedRho i4 (λ ()) (λ ()) (λ ()) refl (λ ())
missedRhoFromSumThree (suc a) (suc b) (suc c) (suc d) 0 eq =
  missedRho i5 (λ ()) (λ ()) (λ ()) (λ ()) refl
missedRhoFromSumThree
  (suc a) (suc b) (suc c) (suc d) (suc e) ()

positiveOneVsFiveLiftImpossible : PositiveOneVsFiveR2SquareData → ⊥
positiveOneVsFiveLiftImpossible data with
  missedRhoFromSumThree
    (e1 data) (e2 data) (e3 data) (e4 data) (e5 data)
    (epsilonRowDegree data)
... | missedRho missed i1z i2z i3z i4z i5z =
  missedIndexImpossible data missed (i1z , i2z , i3z , i4z , i5z)

record P11MatchedDihedralPositiveHeckeNoGoBoundary : Set where
  field
    constructiveFiveVsThreePigeonholeConstructed : Bool
    constructiveFiveVsThreePigeonholeConstructedIsTrue :
      constructiveFiveVsThreePigeonholeConstructed ≡ true

    positiveOneVsFiveNecessaryDataProvedEmpty : Bool
    positiveOneVsFiveNecessaryDataProvedEmptyIsTrue :
      positiveOneVsFiveNecessaryDataProvedEmpty ≡ true

    singletVsAllDoubletsCanCarryPositiveUnitalB2Lift : Bool
    singletVsAllDoubletsCanCarryPositiveUnitalB2LiftIsFalse :
      singletVsAllDoubletsCanCarryPositiveUnitalB2Lift ≡ false

    everyPossibleSixToTwoRepresentationInvariantRuledOutHere : Bool
    everyPossibleSixToTwoRepresentationInvariantRuledOutHereIsFalse :
      everyPossibleSixToTwoRepresentationInvariantRuledOutHere ≡ false

canonicalP11MatchedDihedralPositiveHeckeNoGoBoundary :
  P11MatchedDihedralPositiveHeckeNoGoBoundary
canonicalP11MatchedDihedralPositiveHeckeNoGoBoundary =
  record
    { constructiveFiveVsThreePigeonholeConstructed = true
    ; constructiveFiveVsThreePigeonholeConstructedIsTrue = refl
    ; positiveOneVsFiveNecessaryDataProvedEmpty = true
    ; positiveOneVsFiveNecessaryDataProvedEmptyIsTrue = refl
    ; singletVsAllDoubletsCanCarryPositiveUnitalB2Lift = false
    ; singletVsAllDoubletsCanCarryPositiveUnitalB2LiftIsFalse = refl
    ; everyPossibleSixToTwoRepresentationInvariantRuledOutHere = false
    ; everyPossibleSixToTwoRepresentationInvariantRuledOutHereIsFalse = refl
    }
