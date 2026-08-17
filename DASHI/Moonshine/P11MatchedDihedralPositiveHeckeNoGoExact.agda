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
-- A finite positivity no-go for the natural test lens
--
--   {epsilon}  versus  {rho1,...,rho5}.
--
-- Suppose a nonnegative six-state ell=2 correspondence descends to
--
--        B_11(2) = [[0,3],[2,1]].
--
-- Then the epsilon row has exactly three total edges into the five rho sectors.
-- Hence at least one rho_i receives zero direct epsilon->rho_i multiplicity.
-- Every rho row has quotient multiplicity two back to epsilon and total
-- multiplicity one inside the rho block.  Consequently the rho-block two-step
-- return contribution at any fixed rho_i is at most one.
--
-- At an unhit rho_i the diagonal of R2^2 is therefore at most one.  But a
-- nonnegative full Hecke relation
--
--   R2^2 = R4 + 2 I
--
-- requires every diagonal entry of R2^2 to be at least two.  Contradiction.
--
-- The record below stores only these NECESSARY numerical consequences of such
-- a positive correspondence; no fabricated adjacency matrix is introduced.
-- Therefore its emptiness is a genuine no-go for this one-vs-five quotient.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

------------------------------------------------------------------------
-- Which rho coordinate is missed by the three epsilon edges?
------------------------------------------------------------------------

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
-- A number <=1 cannot equal a number >=2.
------------------------------------------------------------------------

atMostOneCannotBePlusTwo :
  (r r4 : Nat) →
  r ≤ 1 →
  r ≡ r4 + 2 →
  ⊥
atMostOneCannotBePlusTwo 0 r4 bound ()
atMostOneCannotBePlusTwo 1 r4 bound ()
atMostOneCannotBePlusTwo (suc (suc r)) r4 () equality

------------------------------------------------------------------------
-- Necessary diagonal data for a positive one-vs-five lift.
------------------------------------------------------------------------

record PositiveOneVsFiveR2SquareData : Set where
  field
    -- epsilon -> rho_i multiplicities; quotient row degree forces total 3.
    e1 e2 e3 e4 e5 : Nat
    epsilonRowDegree : e1 + e2 + e3 + e4 + e5 ≡ 3

    -- rho-block two-step return contributions.  Because every rho row has
    -- exactly one total rho-block edge, each such return contribution is <=1.
    return1 return2 return3 return4 return5 : Nat
    return1AtMostOne : return1 ≤ 1
    return2AtMostOne : return2 ≤ 1
    return3AtMostOne : return3 ≤ 1
    return4AtMostOne : return4 ≤ 1
    return5AtMostOne : return5 ≤ 1

    -- Nonnegative R4 diagonal entries.
    r4diag1 r4diag2 r4diag3 r4diag4 r4diag5 : Nat

    -- Diagonal prime-square equations.  The first term is the two-step path
    -- rho_i -> epsilon -> rho_i: quotient multiplicity 2 times e_i.
    square1 : 2 * e1 + return1 ≡ r4diag1 + 2
    square2 : 2 * e2 + return2 ≡ r4diag2 + 2
    square3 : 2 * e3 + return3 ≡ r4diag3 + 2
    square4 : 2 * e4 + return4 ≡ r4diag4 + 2
    square5 : 2 * e5 + return5 ≡ r4diag5 + 2

open PositiveOneVsFiveR2SquareData public

------------------------------------------------------------------------
-- Selecting the missed rho turns its square equation into return_i = r4+2,
-- contradicting return_i <=1.
------------------------------------------------------------------------

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

------------------------------------------------------------------------
-- A direct constructive missed-index package avoids any classical pigeonhole
-- principle: the five Nat inputs are pattern-matched exactly.
------------------------------------------------------------------------

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

------------------------------------------------------------------------
-- Boundary.
------------------------------------------------------------------------

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
