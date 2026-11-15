module DASHI.Cognition.Teleodynamics.ExceptionalE8Order3SameObjectSymplecticExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import DASHI.Algebra.Trit using (Trit; neg; zer; pos)

import DASHI.Cognition.Teleodynamics.ExceptionalE6Mod3FiniteGeometryExact as E6
import DASHI.Cognition.Teleodynamics.ExceptionalE6E8PluckerDualityExact as P

------------------------------------------------------------------------
-- E8 ORDER-THREE SAME-OBJECT QUOTIENT
--
-- The integral E8 simple-root lattice carries w = c^10 for a Coxeter element
-- c.  Local exact computation gives det(1-w)=81 and SNF
-- (1,1,1,1,3,3,3,3).  The explicit matrix U below kills (1-w) modulo 3,
-- has rank four, and has kernel index 81.  Hence its integer kernel is exactly
-- (1-w)E8 by containment plus equal index.
--
-- This owner writes the quotient map and an explicit section into the SAME
-- standard symplectic F3^4 used by ExceptionalE6E8PluckerDualityExact.
-- The equal-index lattice argument remains recorded as a local finite/integer
-- computation receipt rather than being promoted to an Agda kernel theorem.
------------------------------------------------------------------------

record E8SimpleRootMod3 : Set where
  constructor e8m3
  field
    x0 x1 x2 x3 x4 x5 x6 x7 : Trit
open E8SimpleRootMod3 public

infixl 6 _⊕_
_⊕_ : Trit → Trit → Trit
_⊕_ = P._⊕_

neg3 : Trit → Trit
neg3 = P.neg3

-- U =
-- [1 2 0 0 0 1 0 1]
-- [0 0 2 2 1 2 1 0]
-- [2 2 2 1 0 1 0 0]
-- [0 1 0 1 1 0 0 0]
-- over F3.
e8Order3Quotient : E8SimpleRootMod3 → P.Symplectic4
e8Order3Quotient x = P.s4
  (x0 x ⊕ neg3 (x1 x) ⊕ x5 x ⊕ x7 x)
  (neg3 (x2 x) ⊕ neg3 (x3 x) ⊕ x4 x ⊕ neg3 (x5 x) ⊕ x6 x)
  (neg3 (x0 x) ⊕ neg3 (x1 x) ⊕ neg3 (x2 x) ⊕ x3 x ⊕ x5 x)
  (x1 x ⊕ x3 x ⊕ x4 x)

-- R is a concrete right inverse of U:
-- [0 1 2 2]
-- [2 1 2 2]
-- [2 0 2 1]
-- [1 2 1 2]
-- [0 0 0 0]
-- [0 0 0 0]
-- [0 0 0 0]
-- [0 0 0 0].
e8Order3Section : P.Symplectic4 → E8SimpleRootMod3
e8Order3Section y = e8m3
  (P.b y ⊕ neg3 (P.c y) ⊕ neg3 (P.d y))
  (neg3 (P.a y) ⊕ P.b y ⊕ neg3 (P.c y) ⊕ neg3 (P.d y))
  (neg3 (P.a y) ⊕ neg3 (P.c y) ⊕ P.d y)
  (P.a y ⊕ neg3 (P.b y) ⊕ P.c y ⊕ neg3 (P.d y))
  zer zer zer zer

record E8Order3SameObjectComputationReceipt : Set where
  constructor e8-order3-same-object-computation-receipt
  field
    grade : E6.EvidenceGrade
    determinantOneMinusW : Nat
    mod3RankOneMinusW : Nat
    quotientRank : Nat
    kernelIndex : Nat
    imageIndex : Nat
    quotientKillsOneMinusW : Bool
    quotientIsWInvariant : Bool
    sectionIsRightInverse : Bool
    equalIndexKernelIdentification : Bool
    descendedAlternatingFormIsStandardSymplectic : Bool
    e8RootCount : Nat
    nonzeroQuotientClassesHit : Nat
    rootsPerNonzeroClass : Nat
    orderThreeRootOrbits : Nat
    eachOrbitIsOneQuotientClass : Bool
    distinctOrbitsGiveDistinctClasses : Bool
    localPythonReproduced : Bool
    provenance : String
open E8Order3SameObjectComputationReceipt public

canonicalE8Order3SameObjectComputationReceipt :
  E8Order3SameObjectComputationReceipt
canonicalE8Order3SameObjectComputationReceipt =
  e8-order3-same-object-computation-receipt
    E6.localFiniteComputation
    81 4 4 81 81
    true true true true true
    240 80 3 80 true true true
    "local exact computation from the E8 Cartan lattice: U(1-w)=0, Uw=U, UR=I4, equal index 81 gives ker(U)=(1-w)E8; R^T G(w-w^2)R is exactly the standard symplectic J"

record E8Order3SameObjectBoundary : Set where
  constructor e8-order3-same-object-boundary
  field
    explicitE8Mod3CarrierWritten : Bool
    explicitQuotientMapWritten : Bool
    explicitSectionWritten : Bool
    localKernelEqualityReceiptPresent : Bool
    localStandardSymplecticReceiptPresent : Bool
    rootOrbitToQuotientClassReceiptPresent : Bool
    integerKernelEqualityKernelProvedHere : Bool
    fullE8WeylActionOnQuotientClaimed : Bool

canonicalE8Order3SameObjectBoundary : E8Order3SameObjectBoundary
canonicalE8Order3SameObjectBoundary =
  e8-order3-same-object-boundary true true true true true true false false
