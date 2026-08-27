module DASHI.Analysis.RiemannMixedChannelAlmostOrthogonalityExact where

------------------------------------------------------------------------
-- PURPOSE
--
-- Exact nonnegative bookkeeping for the only sign-indefinite loss exposed by
-- `RiemannWeilPairKernelFrobeniusExact`:
--
--   N_uv = (a_u . d_v)^2 + (b_u . c_v)^2.
--
-- The analytic frontier is to show that the aggregate mixed-channel budget
-- cannot absorb the positive diagonal Hermitian excess.  Once that statement
-- is supplied as `PairAlmostOrthogonality`, the target-pair retention theorem
-- is now derived here rather than being another independent premise.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)

sym : {A : Set} {x y : A} → x ≡ y → y ≡ x
sym refl = refl

trans : {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl yz = yz

dropSuc : {a b : Nat} → suc a ≡ suc b → a ≡ b
dropSuc refl = refl

congPlusLeft : {a b : Nat} → a ≡ b → (c : Nat) → c + a ≡ c + b
congPlusLeft refl c = refl

congPlusRight : {a b : Nat} → a ≡ b → (c : Nat) → a + c ≡ b + c
congPlusRight refl c = refl

+-assoc : (a b c : Nat) → (a + b) + c ≡ a + (b + c)
+-assoc zero b c = refl
+-assoc (suc a) b c rewrite +-assoc a b c = refl

+-zero-right : (a : Nat) → a + zero ≡ a
+-zero-right zero = refl
+-zero-right (suc a) rewrite +-zero-right a = refl

+-suc-right : (a b : Nat) → a + suc b ≡ suc (a + b)
+-suc-right zero b = refl
+-suc-right (suc a) b rewrite +-suc-right a b = refl

+-comm : (a b : Nat) → a + b ≡ b + a
+-comm zero b = sym (+-zero-right b)
+-comm (suc a) b
  rewrite +-comm a b
        | +-suc-right b a = refl

+-cancel-left : (c a b : Nat) → c + a ≡ c + b → a ≡ b
+-cancel-left zero a b eq = eq
+-cancel-left (suc c) a b eq =
  +-cancel-left c a b (dropSuc eq)

record MixedChannelGlobalLedger : Set where
  constructor mixedChannelGlobalLedger
  field
    positiveDiagonalEnergy : Nat
    mixedInterferenceBudget : Nat
    retainedGlobalExcess : Nat
    interferenceDecomposition :
      mixedInterferenceBudget + retainedGlobalExcess ≡ positiveDiagonalEnergy

open MixedChannelGlobalLedger public

record PairInsideDiagonalLedger (g : MixedChannelGlobalLedger) : Set where
  constructor pairInsideDiagonalLedger
  field
    targetPairDefect : Nat
    otherDiagonalEnergy : Nat
    pairInsideDiagonal :
      targetPairDefect + otherDiagonalEnergy ≡ positiveDiagonalEnergy g

open PairInsideDiagonalLedger public

-- Strong local almost-orthogonality certificate: all mixed interference can be
-- paid from the non-target diagonal reservoir, leaving an explicit margin.
record PairAlmostOrthogonality
  (g : MixedChannelGlobalLedger)
  (p : PairInsideDiagonalLedger g) : Set where
  constructor pairAlmostOrthogonality
  field
    orthogonalityMargin : Nat
    mixedPlusMarginIsOtherDiagonal :
      mixedInterferenceBudget g + orthogonalityMargin ≡ otherDiagonalEnergy p

open PairAlmostOrthogonality public

record RetainedPairCertificate
  (g : MixedChannelGlobalLedger)
  (p : PairInsideDiagonalLedger g) : Set where
  constructor retainedPairCertificate
  field
    retainedMargin : Nat
    retainedContainsPair :
      targetPairDefect p + retainedMargin ≡ retainedGlobalExcess g

------------------------------------------------------------------------
-- CONNECTION WE ALREADY HAVE.
--
-- M + R = P                global interference ledger
-- T + O = P                target pair inside diagonal energy
-- M + m = O                almost-orthogonality payment from other diagonal
-- ---------------------------------------------------------------
-- T + m = R                target pair survives in retained excess.
--
-- This is exact Nat cancellation; no further zeta analysis enters here.
------------------------------------------------------------------------

pairAlmostOrthogonalityRetainsTarget :
  (g : MixedChannelGlobalLedger) →
  (p : PairInsideDiagonalLedger g) →
  PairAlmostOrthogonality g p →
  RetainedPairCertificate g p
pairAlmostOrthogonalityRetainsTarget g p ao =
  retainedPairCertificate (orthogonalityMargin ao) retained
  where
  M : Nat
  M = mixedInterferenceBudget g

  R : Nat
  R = retainedGlobalExcess g

  T : Nat
  T = targetPairDefect p

  O : Nat
  O = otherDiagonalEnergy p

  m : Nat
  m = orthogonalityMargin ao

  mixedTargetMarginToTargetMixedMargin :
    M + (T + m) ≡ T + (M + m)
  mixedTargetMarginToTargetMixedMargin =
    trans
      (sym (+-assoc M T m))
      (trans
        (congPlusRight (+-comm M T) m)
        (+-assoc T M m))

  mixedTargetMarginToPositive :
    M + (T + m) ≡ positiveDiagonalEnergy g
  mixedTargetMarginToPositive =
    trans
      mixedTargetMarginToTargetMixedMargin
      (trans
        (congPlusLeft
          (PairAlmostOrthogonality.mixedPlusMarginIsOtherDiagonal ao)
          T)
        (pairInsideDiagonal p))

  mixedTargetMarginToMixedRetained :
    M + (T + m) ≡ M + R
  mixedTargetMarginToMixedRetained =
    trans
      mixedTargetMarginToPositive
      (sym (interferenceDecomposition g))

  retained : T + m ≡ R
  retained = +-cancel-left M (T + m) R mixedTargetMarginToMixedRetained

record AlmostOrthogonalityProducer : Set₁ where
  field
    ZeroPair : Set
    diagonalHermitianExcess : ZeroPair → Nat
    mixedCrossBudget : ZeroPair → ZeroPair → Nat
    aggregateDiagonalEnergy : Nat
    aggregateMixedBudget : Nat
    retainedExcess : Nat
    globalLedger : MixedChannelGlobalLedger
    targetPairEmbedding : ZeroPair → PairInsideDiagonalLedger globalLedger
    analyticInterferenceDomination :
      (rho : ZeroPair) →
      PairAlmostOrthogonality globalLedger (targetPairEmbedding rho)

retainedPairFromProducer :
  (p : AlmostOrthogonalityProducer) →
  (rho : AlmostOrthogonalityProducer.ZeroPair p) →
  RetainedPairCertificate
    (AlmostOrthogonalityProducer.globalLedger p)
    (AlmostOrthogonalityProducer.targetPairEmbedding p rho)
retainedPairFromProducer p rho =
  pairAlmostOrthogonalityRetainsTarget
    (AlmostOrthogonalityProducer.globalLedger p)
    (AlmostOrthogonalityProducer.targetPairEmbedding p rho)
    (AlmostOrthogonalityProducer.analyticInterferenceDomination p rho)

record MixedChannelAlmostOrthogonalityBoundary : Set where
  field
    mixedInterferenceLedgerConstructed : Bool
    targetPairInsideDiagonalLedgerConstructed : Bool
    retainedPairDerivedFromAlmostOrthogonality : Bool
    sourceMixedChannelIdentified : Bool
    actualZetaCrossSumEstimatedHere : Bool
    almostOrthogonalityProvedForZetaHere : Bool
    diagonalExcessDominatesInterferenceForZetaHere : Bool

mixedChannelAlmostOrthogonalityBoundary : MixedChannelAlmostOrthogonalityBoundary
mixedChannelAlmostOrthogonalityBoundary = record
  { mixedInterferenceLedgerConstructed = true
  ; targetPairInsideDiagonalLedgerConstructed = true
  ; retainedPairDerivedFromAlmostOrthogonality = true
  ; sourceMixedChannelIdentified = true
  ; actualZetaCrossSumEstimatedHere = false
  ; almostOrthogonalityProvedForZetaHere = false
  ; diagonalExcessDominatesInterferenceForZetaHere = false
  }
