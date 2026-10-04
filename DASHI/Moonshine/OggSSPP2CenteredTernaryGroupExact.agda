module DASHI.Moonshine.OggSSPP2CenteredTernaryGroupExact where

------------------------------------------------------------------------
-- RECENTERING THE EXISTING C3 LAW AT THE SIGNED ZERO
--
-- Existing law:
--   TritTriTruthBridge.tritXor has identity Trit.neg, because it transports
--   Base369.triXor where tri-low is additive zero.
--
-- Signed / geometric convention:
--   Trit.zer is the distinguished centre and Trit.inv fixes zer while
--   exchanging neg <-> pos.
--
-- We conjugate the OLD group law by the cyclic translation
--
--   advance : neg -> zer -> pos -> neg.
--
-- The transported operation has:
--
--   * identity zer;
--   * additive inverse EXACTLY Trit.inv;
--   * exponent three;
--   * commutativity and associativity.
--
-- Componentwise, this makes Sheet9 a literal C3 x C3 group with identity
-- (zer,zer), aligned with the elliptic origin-centred chart.
--
-- This resolves the coordinate/basepoint mismatch. It does NOT yet prove
-- that the origin-centred E(F4) chart preserves elliptic addition.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import DASHI.Algebra.Trit as Trit
import DASHI.Algebra.TritTriTruthBridge as Bridge
import DASHI.Codec.TriadicPAdicCodec as Codec
import DASHI.Foundations.TernaryEndomorphismPhaseQuotientExact as Phase
import Base369 as Base

open Codec using ([]ᵥ; _∷ᵥ_)

advance : Trit.Trit → Trit.Trit
advance Trit.neg = Trit.zer
advance Trit.zer = Trit.pos
advance Trit.pos = Trit.neg

retreat : Trit.Trit → Trit.Trit
retreat Trit.neg = Trit.pos
retreat Trit.zer = Trit.neg
retreat Trit.pos = Trit.zer

advanceRetreat :
  (t : Trit.Trit) → advance (retreat t) ≡ t
advanceRetreat Trit.neg = refl
advanceRetreat Trit.zer = refl
advanceRetreat Trit.pos = refl

retreatAdvance :
  (t : Trit.Trit) → retreat (advance t) ≡ t
retreatAdvance Trit.neg = refl
retreatAdvance Trit.zer = refl
retreatAdvance Trit.pos = refl

centerAdd : Trit.Trit → Trit.Trit → Trit.Trit
centerAdd a b =
  advance (Bridge.tritXor (retreat a) (retreat b))

centerZero : Trit.Trit
centerZero = Trit.zer

centerAdd-left-zero :
  (a : Trit.Trit) → centerAdd centerZero a ≡ a
centerAdd-left-zero Trit.neg = refl
centerAdd-left-zero Trit.zer = refl
centerAdd-left-zero Trit.pos = refl

centerAdd-right-zero :
  (a : Trit.Trit) → centerAdd a centerZero ≡ a
centerAdd-right-zero Trit.neg = refl
centerAdd-right-zero Trit.zer = refl
centerAdd-right-zero Trit.pos = refl

centerAdd-comm :
  (a b : Trit.Trit) → centerAdd a b ≡ centerAdd b a
centerAdd-comm Trit.neg Trit.neg = refl
centerAdd-comm Trit.neg Trit.zer = refl
centerAdd-comm Trit.neg Trit.pos = refl
centerAdd-comm Trit.zer Trit.neg = refl
centerAdd-comm Trit.zer Trit.zer = refl
centerAdd-comm Trit.zer Trit.pos = refl
centerAdd-comm Trit.pos Trit.neg = refl
centerAdd-comm Trit.pos Trit.zer = refl
centerAdd-comm Trit.pos Trit.pos = refl

centerAdd-assoc :
  (a b c : Trit.Trit) →
  centerAdd a (centerAdd b c)
  ≡ centerAdd (centerAdd a b) c
centerAdd-assoc Trit.neg Trit.neg Trit.neg = refl
centerAdd-assoc Trit.neg Trit.neg Trit.zer = refl
centerAdd-assoc Trit.neg Trit.neg Trit.pos = refl
centerAdd-assoc Trit.neg Trit.zer Trit.neg = refl
centerAdd-assoc Trit.neg Trit.zer Trit.zer = refl
centerAdd-assoc Trit.neg Trit.zer Trit.pos = refl
centerAdd-assoc Trit.neg Trit.pos Trit.neg = refl
centerAdd-assoc Trit.neg Trit.pos Trit.zer = refl
centerAdd-assoc Trit.neg Trit.pos Trit.pos = refl
centerAdd-assoc Trit.zer Trit.neg Trit.neg = refl
centerAdd-assoc Trit.zer Trit.neg Trit.zer = refl
centerAdd-assoc Trit.zer Trit.neg Trit.pos = refl
centerAdd-assoc Trit.zer Trit.zer Trit.neg = refl
centerAdd-assoc Trit.zer Trit.zer Trit.zer = refl
centerAdd-assoc Trit.zer Trit.zer Trit.pos = refl
centerAdd-assoc Trit.zer Trit.pos Trit.neg = refl
centerAdd-assoc Trit.zer Trit.pos Trit.zer = refl
centerAdd-assoc Trit.zer Trit.pos Trit.pos = refl
centerAdd-assoc Trit.pos Trit.neg Trit.neg = refl
centerAdd-assoc Trit.pos Trit.neg Trit.zer = refl
centerAdd-assoc Trit.pos Trit.neg Trit.pos = refl
centerAdd-assoc Trit.pos Trit.zer Trit.neg = refl
centerAdd-assoc Trit.pos Trit.zer Trit.zer = refl
centerAdd-assoc Trit.pos Trit.zer Trit.pos = refl
centerAdd-assoc Trit.pos Trit.pos Trit.neg = refl
centerAdd-assoc Trit.pos Trit.pos Trit.zer = refl
centerAdd-assoc Trit.pos Trit.pos Trit.pos = refl

-- The major payoff: the pre-existing SIGN involution is now exactly inverse.
centerAdd-inverse :
  (a : Trit.Trit) →
  centerAdd a (Trit.inv a) ≡ centerZero
centerAdd-inverse Trit.neg = refl
centerAdd-inverse Trit.zer = refl
centerAdd-inverse Trit.pos = refl

centerAdd-inverse-left :
  (a : Trit.Trit) →
  centerAdd (Trit.inv a) a ≡ centerZero
centerAdd-inverse-left Trit.neg = refl
centerAdd-inverse-left Trit.zer = refl
centerAdd-inverse-left Trit.pos = refl

centerTripleZero :
  (a : Trit.Trit) →
  centerAdd (centerAdd a a) a ≡ centerZero
centerTripleZero Trit.neg = refl
centerTripleZero Trit.zer = refl
centerTripleZero Trit.pos = refl

centerInvAdd :
  (a b : Trit.Trit) →
  Trit.inv (centerAdd a b)
  ≡ centerAdd (Trit.inv a) (Trit.inv b)
centerInvAdd Trit.neg Trit.neg = refl
centerInvAdd Trit.neg Trit.zer = refl
centerInvAdd Trit.neg Trit.pos = refl
centerInvAdd Trit.zer Trit.neg = refl
centerInvAdd Trit.zer Trit.zer = refl
centerInvAdd Trit.zer Trit.pos = refl
centerInvAdd Trit.pos Trit.neg = refl
centerInvAdd Trit.pos Trit.zer = refl
centerInvAdd Trit.pos Trit.pos = refl

-- Abelian medial law, used by the shear matrix (a,b) |-> (a+b,b).
centerAdd-medial :
  (a b c d : Trit.Trit) →
  centerAdd (centerAdd a b) (centerAdd c d)
  ≡ centerAdd (centerAdd a c) (centerAdd b d)
centerAdd-medial a b c d =
  trans
    (sym (centerAdd-assoc a b (centerAdd c d)))
    (trans
      (cong (λ x → centerAdd a x)
        (centerAdd-assoc b c d))
      (trans
        (cong
          (λ x → centerAdd a (centerAdd x d))
          (centerAdd-comm b c))
        (trans
          (cong (λ x → centerAdd a x)
            (sym (centerAdd-assoc c b d)))
          (centerAdd-assoc a c (centerAdd b d)))))

------------------------------------------------------------------------
-- Exact transport back to the original triXor convention.
------------------------------------------------------------------------

toOld : Trit.Trit → Base.TriTruth
toOld t = Bridge.toTriTruth (retreat t)

fromOld : Base.TriTruth → Trit.Trit
fromOld t = advance (Bridge.fromTriTruth t)

toOldFromOld :
  (t : Base.TriTruth) → toOld (fromOld t) ≡ t
toOldFromOld Base.tri-low = refl
toOldFromOld Base.tri-mid = refl
toOldFromOld Base.tri-high = refl

fromOldToOld :
  (t : Trit.Trit) → fromOld (toOld t) ≡ t
fromOldToOld Trit.neg = refl
fromOldToOld Trit.zer = refl
fromOldToOld Trit.pos = refl

centerAdd-toOld :
  (a b : Trit.Trit) →
  toOld (centerAdd a b) ≡ Base.triXor (toOld a) (toOld b)
centerAdd-toOld Trit.neg Trit.neg = refl
centerAdd-toOld Trit.neg Trit.zer = refl
centerAdd-toOld Trit.neg Trit.pos = refl
centerAdd-toOld Trit.zer Trit.neg = refl
centerAdd-toOld Trit.zer Trit.zer = refl
centerAdd-toOld Trit.zer Trit.pos = refl
centerAdd-toOld Trit.pos Trit.neg = refl
centerAdd-toOld Trit.pos Trit.zer = refl
centerAdd-toOld Trit.pos Trit.pos = refl

------------------------------------------------------------------------
-- Componentwise C3 x C3 on the EXISTING Sheet9 carrier.
------------------------------------------------------------------------

centerSheetZero : Codec.Sheet9
centerSheetZero = Codec.sheet Trit.zer Trit.zer

centerSheetAdd : Codec.Sheet9 → Codec.Sheet9 → Codec.Sheet9
centerSheetAdd
  (a ∷ᵥ b ∷ᵥ []ᵥ)
  (c ∷ᵥ d ∷ᵥ []ᵥ) =
  Codec.sheet (centerAdd a c) (centerAdd b d)

centerSheetNeg : Codec.Sheet9 → Codec.Sheet9
centerSheetNeg (a ∷ᵥ b ∷ᵥ []ᵥ) =
  Codec.sheet (Trit.inv a) (Trit.inv b)

centerSheet-left-zero :
  (s : Codec.Sheet9) →
  centerSheetAdd centerSheetZero s ≡ s
centerSheet-left-zero (a ∷ᵥ b ∷ᵥ []ᵥ)
  rewrite centerAdd-left-zero a
        | centerAdd-left-zero b = refl

centerSheet-right-zero :
  (s : Codec.Sheet9) →
  centerSheetAdd s centerSheetZero ≡ s
centerSheet-right-zero (a ∷ᵥ b ∷ᵥ []ᵥ)
  rewrite centerAdd-right-zero a
        | centerAdd-right-zero b = refl

centerSheet-assoc :
  (a b c : Codec.Sheet9) →
  centerSheetAdd a (centerSheetAdd b c)
  ≡ centerSheetAdd (centerSheetAdd a b) c
centerSheet-assoc
  (a0 ∷ᵥ a1 ∷ᵥ []ᵥ)
  (b0 ∷ᵥ b1 ∷ᵥ []ᵥ)
  (c0 ∷ᵥ c1 ∷ᵥ []ᵥ)
  rewrite centerAdd-assoc a0 b0 c0
        | centerAdd-assoc a1 b1 c1 = refl

centerSheet-comm :
  (a b : Codec.Sheet9) →
  centerSheetAdd a b ≡ centerSheetAdd b a
centerSheet-comm
  (a0 ∷ᵥ a1 ∷ᵥ []ᵥ)
  (b0 ∷ᵥ b1 ∷ᵥ []ᵥ)
  rewrite centerAdd-comm a0 b0
        | centerAdd-comm a1 b1 = refl

centerSheet-inverse :
  (s : Codec.Sheet9) →
  centerSheetAdd s (centerSheetNeg s) ≡ centerSheetZero
centerSheet-inverse (a ∷ᵥ b ∷ᵥ []ᵥ)
  rewrite centerAdd-inverse a
        | centerAdd-inverse b = refl

centerSheet-triple-zero :
  (s : Codec.Sheet9) →
  centerSheetAdd (centerSheetAdd s s) s ≡ centerSheetZero
centerSheet-triple-zero (a ∷ᵥ b ∷ᵥ []ᵥ)
  rewrite centerTripleZero a
        | centerTripleZero b = refl

-- Existing kernel inversion is definitionally the new group inverse.
centerSheetNegIsExistingInversion :
  (s : Codec.Sheet9) →
  centerSheetNeg s ≡ Codec.invertKernel s
centerSheetNegIsExistingInversion (a ∷ᵥ b ∷ᵥ []ᵥ) = refl

------------------------------------------------------------------------
-- Two-sided group carrier chart to the older PhaseQuotient9.
------------------------------------------------------------------------

sheetToPhase : Codec.Sheet9 → Phase.PhaseQuotient9
sheetToPhase (a ∷ᵥ b ∷ᵥ []ᵥ) =
  toOld a , toOld b

phaseToSheet : Phase.PhaseQuotient9 → Codec.Sheet9
phaseToSheet (a , b) =
  Codec.sheet (fromOld a) (fromOld b)

sheetPhaseRoundTrip :
  (s : Codec.Sheet9) →
  phaseToSheet (sheetToPhase s) ≡ s
sheetPhaseRoundTrip (a ∷ᵥ b ∷ᵥ []ᵥ)
  rewrite fromOldToOld a
        | fromOldToOld b = refl

phaseSheetRoundTrip :
  (p : Phase.PhaseQuotient9) →
  sheetToPhase (phaseToSheet p) ≡ p
phaseSheetRoundTrip (a , b)
  rewrite toOldFromOld a
        | toOldFromOld b = refl

sheetToPhase-preserves-addition :
  (a b : Codec.Sheet9) →
  sheetToPhase (centerSheetAdd a b)
  ≡ Phase.q9Add (sheetToPhase a) (sheetToPhase b)
sheetToPhase-preserves-addition
  (a0 ∷ᵥ a1 ∷ᵥ []ᵥ)
  (b0 ∷ᵥ b1 ∷ᵥ []ᵥ)
  rewrite centerAdd-toOld a0 b0
        | centerAdd-toOld a1 b1 = refl

centerSheetZeroMapsToOldZero :
  sheetToPhase centerSheetZero ≡ Phase.q9Zero
centerSheetZeroMapsToOldZero = refl

record Boundary : Set where
  constructor boundary
  field
    oldC3LawReused : Bool
    identityMovedFromNegToSignedZero : Bool
    signedInvIsExactAdditiveInverse : Bool
    exponentThreePaid : Bool
    componentwiseC3SquarePaid : Bool
    twoSidedOldPhaseQuotientChartPaid : Bool
    groupLawTransportToOldPhasePaid : Bool
    ellipticGroupIntertwinerPaid : Bool

canonicalBoundary : Boundary
canonicalBoundary =
  boundary true true true true true true true false
