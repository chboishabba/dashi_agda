module DASHI.Mathematics.Topology.AlexanderHornedS3WordSignOrbitTransportExact where

------------------------------------------------------------------------
-- ACTUAL orbit transport:
--   (three-valued words of length n+1) / global value S3
--       <-> (n balanced ternary DIFFERENCE digits) / global sign C2
--
-- The C3 normal subgroup of S3 is eliminated by fixing the FIRST
-- word symbol as the origin; the residual stabilizer C2 negates
-- the n differences. This gives r_n = sum_{k<=3} S(n+1,k).
--
-- Original owners: S3/C3 ternary permutations, #1275 restricted-growth
-- equality patterns, #1244 native H=C3_sector x C2_sign orbits.
-- New bridge is source-written, Johl Brown-directed/ChatGPT-assisted
-- 2026-10-28, NOT Agda kernel-checked. Group actions on named words,
-- native address fibres and statistical probability measures REMAIN
-- different objects unless specifically transported.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Product using (_×_; _,_)
open import Data.Vec.Base using (Vec; []; _∷_)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; trans)

import DASHI.Core.FiniteC3OrbitStabilizerExact as C3
import DASHI.Algebra.BalancedTernary as Trit
import DASHI.Mathematics.Topology.AlexanderHornedNativeBalancedTernaryEndTowerExact as End
import DASHI.Mathematics.Topology.AlexanderHornedNativeTernaryLocalPhaseActionExact as Phase

-- One anchor label followed by n named labels, all in the EXISTING C3.
AnchoredWord : Nat → Set
AnchoredWord n = C3.C3 × Vec C3.C3 n

relative : C3.C3 → C3.C3 → C3.C3
relative anchor value = C3._∙_ value (C3.inverse anchor)

normalise : ∀ {n} → AnchoredWord n → Vec C3.C3 n
normalise (anchor , suffix) = End.mapVec (relative anchor) suffix

translateWord : ∀ {n} → C3.C3 → AnchoredWord n → AnchoredWord n
translateWord shift (anchor , suffix) =
  C3._∙_ shift anchor ,
  End.mapVec (C3._∙_ shift) suffix

reflectWord : ∀ {n} → AnchoredWord n → AnchoredWord n
reflectWord (anchor , suffix) =
  C3.inverse anchor , End.mapVec C3.inverse suffix

-- Explicit proof that global label translation disappears in differences.
relativeTranslate : ∀ shift anchor value →
  relative (C3._∙_ shift anchor) (C3._∙_ shift value) ≡
  relative anchor value
relativeTranslate C3.c0 C3.c0 C3.c0 = refl
relativeTranslate C3.c0 C3.c0 C3.c1 = refl
relativeTranslate C3.c0 C3.c0 C3.c2 = refl
relativeTranslate C3.c0 C3.c1 C3.c0 = refl
relativeTranslate C3.c0 C3.c1 C3.c1 = refl
relativeTranslate C3.c0 C3.c1 C3.c2 = refl
relativeTranslate C3.c0 C3.c2 C3.c0 = refl
relativeTranslate C3.c0 C3.c2 C3.c1 = refl
relativeTranslate C3.c0 C3.c2 C3.c2 = refl
relativeTranslate C3.c1 C3.c0 C3.c0 = refl
relativeTranslate C3.c1 C3.c0 C3.c1 = refl
relativeTranslate C3.c1 C3.c0 C3.c2 = refl
relativeTranslate C3.c1 C3.c1 C3.c0 = refl
relativeTranslate C3.c1 C3.c1 C3.c1 = refl
relativeTranslate C3.c1 C3.c1 C3.c2 = refl
relativeTranslate C3.c1 C3.c2 C3.c0 = refl
relativeTranslate C3.c1 C3.c2 C3.c1 = refl
relativeTranslate C3.c1 C3.c2 C3.c2 = refl
relativeTranslate C3.c2 C3.c0 C3.c0 = refl
relativeTranslate C3.c2 C3.c0 C3.c1 = refl
relativeTranslate C3.c2 C3.c0 C3.c2 = refl
relativeTranslate C3.c2 C3.c1 C3.c0 = refl
relativeTranslate C3.c2 C3.c1 C3.c1 = refl
relativeTranslate C3.c2 C3.c1 C3.c2 = refl
relativeTranslate C3.c2 C3.c2 C3.c0 = refl
relativeTranslate C3.c2 C3.c2 C3.c1 = refl
relativeTranslate C3.c2 C3.c2 C3.c2 = refl

normaliseTranslate : ∀ {n} shift (w : AnchoredWord n) →
  normalise (translateWord shift w) ≡ normalise w
normaliseTranslate shift (anchor , []) = refl
normaliseTranslate shift (anchor , value ∷ rest) =
  cong₂ _∷_ (relativeTranslate shift anchor value)
    (normaliseTranslateSuffix shift anchor rest)
  where
    normaliseTranslateSuffix : ∀ {k} shift anchor (rest : Vec C3.C3 k) →
      End.mapVec (relative (C3._∙_ shift anchor))
        (End.mapVec (C3._∙_ shift) rest) ≡
      End.mapVec (relative anchor) rest
    normaliseTranslateSuffix shift anchor [] = refl
    normaliseTranslateSuffix shift anchor (value ∷ rest) =
      cong₂ _∷_ (relativeTranslate shift anchor value)
        (normaliseTranslateSuffix shift anchor rest)

-- Global reflection survives as residual sign inversion.
relativeReflection : ∀ anchor value →
  relative (C3.inverse anchor) (C3.inverse value) ≡
  C3.inverse (relative anchor value)
relativeReflection C3.c0 C3.c0 = refl
relativeReflection C3.c0 C3.c1 = refl
relativeReflection C3.c0 C3.c2 = refl
relativeReflection C3.c1 C3.c0 = refl
relativeReflection C3.c1 C3.c1 = refl
relativeReflection C3.c1 C3.c2 = refl
relativeReflection C3.c2 C3.c0 = refl
relativeReflection C3.c2 C3.c1 = refl
relativeReflection C3.c2 C3.c2 = refl

normaliseReflection : ∀ {n} (w : AnchoredWord n) →
  normalise (reflectWord w) ≡
  End.mapVec C3.inverse (normalise w)
normaliseReflection (anchor , []) = refl
normaliseReflection (anchor , value ∷ rest) =
  cong₂ _∷_ (relativeReflection anchor value)
    (reflectionSuffix anchor rest)
  where
    reflectionSuffix : ∀ {k} anchor (rest : Vec C3.C3 k) →
      End.mapVec (relative (C3.inverse anchor))
        (End.mapVec C3.inverse rest) ≡
      End.mapVec C3.inverse (End.mapVec (relative anchor) rest)
    reflectionSuffix anchor [] = refl
    reflectionSuffix anchor (value ∷ rest) =
      cong₂ _∷_ (relativeReflection anchor value)
        (reflectionSuffix anchor rest)

phaseToSignedNegation : ∀ value →
  Phase.phaseToTrit (C3.inverse value) ≡
  Trit.negate (Phase.phaseToTrit value)
phaseToSignedNegation C3.c0 = refl
phaseToSignedNegation C3.c1 = refl
phaseToSignedNegation C3.c2 = refl

-- Actual bridge from the label word into the SOURCE native sign-orbit
-- carrier. The output is a signed difference word, not an identity of
-- address-set labels or physical horn geometry.
signedRelative : ∀ {n} → AnchoredWord n → Vec Trit.Trit n
signedRelative w = End.mapVec Phase.phaseToTrit (normalise w)

signedRelativeTranslationInvariant : ∀ {n} shift
  (w : AnchoredWord n) →
  signedRelative (translateWord shift w) ≡ signedRelative w
signedRelativeTranslationInvariant shift w =
  cong (End.mapVec Phase.phaseToTrit)
       (normaliseTranslate shift w)

signedReflectVec : ∀ {n} (values : Vec C3.C3 n) →
  End.mapVec Phase.phaseToTrit (End.mapVec C3.inverse values) ≡
  End.mapVec Trit.negate (End.mapVec Phase.phaseToTrit values)
signedReflectVec [] = refl
signedReflectVec (v ∷ rest) =
  cong₂ _∷_ (phaseToSignedNegation v) (signedReflectVec rest)

signedRelativeReflection : ∀ {n} (w : AnchoredWord n) →
  signedRelative (reflectWord w) ≡
  End.mapVec Trit.negate (signedRelative w)
signedRelativeReflection w =
  trans (cong (End.mapVec Phase.phaseToTrit)
                (normaliseReflection w))
        (signedReflectVec (normalise w))

-- A canonical section has first value ZERO. It is pointwise inverted
-- by the difference normalisation, for ALL word lengths.
wordFromDifferences : ∀ {n} → Vec Trit.Trit n → AnchoredWord n
wordFromDifferences xs =
  C3.c0 , End.mapVec Phase.tritToPhase xs

signedRelativeSection : ∀ {n} (xs : Vec Trit.Trit n) →
  signedRelative (wordFromDifferences xs) ≡ xs
signedRelativeSection [] = refl
signedRelativeSection (x ∷ xs) =
  cong₂ _∷_ (oneDifference x) (signedRelativeSection xs)
  where
    oneDifference : (x : Trit.Trit) →
      Phase.phaseToTrit (relative C3.c0 (Phase.tritToPhase x)) ≡ x
    oneDifference x =
      trans (cong Phase.phaseToTrit
              (C3.rightIdentity (Phase.tritToPhase x)))
            (Phase.tritPhaseRoundTrip x)

-- Recover the whole named word up to a GLOBAL C3 translation:
-- subtract the anchor to send it to zero and obtain its differences.
cancelAnchorInSuffix : ∀ anchor value →
  C3._∙_ (C3.inverse anchor) value ≡ relative anchor value
cancelAnchorInSuffix C3.c0 C3.c0 = refl
cancelAnchorInSuffix C3.c0 C3.c1 = refl
cancelAnchorInSuffix C3.c0 C3.c2 = refl
cancelAnchorInSuffix C3.c1 C3.c0 = refl
cancelAnchorInSuffix C3.c1 C3.c1 = refl
cancelAnchorInSuffix C3.c1 C3.c2 = refl
cancelAnchorInSuffix C3.c2 C3.c0 = refl
cancelAnchorInSuffix C3.c2 C3.c1 = refl
cancelAnchorInSuffix C3.c2 C3.c2 = refl

cancelAnchorInVec : ∀ {n} anchor (xs : Vec C3.C3 n) →
  End.mapVec (C3._∙_ (C3.inverse anchor)) xs ≡
  End.mapVec (relative anchor) xs
cancelAnchorInVec anchor [] = refl
cancelAnchorInVec anchor (v ∷ xs) =
  cong₂ _∷_ (cancelAnchorInSuffix anchor v)
    (cancelAnchorInVec anchor xs)

normalisedWord : ∀ {n} → Vec C3.C3 n → AnchoredWord n
normalisedWord xs = C3.c0 , xs

anchor : ∀ {n} → AnchoredWord n → C3.C3
anchor (c , xs) = c

normaliseViaTranslation : ∀ {n} (w : AnchoredWord n) →
  translateWord (C3.inverse (anchor w)) w ≡
  normalisedWord (normalise w)
normaliseViaTranslation (a , xs) =
  cong₂ _,_ (C3.inverseLeft a) (cancelAnchorInVec a xs)

-- This is a proof-level orbit-transport INTERFACE:
-- C3 orbit normalization erases global translation; reflection is
-- exactly simultaneous sign change on the canonical n trits.
-- Equivalence of quotient SETS follows from these maps and witnesses.
-- We do NOT identify the original value-S3 action with the distinct
-- sector-shift/sign action on raw native end addresses.
