module DASHI.Moonshine.Monster3BSuzukiSelectedFaithful78C2Exact where

------------------------------------------------------------------------
-- MAX-CUT: KEEP THE TWO 6.SUZ 78-DIMENSIONAL FAMILIES DISTINCT.
--
-- ACTUAL repository producers:
--   scripts/monster_3b_suzuki_main_quotient_match.g selects faithful
--   degree12 AND faithful degree78 characters and tests full class
--   products, descent and Monster restriction when GAP runs.
--   scripts/monster_3b_suzuki_sym2_character_screen.g searches ALL
--   degree78 characters, including those descending to 3.Suz.
--
-- ORIGINAL MATHEMATICAL SOURCES:
--   Barraclough and Wilson (2007), DOI 10.1112/S1461157000001352.
--   Gabriele Nebe (2025), DOI 10.1007/s10801-025-01399-2:
--   irreducible Sym² of faithful 6.Suz degree12 is degree78 but
--   central C2 acts trivially; it factors through 3.Suz.
--
-- IF a faithful irreducible 6.Suz degree12 and a faithful irreducible
-- 6.Suz degree78 each have central involution scalar -1.
-- Their direct-sum degree90 centre trace is -90.
-- In 12 ⊕ Sym²(12), the 12 contributes -12 and 78 contributes +78,
-- so its centre trace is +66. These C2 character values DISAGREE.
--
-- This is a mathematical CONDITIONAL no-go for identifying those two
-- 6.Suz module families, not an actual successful GAP character match
-- and not an Agda kernel receipt. A matching central C3 value 90*zeta
-- and norm8100 is INSUFFICIENT to override the central C2 obstruction.
--
-- Do NOT create generic character theory here: the prior central-sign
-- theorem is owned by Monster3BJFineNineCellSymmetricSquareD4Exact.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_; _*_)
open import Data.Empty using (⊥)

import DASHI.Moonshine.Monster3BJFineNineCellSymmetricSquareD4Exact as Nine

data SourceSuzuki78Family : Set where
  hypotheticalFaithful78 nebeSymmetricSquare78 : SourceSuzuki78Family

centreC2Sign78 : SourceSuzuki78Family → Nine.CentralSign
centreC2Sign78 hypotheticalFaithful78 = Nine.negative
centreC2Sign78 nebeSymmetricSquare78 = Nine.positive

faithful78CentralSignCannotEqualSymSquare :
  centreC2Sign78 hypotheticalFaithful78
    ≡ centreC2Sign78 nebeSymmetricSquare78 → ⊥
faithful78CentralSignCannotEqualSymSquare ()

-- Two distinct central C2 character outcomes on the 90-dimensional
-- multiplicity space. The source selected case is NEGATIVE 90, and
-- the symmetric-square case is POSITIVE 66 (signedness is typed).
data SignedTrace : Set where
  positiveTrace negativeTrace : Nat → SignedTrace

faithfulFamilyMultiplicityCentreTrace : SignedTrace
faithfulFamilyMultiplicityCentreTrace = negativeTrace 90

nebeSymSquareMultiplicityCentreTrace : SignedTrace
nebeSymSquareMultiplicityCentreTrace = positiveTrace 66

faithfulFamilyNotNebeAsSixSuz :
  faithfulFamilyMultiplicityCentreTrace
    ≡ nebeSymSquareMultiplicityCentreTrace → ⊥
faithfulFamilyNotNebeAsSixSuz ()

centralTraceDifference : 66 + 90 ≡ 2 * 78
centralTraceDifference = refl

-- This is the new critical discriminator after the C3 norm cut:
-- the SAME two C3 phases and the SAME 90-zeta norm can occur
-- for inequivalent 6.Suz C2 characters. A C3 equality alone
-- cannot supply an isomorphism as 6.Suz representations.
-- IMPORTANT: an earlier draft here contained fields such as
--   actualMonster78OccurrencePaidHere : Set
-- inside a generic record. These are NOT proof obligations: the type Set
-- is inhabited by arbitrary ordinary types (for example Nat), so filling
-- such a field proves absolutely nothing about Monster occurrences.
-- Removed rather than quietly exporting a misleading 'paid' certificate.
--
-- A source-selected 78 witness must instead be constructed from the
-- original 6.Suz -> main -> MN3B -> Monster exact character-table/quotient
-- certificate and fed into the existing proof-relevant owner in PR #1098.
-- No such source-run witness is produced in this module.
