module DASHI.Wikimedia.IbrahimMonster3BModernRestrictionTwelveSeventyEightOccurrenceSnowballExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Attribution
import DASHI.Core.SnowballAttributionProvenanceInvariantExact as Snowball
import DASHI.Wikimedia.IbrahimMonster3BModernCharacterVerificationKernel20SnowballExact as Modern

------------------------------------------------------------------------
-- MODERN RESTRICTION DEGREE UNIQUENESS -> SOURCE-PAID 12/78 OCCURRENCE
--
-- Two independent published/source surfaces now meet without needing the
-- unexecuted local GAP class-function matcher:
--
--   Breuer--Magaard--Wilson detailed protocol:
--     * selected quotient is H/[1,20];
--     * cand = Irr(H/[1,20]) with degree <= 196883 has length 95;
--     * the accepted restriction solution has exactly four coefficient-one
--       constituents.
--
--   An--Wilson Table A.17:
--     * gives the complete degree inventory WITH multiplicities for
--       Irr(3^(1+12).2.Suz.2).
--
-- Exhausting the published 95-element multiset under the four-constituent
-- constraint gives exactly one degree multiset summing to 196883:
--
--       143 + 17496 + 65520 + 113724 = 196883.
--
-- The two unique paired-sector degrees then factor source-natively as
--
--       17496  = 2 * 729 * 12
--       113724 = 2 * 729 * 78.
--
-- This pays DEGREE-LEVEL OCCURRENCE of the 12 and 78 multiplicity factors in
-- the actual Monster 3B-normalizer restriction.  It does NOT yet construct
-- their matrices, the inertia action, an intertwiner, or a phase-resolved
-- W_zeta representation.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- 1. Attribution.
------------------------------------------------------------------------

anWilson : Attribution.AttributedSource
anWilson = Attribution.mkDOISource
  "Jianbei An; R. A. Wilson"
  "The Alperin weight conjecture and Uno's conjecture for the Monster M, p odd"
  "LMS Journal of Computation and Mathematics 13, 320-356"
  "2010"
  "10.1112/S1461157009000059"
  "https://doi.org/10.1112/S1461157009000059"
  Attribution.academicArticleSource
  "independent published source for the complete irreducible-character degree inventory and multiplicities of 3^(1+12).2.Suz.2 in Table A.17"
  Attribution.publicAttribution

anWilsonAttribution = Snowball.canonicalSourceRoleSnowballReceipt anWilson

anWilsonDOI : String
anWilsonDOI = "10.1112/S1461157009000059"

modernVerificationDOI : String
modernVerificationDOI = "10.1016/j.jalgebra.2025.09.034"

------------------------------------------------------------------------
-- 2. Exact arithmetic consequences of the unique source-paid degree set.
------------------------------------------------------------------------

restrictionDegreeTotal : 143 + 17496 + 65520 + 113724 ≡ 196883
restrictionDegreeTotal = refl

twelvePairedDegree : 2 * 729 * 12 ≡ 17496
twelvePairedDegree = refl

seventyEightPairedDegree : 2 * 729 * 78 ≡ 113724
seventyEightPairedDegree = refl

pairedSectorTotal : 17496 + 113724 ≡ 2 * 65610
pairedSectorTotal = refl

centreTrivialTotal : 143 + 65520 ≡ 65663
centreTrivialTotal = refl

multiplicityTotal : 12 + 78 ≡ 90
multiplicityTotal = refl

------------------------------------------------------------------------
-- 3. Source/computation receipt.
------------------------------------------------------------------------

record RestrictionDegreeUniquenessReceipt : Set where
  constructor restriction-degree-uniqueness-receipt
  field
    selectedNormalizerTable : String
    modernCandidateCount : Nat
    restrictionConstituentCount : Nat
    allRestrictionCoefficientsOne : Bool
    anWilsonInventoryCompleteForBound : Bool
    uniqueDegreeMultisetFound : Bool
    firstDegree : Nat
    secondDegree : Nat
    thirdDegree : Nat
    fourthDegree : Nat
    twelveMultiplicityDegree : Nat
    seventyEightMultiplicityDegree : Nat
    verifierPath : String
    verifierGitBlobSha : String
    focusedCheckerPath : String
    exactRepoBlobExecutionReceiptPaid : Bool
open RestrictionDegreeUniquenessReceipt public

canonicalRestrictionDegreeUniquenessReceipt : RestrictionDegreeUniquenessReceipt
canonicalRestrictionDegreeUniquenessReceipt = restriction-degree-uniqueness-receipt
  "3^(1+12).2.Suz.2 / MN3B"
  95
  4
  true
  true
  true
  143 17496 65520 113724
  12 78
  "scripts/monster_3b_modern_restriction_degree_uniqueness.py"
  "2e33bf6d961683af1804e2a7e9488fe8291bbd3b"
  "scripts/check_monster_3b_modern_restriction_degree_uniqueness.sh"
  false

------------------------------------------------------------------------
-- 4. DOI / QID / Dewey / OEIS are separate coordinates.
------------------------------------------------------------------------

record RestrictionOccurrenceExternalCoordinates : Set where
  constructor restriction-occurrence-external-coordinates
  field
    anWilsonExactArticleQid : String
    modernExactArticleQid : String
    groupRepresentationQid : String
    representationCharacterQid : String
    finiteGroupQid : String
    anWilsonExactPublicationDewey : String
    modernExactPublicationDewey : String
    groupRepresentationTopicDewey : String
    finiteGroupTopicDewey : String
    oeisCoordinate : String
    oeisHasOccurrenceAuthority : Bool
open RestrictionOccurrenceExternalCoordinates public

canonicalRestrictionOccurrenceExternalCoordinates : RestrictionOccurrenceExternalCoordinates
canonicalRestrictionOccurrenceExternalCoordinates = restriction-occurrence-external-coordinates
  "unresolved rather than guessed for the exact An-Wilson article"
  "unresolved rather than guessed for the exact Breuer-Magaard-Wilson article"
  "Q1055807"
  "Q600043"
  "Q1057968"
  "unresolved rather than inferred from subject classification"
  "510"
  "512.22"
  "512.23"
  "A005052 only as numerical provenance for 90 = 10*3^2; not character-occurrence authority"
  false

------------------------------------------------------------------------
-- 5. WrongType / non-promotion boundaries.
------------------------------------------------------------------------

data DegreeOccurrenceCreatesAction : Set where
data DegreeOccurrenceCreatesIntertwiner : Set where
data DegreeOccurrenceCreatesPhaseResolvedSector : Set where
data DegreeOccurrenceCreatesE6Action : Set where
data SourceExecutionCreatesLocalGAPReceipt : Set where
data OeisCreatesCharacterOccurrence : Set where

degreeOccurrenceDoesNotCreateAction : DegreeOccurrenceCreatesAction → ⊥
degreeOccurrenceDoesNotCreateAction ()

degreeOccurrenceDoesNotCreateIntertwiner : DegreeOccurrenceCreatesIntertwiner → ⊥
degreeOccurrenceDoesNotCreateIntertwiner ()

degreeOccurrenceDoesNotResolvePhase : DegreeOccurrenceCreatesPhaseResolvedSector → ⊥
degreeOccurrenceDoesNotResolvePhase ()

degreeOccurrenceDoesNotCreateE6Action : DegreeOccurrenceCreatesE6Action → ⊥
degreeOccurrenceDoesNotCreateE6Action ()

sourceExecutionDoesNotCreateLocalGAPReceipt : SourceExecutionCreatesLocalGAPReceipt → ⊥
sourceExecutionDoesNotCreateLocalGAPReceipt ()

oeisDoesNotCreateOccurrence : OeisCreatesCharacterOccurrence → ⊥
oeisDoesNotCreateOccurrence ()

------------------------------------------------------------------------
-- 6. Corrected frontier.
------------------------------------------------------------------------

record RestrictionOccurrenceFrontier : Set where
  constructor restriction-occurrence-frontier
  field
    modernFourConstituentConstraintPaid : Bool
    modernNinetyFiveCandidateConstraintPaid : Bool
    anWilsonDegreeInventoryPaid : Bool
    exhaustiveDegreeUniquenessVerifierWritten : Bool
    uniqueFourDegreeMultisetPaid : Bool
    degree17496OccursInActualRestriction : Bool
    degree113724OccursInActualRestriction : Bool
    multiplicityTwelveOccursAtDegreeLevel : Bool
    multiplicitySeventyEightOccursAtDegreeLevel : Bool
    localFullCharacterMatcherExecuted : Bool
    actualMultiplicityMatricesPaid : Bool
    actualInertiaActionPaid : Bool
    twelvePlusSeventyEightIntertwinerPaid : Bool
    e6ActionIdentificationPaid : Bool
    nextResidual : String
open RestrictionOccurrenceFrontier public

currentRestrictionOccurrenceFrontier : RestrictionOccurrenceFrontier
currentRestrictionOccurrenceFrontier = restriction-occurrence-frontier
  true true true true true true true true true
  false false false false false
  "the actual Monster N(3B) restriction is now source-paid at the degree-occurrence level: its four coefficient-one low-degree constituents have the unique degree multiset {143,17496,65520,113724}, so the 2*729*12 and 2*729*78 paired constituents genuinely occur. Stop treating local GAP replay as the sole occurrence gate. The next theorem-bearing leaf is stronger: construct or recover the actual multiplicity-space representation/action for the 17496 and 113724 constituents on the source-native inertia actor, then identify its 12 and 78 factors by a same-action character/intertwiner receipt. A local GAP replay remains valuable independent verification, but degree occurrence alone does not create matrices, phase-resolved W_zeta, or an E6 action."

modernFrontier : Modern.ModernKernelVerificationFrontier
modernFrontier = Modern.currentModernKernelVerificationFrontier
