module DASHI.Wikimedia.IbrahimExceptionalOEISHypothesisTestExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Attribution
import DASHI.Core.SnowballAttributionProvenanceInvariantExact as AttributionSnowball
import DASHI.Foundations.ExceptionalAlbertFreudenthalResidualExact as Exceptional
import DASHI.Moonshine.Base369Monster3BMultiplicityInertiaTwelveSeventyEightBidiExact as Multiplicity
import DASHI.Moonshine.Base369Monster3BSeventyEightExceptionalE6BidiExact as E6Candidate

------------------------------------------------------------------------
-- OEIS AS HYPOTHESIS TEST, NOT SEMANTIC AUTHORITY
--
-- The existing DASHI constellation is
--
--   90 = 12 + 78
--   78 = 52 + 26
--   52 = 26 + 26
--   53 = 1 + 26 + 26
--   54 = 27 + 27.
--
-- OEIS gives two particularly strong independent representation-dimension
-- sequences:
--
--   A121737 (E6 irreducible dimensions): 1, 27, 78, ...
--   A121738 (F4 irreducible dimensions): 1, 26, 52, ...
--
-- Thus 27/78 and 26/52 have direct representation-sequence roles, while
-- 53/54 are derived sums of those roles.  The Monster-specific 12+78 split is
-- NOT thereby an exceptional-Lie representation decomposition: 12 is not a
-- low-dimensional E6/F4 irrep term in these two sequence families.
------------------------------------------------------------------------

record OEISRepresentationTerm : Set where
  constructor oeis-representation-term
  field
    sequenceId : String
    position : Nat
    value : Nat
    semanticRole : String
open OEISRepresentationTerm public

e6Trivial : OEISRepresentationTerm
e6Trivial = oeis-representation-term "A121737" 1 1 "E6 trivial representation dimension"

e6Minuscule27 : OEISRepresentationTerm
e6Minuscule27 = oeis-representation-term "A121737" 2 27 "E6 smallest faithful/minuscule representation dimension"

e6Adjoint78 : OEISRepresentationTerm
e6Adjoint78 = oeis-representation-term "A121737" 3 78 "E6 adjoint representation dimension"

f4Trivial : OEISRepresentationTerm
f4Trivial = oeis-representation-term "A121738" 1 1 "F4 trivial representation dimension"

f4Standard26 : OEISRepresentationTerm
f4Standard26 = oeis-representation-term "A121738" 2 26 "F4 standard/traceless-Albert representation dimension"

f4Adjoint52 : OEISRepresentationTerm
f4Adjoint52 = oeis-representation-term "A121738" 3 52 "F4 adjoint representation dimension"

------------------------------------------------------------------------
-- Exact local arithmetic already owned by the exceptional carrier.
------------------------------------------------------------------------

e6AdjointAsF4Plus26 : 78 ≡ 52 + 26
e6AdjointAsF4Plus26 = Exceptional.eSixIsF4PlusTracelessAlbert

f4AdjointAsTwo26 : 52 ≡ 26 + 26
f4AdjointAsTwo26 = Exceptional.fFourIsTwoTracelessAlbertDimensions

reduced53AsOnePlusTwo26 : 53 ≡ 1 + (26 + 26)
reduced53AsOnePlusTwo26 = Exceptional.reducedAlbertPairIsOnePlusTwoTraceless

full54AsTwo27 : 54 ≡ 27 + 27
full54AsTwo27 = Exceptional.albertPairIsTwoAlbert

monsterMultiplicityAsTwelvePlusSeventyEight : 90 ≡ 12 + 78
monsterMultiplicityAsTwelvePlusSeventyEight = refl

------------------------------------------------------------------------
-- Hypothesis-test classification.
------------------------------------------------------------------------

data OEISTestStrength : Set where
  directRepresentationSequenceTerm : OEISTestStrength
  derivedFromDirectRepresentationTerms : OEISTestStrength
  arithmeticOnlyAgainstThisSequenceFamily : OEISTestStrength
  rejectedSemanticPromotion : OEISTestStrength

record ExceptionalOEISTest : Set where
  constructor exceptional-oeis-test
  field
    formulation : String
    strength : OEISTestStrength
    passesArithmetic : Bool
    directOEISRepresentationSupport : Bool
    actionIntertwinerPaid : Bool
    interpretation : String
open ExceptionalOEISTest public

test78 : ExceptionalOEISTest
test78 = exceptional-oeis-test
  "78 = dim(E6 adjoint) and 78 = 52 + 26"
  directRepresentationSequenceTerm true true false
  "A121737 directly supports 78 as an E6 irrep dimension; A121738 directly supports 52 and 26 as F4 irrep dimensions; the E6 -> F4 + 26 branching/intertwiner is not supplied by OEIS"

test52 : ExceptionalOEISTest
test52 = exceptional-oeis-test
  "52 = 26 + 26"
  directRepresentationSequenceTerm true true false
  "A121738 directly supports both 26 and 52 as F4 irrep dimensions; the equality 52=26+26 is arithmetic and does not decompose the F4 adjoint representation into two 26-dimensional subrepresentations"

test53 : ExceptionalOEISTest
test53 = exceptional-oeis-test
  "53 = 1 + 26 + 26"
  derivedFromDirectRepresentationTerms true false false
  "1 and 26 are direct F4 representation-dimension terms, but 53 itself is not thereby an F4 irrep; retain the DASHI reduced-Albert 53 only as a candidate carrier until a same-action recognition is supplied"

test54 : ExceptionalOEISTest
test54 = exceptional-oeis-test
  "54 = 27 + 27"
  derivedFromDirectRepresentationTerms true false false
  "27 is a direct E6 representation-dimension term, but 54 is a doubled carrier dimension rather than an E6 irrep identification from A121737 alone"

test90 : ExceptionalOEISTest
test90 = exceptional-oeis-test
  "90 = 12 + 78"
  arithmeticOnlyAgainstThisSequenceFamily true false false
  "78 has a direct E6 role, but 12 is not a low-dimensional E6/F4 irrep term in A121737/A121738; OEIS therefore does not support promoting the Monster 12+78 multiplicity split to an exceptional-Lie decomposition"

------------------------------------------------------------------------
-- Negative calibration: an OEIS miss/role mismatch is informative.
------------------------------------------------------------------------

data TwelvePlusSeventyEightCreatesE6Branching : Set where
data FiftyThreeSumCreatesF4Irrep : Set where
data FiftyFourSumCreatesE6Irrep : Set where
data OEISMembershipCreatesIntertwiner : Set where

twelvePlus78DoesNotCreateE6Branching : TwelvePlusSeventyEightCreatesE6Branching → ⊥
twelvePlus78DoesNotCreateE6Branching ()

fiftyThreeDoesNotBecomeF4Irrep : FiftyThreeSumCreatesF4Irrep → ⊥
fiftyThreeDoesNotBecomeF4Irrep ()

fiftyFourDoesNotBecomeE6Irrep : FiftyFourSumCreatesE6Irrep → ⊥
fiftyFourDoesNotBecomeE6Irrep ()

oeisDoesNotCreateIntertwiner : OEISMembershipCreatesIntertwiner → ⊥
oeisDoesNotCreateIntertwiner ()

------------------------------------------------------------------------
-- Provenance / external coordinates.
------------------------------------------------------------------------

record ExceptionalOEISCoordinates : Set where
  constructor exceptional-oeis-coordinates
  field
    e6Qid : String
    f4Qid : String
    jordanAlgebraQid : String
    e6IrrepDimensionOEIS : String
    f4IrrepDimensionOEIS : String
    simpleLieDimensionOEIS : String
    tItsDOI : String
    oeisIsTestSurfaceNotAuthority : Bool
open ExceptionalOEISCoordinates public

canonicalExceptionalOEISCoordinates : ExceptionalOEISCoordinates
canonicalExceptionalOEISCoordinates = exceptional-oeis-coordinates
  "Q1054513" "Q869077" "Q649977"
  "A121737" "A121738" "A263005"
  "10.1016/S1385-7258(66)50028-2"
  true

titsSource : Attribution.AttributedSource
titsSource = Attribution.mkDOISource
  "Jacques Tits"
  "Algèbres alternatives, algèbres de Jordan et algèbres de Lie exceptionnelles"
  "Indagationes Mathematicae 28, 223-237"
  "1966"
  "10.1016/S1385-7258(66)50028-2"
  "https://doi.org/10.1016/S1385-7258(66)50028-2"
  Attribution.academicArticleSource
  "primary exceptional Lie/Jordan construction provenance; does not identify the Monster 12+78 or 53 residual carriers"
  Attribution.publicAttribution

titsAttribution = AttributionSnowball.canonicalSourceRoleSnowballReceipt titsSource

------------------------------------------------------------------------
-- Existing action-level gates remain authoritative.
------------------------------------------------------------------------

multiplicityBoundary : Multiplicity.MultiplicityInertiaTwelveSeventyEightBoundary
multiplicityBoundary = Multiplicity.canonicalMultiplicityInertiaTwelveSeventyEightBoundary

e6CandidateBoundary : E6Candidate.SeventyEightExceptionalBoundary
e6CandidateBoundary = E6Candidate.canonicalSeventyEightExceptionalBoundary

record ExceptionalOEISHypothesisFrontier : Set where
  constructor exceptional-oeis-hypothesis-frontier
  field
    e6SequenceDirect12778Paid : Bool
    f4SequenceDirect12652Paid : Bool
    seventyEightExceptionalHypothesisStrengthened : Bool
    fiftyThreeDerivedCandidateRetained : Bool
    fiftyFourDerivedCandidateRetained : Bool
    twelvePlusSeventyEightExceptionalPromotionSupportedByTheseOEISFamilies : Bool
    actualFin90SameActionSplitPaid : Bool
    actual78ToE6IntertwinerPaid : Bool
    actual53ResidualToAlbertIntertwinerPaid : Bool
    nextResidual : String
open ExceptionalOEISHypothesisFrontier public

currentExceptionalOEISHypothesisFrontier : ExceptionalOEISHypothesisFrontier
currentExceptionalOEISHypothesisFrontier = exceptional-oeis-hypothesis-frontier
  true true true true true false false false false
  "use OEIS as a discriminator: prioritize the 78 -> E6 and 26/52/27 exceptional tests because their representation-sequence roles are direct; do not spend action-level proof debt on 12 -> exceptional semantics until an independent representation/source edge appears. First pay the existing actual Fin90 inertia attachment, then test the literal 78 block by an explicit E6 intertwiner and the literal Residual53 by the existing Albert/F4 same-action interface"
