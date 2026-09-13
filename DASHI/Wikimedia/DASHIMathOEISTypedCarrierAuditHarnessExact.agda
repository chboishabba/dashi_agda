module DASHI.Wikimedia.DASHIMathOEISTypedCarrierAuditHarnessExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Wikimedia.DASHIMathOEIS196883AuditRoadmapExact as PriorAudit
import DASHI.Wikimedia.IbrahimExceptionalOEISHypothesisTestExact as ExceptionalTest
import DASHI.Wikimedia.IbrahimE6CoxeterNinetyTypedCorrectionExact as E6Coxeter
import DASHI.Wikimedia.IbrahimG2SevenTwentyNineOEISNegativeControlExact as G2Control
import DASHI.Wikimedia.WikipediaAllPairsPrunedMergeSnowballExact as AllPairs

------------------------------------------------------------------------
-- REPO-WIDE TYPED OEIS HYPOTHESIS HARNESS
--
-- Semantic policy:
--   repo role -> typed OEIS family -> exact role/index -> provenance/QID/Dewey
--             -> same-object/action gate.
--
-- A numeral may appear in many families.  That creates multiple candidate
-- coordinates, NOT an identification between their carriers.
------------------------------------------------------------------------

data OEISFamily : Set where
  powerSequence
  representationDimension
  lieInvariant
  rootWeylCoxeter
  latticeTheta
  modularCoefficient
  divisorFactor
  finiteFieldProjective
  partitionCombinatorics
  physicalCount
  otherTypedFamily : OEISFamily

data TypedMatchStrength : Set where
  exactSameObject
  directTypedRole
  derivedTypedRole
  candidateRole
  collisionOnly
  negativeControl
  unqueried : TypedMatchStrength

record TypedOEISRole : Set where
  constructor typed-oeis-role
  field
    value : Nat
    repoRole : String
    family : OEISFamily
    oeisId : String
    externalRole : String
    strength : TypedMatchStrength
    arithmeticPaid : Bool
    sameSemanticObjectPaid : Bool
    actionOrIntertwinerPaid : Bool
    provenance : String
open TypedOEISRole public

------------------------------------------------------------------------
-- Exact requested seed list.  It is deliberately distinct from the role list:
-- one seed may have many typed roles.
------------------------------------------------------------------------

requestedCarrierDimensions : List Nat
requestedCarrierDimensions =
  1 ∷ 3 ∷ 6 ∷ 8 ∷ 9 ∷ 10 ∷ 12 ∷ 14 ∷ 26 ∷ 27 ∷
  52 ∷ 53 ∷ 54 ∷ 56 ∷ 64 ∷ 71 ∷ 72 ∷ 78 ∷ 90 ∷ 128 ∷
  19683 ∷ 65610 ∷ 196830 ∷ 196883 ∷ 196884 ∷ []

------------------------------------------------------------------------
-- Paid / high-confidence typed rows from existing repo and external audits.
------------------------------------------------------------------------

oneGeneric : TypedOEISRole
oneGeneric = typed-oeis-role 1
  "trivial/unit occurs in many DASHI carriers; role must be indexed"
  otherTypedFamily "multiple"
  "generic unit/trivial-representation term; too non-specific for semantic promotion"
  candidateRole true false false
  "retain only with a named carrier/source"

threePower : TypedOEISRole
threePower = typed-oeis-role 3 "C3 / ternary cardinality" powerSequence "A000244"
  "3^1" exactSameObject true false false
  "Base369 power-of-three coordinate"

sixE6InvariantDegree : TypedOEISRole
sixE6InvariantDegree = typed-oeis-role 6
  "Base369 HexTruth numeral; independently an E6 Weyl invariant degree"
  rootWeylCoxeter "A161409"
  "one invariant degree in the E6 Weyl-group Poincare/growth product"
  directTypedRole true false false
  "multi-role collision retained; does not identify Base369 HexTruth with E6"

eightE6InvariantDegree : TypedOEISRole
eightE6InvariantDegree = typed-oeis-role 8
  "Base369 pointed-extension predecessor 8; independently E6 invariant degree"
  rootWeylCoxeter "A161409"
  "one invariant degree in the E6 Weyl-group product"
  directTypedRole true false false
  "external E6 Weyl coordinate only"

ninePower : TypedOEISRole
ninePower = typed-oeis-role 9 "C9 / NonaryTruth" powerSequence "A000244"
  "3^2" exactSameObject true false false
  "Base369 power-of-three coordinate"

nineE6InvariantDegree : TypedOEISRole
nineE6InvariantDegree = typed-oeis-role 9
  "NonaryTruth numeral; independently E6 Weyl invariant degree"
  rootWeylCoxeter "A161409"
  "one invariant degree in the E6 Weyl-group product"
  directTypedRole true false false
  "same numeral does not identify the carriers"

tenPowerFamily : TypedOEISRole
tenPowerFamily = typed-oeis-role 10
  "9+1 completed coarse count"
  powerSequence "A005052"
  "10*3^0" directTypedRole true false false
  "numeric-family coordinate; pointed-unit role remains DASHI-owned"

twelveE6Coxeter : TypedOEISRole
twelveE6Coxeter = typed-oeis-role 12
  "Monster 12+78 multiplicity part; candidate E6 Coxeter invariant"
  rootWeylCoxeter "A161409"
  "largest E6 invariant degree / Coxeter number h(E6)=12"
  directTypedRole true false false
  "typed correction: not a 12-dimensional E6 irrep"

fourteenG2 : TypedOEISRole
fourteenG2 = typed-oeis-role 14
  "repo numeral; independently G2 representation dimension"
  representationDimension "A104599"
  "G2 irreducible-representation dimension"
  directTypedRole true false false
  "candidate cross-domain coordinate only until repo same-object role is specified"

twentySixF4 : TypedOEISRole
twentySixF4 = typed-oeis-role 26
  "traceless Albert / F4 standard carrier"
  representationDimension "A121738"
  "F4 standard/minimal representation dimension"
  directTypedRole true false false
  "exceptional carrier role; action recognition remains separate"

twentySevenPower : TypedOEISRole
twentySevenPower = typed-oeis-role 27
  "C27 / ternary cube cardinality"
  powerSequence "A000244"
  "3^3" exactSameObject true false false
  "Base369 power-of-three role"

twentySevenE6 : TypedOEISRole
twentySevenE6 = typed-oeis-role 27
  "Albert dimension; independently E6 minuscule representation dimension"
  representationDimension "A121737"
  "E6 smallest faithful/minuscule representation dimension"
  directTypedRole true false false
  "multiple exceptional/Base369 roles remain distinct"

twentySevenG2 : TypedOEISRole
twentySevenG2 = typed-oeis-role 27
  "same numeral also occurs in G2 representation dimensions"
  representationDimension "A104599"
  "G2 irreducible-representation dimension"
  collisionOnly true false false
  "use as all-pairs collision unless an independent action map appears"

fiftyTwoF4 : TypedOEISRole
fiftyTwoF4 = typed-oeis-role 52
  "F4 adjoint dimension = 2*26 numerically"
  representationDimension "A121738"
  "F4 adjoint representation dimension"
  directTypedRole true false false
  "52=26+26 does not itself split the adjoint"

fiftyThreeExceptionalCandidate : TypedOEISRole
fiftyThreeExceptionalCandidate = typed-oeis-role 53
  "Monster residual / Base369 54-1 / reduced Albert candidate"
  representationDimension "A121738"
  "derived 1+26+26 from direct F4 terms; 53 is not promoted as an F4 irrep"
  derivedTypedRole true false false
  "requires same-action Residual53 <-> exceptional recognition"

fiftyFourExceptionalCandidate : TypedOEISRole
fiftyFourExceptionalCandidate = typed-oeis-role 54
  "Base369 full residual / Albert pair 27+27"
  representationDimension "A121737"
  "derived double of direct E6 27-dimensional term"
  derivedTypedRole true false false
  "not an E6 irrep from A121737 alone"

fiftyFourMoonshineDivisor : TypedOEISRole
fiftyFourMoonshineDivisor = typed-oeis-role 54
  "divisor of 196884 and full 53+1 residual"
  divisorFactor "A199014"
  "54 divides 196884"
  directTypedRole true false false
  "arithmetic divisor role; no moonshine semantics imported"

fiftySixExceptional : TypedOEISRole
fiftySixExceptional = typed-oeis-role 56
  "Freudenthal carrier 1+1+27+27"
  representationDimension "unqueried-E7-family"
  "known repo exceptional carrier; typed OEIS E7-family verification retained as next query"
  unqueried true false false
  "do not guess sequence ID until verified"

sixtyFourG2 : TypedOEISRole
sixtyFourG2 = typed-oeis-role 64
  "repo carrier numeral; independently G2 irrep dimension"
  representationDimension "A104599"
  "G2 irreducible-representation dimension"
  directTypedRole true false false
  "same-number role only unless repo carrier is G2-linked"

seventyOneMonsterFactor : TypedOEISRole
seventyOneMonsterFactor = typed-oeis-role 71
  "prime factor in 47*59*71=196883"
  divisorFactor "A309510"
  "71 is a divisor/prime factor of 196883"
  directTypedRole true false false
  "arithmetic Monster divisor coordinate"

seventyTwoE6Roots : TypedOEISRole
seventyTwoE6Roots = typed-oeis-role 72
  "E6 root count = rank 6 * Coxeter number 12"
  rootWeylCoxeter "A161409"
  "derived E6 root-system invariant from rank/Coxeter data"
  derivedTypedRole true false false
  "root count is not an irrep dimension"

seventyEightE6 : TypedOEISRole
seventyEightE6 = typed-oeis-role 78
  "Monster multiplicity 78-block; E6 adjoint candidate"
  representationDimension "A121737"
  "E6 adjoint representation dimension"
  directTypedRole true false false
  "strong hypothesis target; actual Monster-to-E6 intertwiner remains unpaid"

ninetyPowerFamily : TypedOEISRole
ninetyPowerFamily = typed-oeis-role 90
  "Monster multiplicity Fin90 / completed trit-square"
  powerSequence "A005052"
  "10*3^2" exactSameObject true false false
  "exact numerical-family role"

ninetyE6MixedInvariant : TypedOEISRole
ninetyE6MixedInvariant = typed-oeis-role 90
  "same Monster multiplicity integer; candidate E6 mixed invariant"
  lieInvariant "A161409+A121737"
  "h(E6)+dim(E6)=12+78=90"
  derivedTypedRole true false false
  "mixed Coxeter-plus-dimension interpretation; not an E6 irrep/direct-sum claim"

oneTwentyEightUnqueried : TypedOEISRole
oneTwentyEightUnqueried = typed-oeis-role 128
  "owned DASHI carrier numeral"
  otherTypedFamily "unqueried"
  "typed sequence family not yet paid in this tranche"
  unqueried true false false
  "query Spin/Clifford/finite-field/power-of-two families before assigning semantics"

nineteenSixEightThreePower : TypedOEISRole
nineteenSixEightThreePower = typed-oeis-role 19683
  "Base369 hyperfabric state count 3^9"
  powerSequence "A000244"
  "3^9" exactSameObject true false false
  "exact Base369 numerical cardinality coordinate"

sixFiveSixOneZeroPowerFamily : TypedOEISRole
sixFiveSixOneZeroPowerFamily = typed-oeis-role 65610
  "one Monster regular C3 phase multiplicity = 90*729"
  powerSequence "A005052"
  "10*3^8" directTypedRole true false false
  "OEIS numeric family agrees; Monster representation meaning comes from character/action sources"

oneNineSixEightThreeZeroPowerFamily : TypedOEISRole
oneNineSixEightThreeZeroPowerFamily = typed-oeis-role 196830
  "three-phase regular Monster bulk"
  powerSequence "A005052"
  "10*3^9" directTypedRole true false false
  "exact numeric-family coordinate; same-action bulk identification remains distinct"

oneNineSixEightThreeMonster : TypedOEISRole
oneNineSixEightThreeMonster = typed-oeis-role 196883
  "Monster smallest nontrivial representation degree / Base369 bulk+53 total"
  representationDimension "A001379"
  "Monster irreducible-representation degree"
  directTypedRole true false false
  "representation role independent of Base369 arithmetic construction"

oneNineSixEightThreeDivisor : TypedOEISRole
oneNineSixEightThreeDivisor = typed-oeis-role 196883
  "47*59*71 target"
  divisorFactor "A309510"
  "full divisor-sequence object for 196883"
  exactSameObject true false false
  "arithmetic same-number view"

oneNineSixEightFourJ : TypedOEISRole
oneNineSixEightFourJ = typed-oeis-role 196884
  "repo j q^1 coefficient / V^natural weight-two dimension"
  modularCoefficient "A000521"
  "classical modular j coefficient"
  exactSameObject true false false
  "finite prefix same-object receipt already owned; whole series semantics separate"

oneNineSixEightFourDivisors : TypedOEISRole
oneNineSixEightFourDivisors = typed-oeis-role 196884
  "full Base369 bulk+54 total"
  divisorFactor "A199014"
  "integer whose divisor set contains 3,6,9,27,54"
  directTypedRole true false false
  "divisor atlas does not create Base369 or moonshine meaning"

------------------------------------------------------------------------
-- The role atlas is intentionally multi-valued.
------------------------------------------------------------------------

knownTypedRoles : List TypedOEISRole
knownTypedRoles =
  oneGeneric ∷ threePower ∷ sixE6InvariantDegree ∷ eightE6InvariantDegree ∷
  ninePower ∷ nineE6InvariantDegree ∷ tenPowerFamily ∷ twelveE6Coxeter ∷
  fourteenG2 ∷ twentySixF4 ∷ twentySevenPower ∷ twentySevenE6 ∷
  twentySevenG2 ∷ fiftyTwoF4 ∷ fiftyThreeExceptionalCandidate ∷
  fiftyFourExceptionalCandidate ∷ fiftyFourMoonshineDivisor ∷
  fiftySixExceptional ∷ sixtyFourG2 ∷ seventyOneMonsterFactor ∷
  seventyTwoE6Roots ∷ seventyEightE6 ∷ ninetyPowerFamily ∷
  ninetyE6MixedInvariant ∷ oneTwentyEightUnqueried ∷
  nineteenSixEightThreePower ∷ sixFiveSixOneZeroPowerFamily ∷
  oneNineSixEightThreeZeroPowerFamily ∷ oneNineSixEightThreeMonster ∷
  oneNineSixEightThreeDivisor ∷ oneNineSixEightFourJ ∷
  oneNineSixEightFourDivisors ∷ []

------------------------------------------------------------------------
-- Router discipline.
------------------------------------------------------------------------

data AuditStage : Set where
  locateRepoRole
  queryTypedFamily
  verifyExactIndexOrInvariant
  attachPrimarySourceQidDewey
  testSameCarrier
  testActionOrIntertwiner : AuditStage

canonicalAuditOrder : List AuditStage
canonicalAuditOrder =
  locateRepoRole ∷ queryTypedFamily ∷ verifyExactIndexOrInvariant ∷
  attachPrimarySourceQidDewey ∷ testSameCarrier ∷ testActionOrIntertwiner ∷ []

record TypedOEISAuditBoundary : Set where
  constructor typed-oeis-audit-boundary
  field
    requestedSeedListRecordedExactly : Bool
    oneNumberMayHaveMultipleTypedRoles : Bool
    sequenceFamilySelectedBeforeSemanticPromotion : Bool
    oeisUsedForNegativeControls : Bool
    e6TwelveRetypedAsCoxeterNotIrrep : Bool
    g2SevenTwentyNineNegativeControlRetained : Bool
    unresolvedNumbersRemainExplicit : Bool
    oeisMembershipCreatesAction : Bool
    qidDeweyCreatesProof : Bool
    nextResidual : String
open TypedOEISAuditBoundary public

canonicalTypedOEISAuditBoundary : TypedOEISAuditBoundary
canonicalTypedOEISAuditBoundary = typed-oeis-audit-boundary
  true true true true true true true false false
  "continue the typed-family scan for 56, 128 and any remaining seed roles; then use direct typed-role hits to rank SAME-OBJECT tests. Highest exceptional target remains the actual Fin90 inertia split followed by a literal 78-to-E6 action intertwiner and a test whether the literal 12 block carries Coxeter/invariant structure from that same E6 action."

priorAudit = PriorAudit.canonical196883MultiView
exceptionalTest = ExceptionalTest.currentExceptionalOEISHypothesisFrontier
e6CoxeterCorrection = E6Coxeter.currentE6CoxeterNinetyCorrectionFrontier
g2NegativeControl = G2Control.canonicalG2SevenTwentyNineNegativeControlBoundary
allPairsBoundary = AllPairs.canonicalWikipediaAllPairsBoundary
