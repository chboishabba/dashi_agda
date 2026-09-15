module DASHI.Wikimedia.IbrahimMonster3BOEISSameIntegerRoleCollisionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Attribution
import DASHI.Core.SnowballAttributionProvenanceInvariantExact as Snowball
import DASHI.Wikimedia.IbrahimMonster3BModernRestrictionTwelveSeventyEightOccurrenceSnowballExact as Occurrence

------------------------------------------------------------------------
-- OEIS SAME-INTEGER / DIFFERENT-ROLE COLLISION BOUNDARY
--
-- OEIS is valuable here precisely because it gives us both useful numerical
-- coordinates and a concrete warning against numeral-based object identity.
--
-- In particular, 17496 occurs in two genuinely Monster-adjacent contexts:
--
--   * the source-paid N(3B) restriction degree
--         17496 = 2 * 729 * 12,
--
--   * OEIS A058678, the class-42d McKay--Thompson series, where 17496 is an
--     unrelated series coefficient.
--
-- Therefore even
--
--   same integer + Monster context + genuine OEIS record
--
-- does NOT identify the same representation, character constituent, action,
-- basis, intertwiner, or same-object carrier.
------------------------------------------------------------------------

pow : Nat → Nat → Nat
pow b zero = 1
pow b (suc n) = b * pow b n

a000244 : Nat → Nat
a000244 n = pow 3 n

a005052 : Nat → Nat
a005052 n = 10 * pow 3 n

sevenTwentyNineIsA000244Level6 : a000244 6 ≡ 729
sevenTwentyNineIsA000244Level6 = refl

ninetyIsA005052Level2 : a005052 2 ≡ 90
ninetyIsA005052Level2 = refl

sixFiveSixOneZeroIsA005052Level8 : a005052 8 ≡ 65610
sixFiveSixOneZeroIsA005052Level8 = refl

oneNineSixEightThreeZeroIsA005052Level9 : a005052 9 ≡ 196830
oneNineSixEightThreeZeroIsA005052Level9 = refl

restriction17496 : Nat
restriction17496 = 17496

mcKayThompson42dObserved17496 : Nat
mcKayThompson42dObserved17496 = 17496

same17496Integer : restriction17496 ≡ mcKayThompson42dObserved17496
same17496Integer = refl

restriction17496Factorisation : 2 * 729 * 12 ≡ restriction17496
restriction17496Factorisation = Occurrence.twelvePairedDegree

restriction113724Factorisation : 2 * 729 * 78 ≡ 113724
restriction113724Factorisation = Occurrence.seventyEightPairedDegree

------------------------------------------------------------------------
-- Source-bounded OEIS manifestations.
------------------------------------------------------------------------

oeisA000244 : Attribution.AttributedSource
oeisA000244 = Attribution.mkNoDOISource
  "OEIS Foundation Inc.; OEIS contributors"
  "A000244: Powers of 3"
  "On-Line Encyclopedia of Integer Sequences"
  "retrieved 2026-09-15"
  "https://oeis.org/A000244"
  (Attribution.namedSourceKind "integer-sequence database record")
  "numerical provenance for 3^n, including 3^6 = 729; not Stone-von Neumann or Monster representation authority"
  Attribution.publicAttribution

oeisA005052 : Attribution.AttributedSource
oeisA005052 = Attribution.mkNoDOISource
  "OEIS Foundation Inc.; OEIS contributors"
  "A005052: a(n) = 10*3^n"
  "On-Line Encyclopedia of Integer Sequences"
  "retrieved 2026-09-15"
  "https://oeis.org/A005052"
  (Attribution.namedSourceKind "integer-sequence database record")
  "numerical provenance for 90, 65610, and 196830 in the 10*3^n ladder; not character or same-object authority"
  Attribution.publicAttribution

oeisA001379 : Attribution.AttributedSource
oeisA001379 = Attribution.mkNoDOISource
  "N. J. A. Sloane; OEIS contributors"
  "A001379: Degrees of irreducible representations of Monster group M"
  "On-Line Encyclopedia of Integer Sequences"
  "retrieved 2026-09-15"
  "https://oeis.org/A001379"
  (Attribution.namedSourceKind "integer-sequence database record")
  "Monster-degree navigation/provenance including 196883; not a replacement for the ATLAS or a same-action restriction receipt"
  Attribution.publicAttribution

oeisA014708 : Attribution.AttributedSource
oeisA014708 = Attribution.mkNoDOISource
  "N. J. A. Sloane; OEIS contributors"
  "A014708: Coefficients of the modular function J = j - 744"
  "On-Line Encyclopedia of Integer Sequences"
  "retrieved 2026-09-15"
  "https://oeis.org/A014708"
  (Attribution.namedSourceKind "integer-sequence database record")
  "numerical/modular-series provenance including the 196884 q coefficient and Monster 1A cross-reference; not VOA same-object proof"
  Attribution.publicAttribution

oeisA058678 : Attribution.AttributedSource
oeisA058678 = Attribution.mkNoDOISource
  "N. J. A. Sloane; G. C. Greubel; OEIS contributors"
  "A058678: McKay-Thompson series of class 42d for Monster"
  "On-Line Encyclopedia of Integer Sequences"
  "retrieved 2026-09-15"
  "https://oeis.org/A058678"
  (Attribution.namedSourceKind "integer-sequence database record")
  "Monster-adjacent numerical provenance whose listed coefficients include 17496; explicitly not the N(3B) 17496 restriction constituent"
  Attribution.publicAttribution

oeisA199014 : Attribution.AttributedSource
oeisA199014 = Attribution.mkNoDOISource
  "Omar E. Pol; OEIS contributors"
  "A199014: Divisors of 196884"
  "On-Line Encyclopedia of Integer Sequences"
  "retrieved 2026-09-15"
  "https://oeis.org/A199014"
  (Attribution.namedSourceKind "integer-sequence database record")
  "arithmetic divisor provenance for 196884; not moonshine or representation authority"
  Attribution.publicAttribution

oeisA309510 : Attribution.AttributedSource
oeisA309510 = Attribution.mkNoDOISource
  "Jelle Herold; OEIS contributors"
  "A309510: Divisors of 196883"
  "On-Line Encyclopedia of Integer Sequences"
  "retrieved 2026-09-15"
  "https://oeis.org/A309510"
  (Attribution.namedSourceKind "integer-sequence database record")
  "arithmetic divisor provenance for 196883 with Monster-degree commentary; not a construction of the Monster representation"
  Attribution.publicAttribution

a000244Attribution = Snowball.canonicalSourceRoleSnowballReceipt oeisA000244
a005052Attribution = Snowball.canonicalSourceRoleSnowballReceipt oeisA005052
a001379Attribution = Snowball.canonicalSourceRoleSnowballReceipt oeisA001379
a014708Attribution = Snowball.canonicalSourceRoleSnowballReceipt oeisA014708
a058678Attribution = Snowball.canonicalSourceRoleSnowballReceipt oeisA058678
a199014Attribution = Snowball.canonicalSourceRoleSnowballReceipt oeisA199014
a309510Attribution = Snowball.canonicalSourceRoleSnowballReceipt oeisA309510

------------------------------------------------------------------------
-- Role-indexed coordinates.  Equality of observed integers is intentionally
-- separated from identity of the represented object.
------------------------------------------------------------------------

record OEISRoleCoordinate : Set where
  constructor oeis-role-coordinate
  field
    sequenceId : String
    sequenceMeaning : String
    observedInteger : Nat
    roleInThisLane : String
    sameObjectPaid : Bool
    theoremAuthorityPaid : Bool
open OEISRoleCoordinate public

powersOfThree729 : OEISRoleCoordinate
powersOfThree729 = oeis-role-coordinate
  "A000244" "powers of 3" 729
  "numerical coordinate for the 3^6 Schrödinger/Heisenberg degree" false false

tenTimesPowersNinety : OEISRoleCoordinate
tenTimesPowersNinety = oeis-role-coordinate
  "A005052" "10 times powers of 3" 90
  "numerical coordinate for 10*3^2" false false

monsterDegree196883 : OEISRoleCoordinate
monsterDegree196883 = oeis-role-coordinate
  "A001379" "degrees of irreducible representations of Monster group M" 196883
  "Monster irreducible-degree provenance/navigation" false false

jCoefficient196884 : OEISRoleCoordinate
jCoefficient196884 = oeis-role-coordinate
  "A014708" "coefficients of J = j - 744 / Monster 1A McKay-Thompson series" 196884
  "q-coefficient provenance/navigation" false false

mckayThompson42d17496 : OEISRoleCoordinate
mckayThompson42d17496 = oeis-role-coordinate
  "A058678" "McKay-Thompson series of Monster class 42d" 17496
  "series coefficient; deliberately not the N(3B) restriction constituent" false false

divisors196884 : OEISRoleCoordinate
divisors196884 = oeis-role-coordinate
  "A199014" "divisors of 196884" 196884
  "integer/divisor surface only" false false

divisors196883 : OEISRoleCoordinate
divisors196883 = oeis-role-coordinate
  "A309510" "divisors of 196883" 196883
  "integer/divisor surface only" false false

------------------------------------------------------------------------
-- Same-number collision counterexample.
------------------------------------------------------------------------

record SameIntegerRoleCollision : Set where
  constructor same-integer-role-collision
  field
    leftSequence : String
    rightSource : String
    commonInteger : Nat
    leftRole : String
    rightRole : String
    integerEqualityPaid : Bool
    bothMonsterAdjacent : Bool
    sameObjectPaid : Bool
    sameRepresentationPaid : Bool
    sameCharacterRolePaid : Bool
open SameIntegerRoleCollision public

monster17496Collision : SameIntegerRoleCollision
monster17496Collision = same-integer-role-collision
  "OEIS A058678 / Monster class 42d McKay-Thompson series"
  "An-Wilson + modern N(3B) restriction occurrence"
  17496
  "42d McKay-Thompson coefficient"
  "degree of the source-paid N(3B) constituent factoring as 2*729*12"
  true true false false false

sameIntegerCollisionCounterexamplePaid : Bool
sameIntegerCollisionCounterexamplePaid = true

oeisPaysNumericalCoordinateOnly : Bool
oeisPaysNumericalCoordinateOnly = true

------------------------------------------------------------------------
-- WrongType / non-promotion firewalls.
------------------------------------------------------------------------

data SameIntegerMonsterContextIdentifiesObject : Set where
data McKayThompson42d17496IdentifiesRestriction17496 : Set where
data A001379CreatesLiteralMonsterAction : Set where
data A014708CreatesVOASameObjectWeld : Set where
data A000244CreatesStoneVonNeumannTheorem : Set where
data A005052CreatesMultiplicityRepresentation : Set where
data DivisorSequenceCreatesRepresentation : Set where

sameIntegerMonsterContextDoesNotIdentifyObject :
  SameIntegerMonsterContextIdentifiesObject → ⊥
sameIntegerMonsterContextDoesNotIdentifyObject ()

mcKayThompson42d17496DoesNotIdentifyRestriction17496 :
  McKayThompson42d17496IdentifiesRestriction17496 → ⊥
mcKayThompson42d17496DoesNotIdentifyRestriction17496 ()

a001379DoesNotCreateLiteralAction : A001379CreatesLiteralMonsterAction → ⊥
a001379DoesNotCreateLiteralAction ()

a014708DoesNotCreateVOAWeld : A014708CreatesVOASameObjectWeld → ⊥
a014708DoesNotCreateVOAWeld ()

a000244DoesNotCreateStoneVonNeumann : A000244CreatesStoneVonNeumannTheorem → ⊥
a000244DoesNotCreateStoneVonNeumann ()

a005052DoesNotCreateMultiplicityRepresentation : A005052CreatesMultiplicityRepresentation → ⊥
a005052DoesNotCreateMultiplicityRepresentation ()

divisorSequenceDoesNotCreateRepresentation : DivisorSequenceCreatesRepresentation → ⊥
divisorSequenceDoesNotCreateRepresentation ()

------------------------------------------------------------------------
-- Pareto frontier.
------------------------------------------------------------------------

record OEISSameIntegerCollisionFrontier : Set where
  constructor oeis-same-integer-collision-frontier
  field
    powersOfThreeCoordinatePaid : Bool
    tenTimesPowersCoordinatePaid : Bool
    monsterDegreeCoordinatePaid : Bool
    jCoefficientCoordinatePaid : Bool
    monster42dCoordinatePaid : Bool
    divisor196883CoordinatePaid : Bool
    divisor196884CoordinatePaid : Bool
    restriction17496OccurrencePaidUpstream : Bool
    sameIntegerCollisionPaid : Bool
    sameIntegerCreatesSameObject : Bool
    oeisCreatesCharacterOccurrence : Bool
    nextResidual : String
open OEISSameIntegerCollisionFrontier public

currentOEISSameIntegerCollisionFrontier : OEISSameIntegerCollisionFrontier
currentOEISSameIntegerCollisionFrontier = oeis-same-integer-collision-frontier
  true true true true true true true true true false false
  "retain OEIS as role-indexed numerical/search provenance. In particular, use A058678's independent Monster-context 17496 collision as a regression against numeral-based promotion. The theorem-bearing 12+78 lane must continue through the source-native N(3B) restriction/action and same-action character/intertwiner receipts; no OEIS occurrence, even a Monster-related one with the same integer, can pay that identity step."

restrictionOccurrenceFrontier : Occurrence.RestrictionOccurrenceFrontier
restrictionOccurrenceFrontier = Occurrence.currentRestrictionOccurrenceFrontier
