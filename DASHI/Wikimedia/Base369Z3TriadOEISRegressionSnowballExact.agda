module DASHI.Wikimedia.Base369Z3TriadOEISRegressionSnowballExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Attribution
import DASHI.Core.SnowballAttributionProvenanceInvariantExact as AttributionSnowball
import DASHI.Wikimedia.SnowballExternalIdentityAvailabilityExact as Identity
import DASHI.Physics.Closure.Base369Ternary27Z3TriadRegressionExact as Triad
import DASHI.Wikimedia.Base369OEISWikidataTeslaSnowballExact as Power3
import DASHI.Wikimedia.WikipediaAllPairsPrunedMergeSnowballExact as AllPairs

------------------------------------------------------------------------
-- OEIS REGRESSION SNOWBALL FOR THE FINITE Z^3 TRIAD FIXTURE
--
-- External sequence coordinates inspected 2026-09-10:
--   A000244 = powers of 3: 1,3,9,27,...,19683,...
--   A000420 = powers of 7: 1,7,49,343,...
--
-- The first sequence is already attached to the Base369 3/9/27 cardinality
-- lane.  The second independently supplies an exact external numerical
-- coordinate for the new raw ordered cutoff-one triad count 343 = 7^3.
-- Neither OEIS sequence is a source for Navier-Stokes resonance semantics.
------------------------------------------------------------------------

oeisA000420Source : Attribution.AttributedSource
oeisA000420Source = Attribution.mkNoDOISource
  "N. J. A. Sloane and OEIS contributors"
  "A000420: Powers of 7"
  "The On-Line Encyclopedia of Integer Sequences"
  "continuously revised"
  "https://oeis.org/A000420"
  (Attribution.namedSourceKind "mathematical sequence database")
  "external numerical identity for powers 7^n; used only to cross-check the independently derived finite triad count 343"
  Attribution.publicAttribution

oeisA000420Attribution : AttributionSnowball.SourceRoleSnowballReceipt oeisA000420Source
oeisA000420Attribution = AttributionSnowball.canonicalSourceRoleSnowballReceipt oeisA000420Source

oeisA000420Id : Identity.ExternalIdentityDemand
oeisA000420Id = Identity.mkOptionalIdentityDemand
  "Base369/Z3 finite triad regression snowball"
  "powers-of-seven sequence identity"
  "OEIS A000420"
  Identity.officialIdentifier
  (Identity.verified "A000420" "OEIS inspected 2026-09-10")

rawTriadCount : Nat
rawTriadCount = Triad.rawOrderedBoundedTriadCount

rawTriadCountIs343 : rawTriadCount ≡ 343
rawTriadCountIs343 = Triad.rawOrderedBoundedTriadCountIs343

record OEISTriadNumericalSeam : Set where
  constructor oeis-triad-numerical-seam
  field
    internalCountReference : String
    externalSequenceId : String
    externalTermReference : String
    internalCount : Nat
    exactCountPayment : internalCount ≡ 343
    sevenCoordinateChoicesPerDimension : Bool
    threeIndependentCoordinates : Bool
    oeisAuthoredTriadEnumeration : Bool
    sequenceMembershipCreatesNSMeaning : Bool
open OEISTriadNumericalSeam public

canonicalOEISTriadNumericalSeam : OEISTriadNumericalSeam
canonicalOEISTriadNumericalSeam = oeis-triad-numerical-seam
  "Base369Ternary27Z3TriadRegressionExact.rawOrderedBoundedTriadCount"
  "A000420"
  "7^3 = 343"
  rawTriadCount
  rawTriadCountIs343
  true true false false

------------------------------------------------------------------------
-- Two independent OEIS fibres now coexist.
------------------------------------------------------------------------

record Base369OEISMultiFibre : Set where
  constructor base369-oeis-multi-fibre
  field
    powerThreeSequence : String
    powerSevenSequence : String
    powerThreeRole : String
    powerSevenRole : String
    sameSequenceClaimed : Bool
    sharedNumericTermCreatesSharedSemantics : Bool
    allPairsComparisonAllowed : Bool
open Base369OEISMultiFibre public

canonicalBase369OEISMultiFibre : Base369OEISMultiFibre
canonicalBase369OEISMultiFibre = base369-oeis-multi-fibre
  "A000244"
  "A000420"
  "3/9/27/19683 external power-of-three coordinates"
  "7/49/343 external power-of-seven coordinates; 343 cross-checks raw cutoff-one triad count"
  false false true

powerThreeIdentityRetained : Identity.ExternalIdentityDemand
powerThreeIdentityRetained = Power3.oeisA000244Id

allPairsBoundary : AllPairs.WikipediaAllPairsBoundary
allPairsBoundary = AllPairs.canonicalWikipediaAllPairsBoundary

------------------------------------------------------------------------
-- Snowball interpretation.
------------------------------------------------------------------------

data TriadOEISSnowballAxis : Set where
  coordinateChoiceCountAxis : TriadOEISSnowballAxis
  productDimensionAxis : TriadOEISSnowballAxis
  rawOrderedTriadCountAxis : TriadOEISSnowballAxis
  nonzeroTriadCountAxis : TriadOEISSnowballAxis
  conjugacyOrbitAxis : TriadOEISSnowballAxis
  schurWeightAxis : TriadOEISSnowballAxis
  oeisSequenceIdentityAxis : TriadOEISSnowballAxis

record TriadOEISSnowballBoundary : Set where
  constructor triad-oeis-snowball-boundary
  field
    raw343NumericalIdentityPaid : Bool
    literalEnumerationLength343Paid : Bool
    nonzeroSubcountPaid : Bool
    conjugacyOrbitCountPaid : Bool
    schurWeightedRegressionPaid : Bool
    oeisSequenceCanCrossCheckNumericResult : Bool
    oeisSequenceCanCreatePhysicalInterpretation : Bool
    failedNumericMatchMayRemainResidual : Bool
open TriadOEISSnowballBoundary public

canonicalTriadOEISSnowballBoundary : TriadOEISSnowballBoundary
canonicalTriadOEISSnowballBoundary = triad-oeis-snowball-boundary
  true false false false false true false true

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data A000420CreatesNavierStokesTriads : Set where
data Numeric343CreatesEnumerationBijection : Set where
data Same343CreatesSameObject : Set where
data OEISIdentityPaysSchurBound : Set where

a000420DoesNotCreateTriads : A000420CreatesNavierStokesTriads → ⊥
a000420DoesNotCreateTriads ()

numericCountDoesNotCreateBijection : Numeric343CreatesEnumerationBijection → ⊥
numericCountDoesNotCreateBijection ()

sameNumberDoesNotCreateSameObject : Same343CreatesSameObject → ⊥
sameNumberDoesNotCreateSameObject ()

oeisDoesNotPaySchurBound : OEISIdentityPaysSchurBound → ⊥
oeisDoesNotPaySchurBound ()
