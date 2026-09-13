module DASHI.Wikimedia.IbrahimMonster3BSuzukiNinetyPermutationCharacterNoGoExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Attribution
import DASHI.Core.SnowballAttributionProvenanceInvariantExact as Snowball
import DASHI.Wikimedia.IbrahimMonster3BSuzukiMultiplicityCharacterSnowballExact as Suzuki
import DASHI.Wikimedia.IbrahimMonster3BMultiplicityBasisLinearWrongTypeCorrectionExact as WrongType

------------------------------------------------------------------------
-- PURE 90-POINT PERMUTATION ACTION NO-GO
--
-- The source-paid complex degree-12 representation of 6.Suz detects the
-- central order-three element by a nontrivial scalar.  We need no assumption
-- about whether the degree-78 factor is faithful: allow its central scalar to
-- be 1, zeta, or zeta^2.
--
-- In Q(zeta), zeta^2 = -1-zeta.  For the six possible assignments with the
-- 12-block nontrivial, the character of the 12+78 direct sum has coordinates
-- (a,b) in the basis 1,zeta:
--
--   12 zeta   + 78       = ( 78,  12)
--   12 zeta   + 78 zeta  = (  0,  90)
--   12 zeta   + 78 zeta2 = (-78, -66)
--   12 zeta2  + 78       = ( 66, -12)
--   12 zeta2  + 78 zeta  = (-12,  66)
--   12 zeta2  + 78 zeta2 = (-90, -90).
--
-- The zeta coefficient is never zero, hence none of these values is an
-- integer.  But the character of a permutation representation at an element
-- is the number of fixed points, a natural number.  Therefore the source-paid
-- 12+78 multiplicity representation cannot be the pure permutation action
-- Inertia -> Fin 90 -> Fin 90 used by the historical special-case owner.
--
-- This does NOT exclude a monomial representation: a basis vector may be sent
-- to a scalar multiple of another basis vector.  Such a route requires both a
-- permutation and scalar coefficient/cocycle; the old Fin90-only action does
-- not carry those coefficients.
------------------------------------------------------------------------

barracloughWilson : Attribution.AttributedSource
barracloughWilson = Attribution.mkDOISource
  "R. W. Barraclough; R. A. Wilson"
  "The Character Table of a Maximal Subgroup of the Monster"
  "LMS Journal of Computation and Mathematics 10, 161-175"
  "2007"
  "10.1112/S1461157000001352"
  "https://doi.org/10.1112/S1461157000001352"
  Attribution.academicArticleSource
  "primary source for the complex 6.Suz representation used to detect the central scalar and for the source-native 729-times-multiplicity character construction"
  Attribution.publicAttribution

serre : Attribution.AttributedSource
serre = Attribution.mkDOISource
  "Jean-Pierre Serre"
  "Linear Representations of Finite Groups"
  "Springer"
  "1977"
  "10.1007/978-1-4684-9458-7"
  "https://doi.org/10.1007/978-1-4684-9458-7"
  Attribution.academicArticleSource
  "representation-theory calibration: central elements act by scalars on irreducibles, and permutation characters count fixed points"
  Attribution.publicAttribution

barracloughWilsonAttribution = Snowball.canonicalSourceRoleSnowballReceipt barracloughWilson
serreAttribution = Snowball.canonicalSourceRoleSnowballReceipt serre

------------------------------------------------------------------------
-- Exact symbolic receipt from the source-paid degrees and central-phase gate.
------------------------------------------------------------------------

record CyclotomicCoordinate : Set where
  constructor cyclotomic-coordinate
  field
    rationalCoefficient : String
    zetaCoefficient : String
open CyclotomicCoordinate public

record CentralPhaseCase : Set where
  constructor central-phase-case
  field
    twelvePhase : String
    seventyEightPhase : String
    value : CyclotomicCoordinate
    zetaCoefficientNonzero : Bool
open CentralPhaseCase public

case12z78one : CentralPhaseCase
case12z78one = central-phase-case "zeta" "1" (cyclotomic-coordinate "78" "12") true

case12z78z : CentralPhaseCase
case12z78z = central-phase-case "zeta" "zeta" (cyclotomic-coordinate "0" "90") true

case12z78z2 : CentralPhaseCase
case12z78z2 = central-phase-case "zeta" "zeta^2" (cyclotomic-coordinate "-78" "-66") true

case12z2_78one : CentralPhaseCase
case12z2_78one = central-phase-case "zeta^2" "1" (cyclotomic-coordinate "66" "-12") true

case12z2_78z : CentralPhaseCase
case12z2_78z = central-phase-case "zeta^2" "zeta" (cyclotomic-coordinate "-12" "66") true

case12z2_78z2 : CentralPhaseCase
case12z2_78z2 = central-phase-case "zeta^2" "zeta^2" (cyclotomic-coordinate "-90" "-90") true

record PermutationCharacterNoGoReceipt : Set where
  constructor permutation-character-no-go-receipt
  field
    twelveDegree : Nat
    seventyEightDegree : Nat
    sourcePaidTwelveCentralPhaseNontrivial : Bool
    seventyEightFaithfulnessRequired : Bool
    sourceAdmissibleCaseCount : Nat
    everyCaseHasNonzeroZetaCoefficient : Bool
    pureNinetyPointPermutationCharacterCompatible : Bool
    monomialWithScalarCoefficientsExcluded : Bool
    pythonProducerWritten : Bool
    ciExecutionReceiptObserved : Bool
open PermutationCharacterNoGoReceipt public

canonicalPermutationCharacterNoGoReceipt : PermutationCharacterNoGoReceipt
canonicalPermutationCharacterNoGoReceipt = permutation-character-no-go-receipt
  12 78 true false 6 true false false true false

------------------------------------------------------------------------
-- WrongType / non-promotion boundaries.
------------------------------------------------------------------------

data PurePermutationCharacterCanHaveNonintegralCentralValue : Set where
data NonPermutationCreatesActualLinearAction : Set where
data NonPermutationExcludesMonomialScalarAction : Set where
data QidCreatesPermutationNoGo : Set where
data DeweyCreatesPermutationNoGo : Set where
data OeisCreatesPermutationNoGo : Set where

permutationCharacterCentralValueMustBeIntegral :
  PurePermutationCharacterCanHaveNonintegralCentralValue → ⊥
permutationCharacterCentralValueMustBeIntegral ()

noGoDoesNotCreateLinearAction : NonPermutationCreatesActualLinearAction → ⊥
noGoDoesNotCreateLinearAction ()

noGoDoesNotExcludeMonomialScalarAction : NonPermutationExcludesMonomialScalarAction → ⊥
noGoDoesNotExcludeMonomialScalarAction ()

qidDoesNotCreateNoGo : QidCreatesPermutationNoGo → ⊥
qidDoesNotCreateNoGo ()

deweyDoesNotCreateNoGo : DeweyCreatesPermutationNoGo → ⊥
deweyDoesNotCreateNoGo ()

oeisDoesNotCreateNoGo : OeisCreatesPermutationNoGo → ⊥
oeisDoesNotCreateNoGo ()

------------------------------------------------------------------------
-- Typed external coordinates.
------------------------------------------------------------------------

record PermutationNoGoExternalCoordinates : Set where
  constructor permutation-no-go-external-coordinates
  field
    groupRepresentationQid : String
    representationCharacterQid : String
    finiteGroupQid : String
    groupRepresentationDewey : String
    finiteGroupDewey : String
    oeisCoordinate : String
    oeisHasNoGoAuthority : Bool
open PermutationNoGoExternalCoordinates public

canonicalPermutationNoGoExternalCoordinates : PermutationNoGoExternalCoordinates
canonicalPermutationNoGoExternalCoordinates = permutation-no-go-external-coordinates
  "Q1055807"
  "Q600043"
  "Q1057968"
  "512.22"
  "512.23"
  "A005052 remains numeric provenance for 90=10*3^2 only; it does not prove a character is or is not a permutation character"
  false

------------------------------------------------------------------------
-- Corrected frontier.
------------------------------------------------------------------------

record SuzukiNinetyPermutationNoGoFrontier : Set where
  constructor suzuki-ninety-permutation-no-go-frontier
  field
    primaryComplexTwelveCentralScalarPaid : Bool
    seventyEightCentralKernelNeededForNoGo : Bool
    exactCyclotomicProducerWritten : Bool
    exactSixCaseArithmeticChecked : Bool
    pureFinNinetyPermutationRouteRefuted : Bool
    monomialScalarRouteStillPossible : Bool
    actualLinearMultiplicityActionPaid : Bool
    nextResidual : String
open SuzukiNinetyPermutationNoGoFrontier public

currentSuzukiNinetyPermutationNoGoFrontier : SuzukiNinetyPermutationNoGoFrontier
currentSuzukiNinetyPermutationNoGoFrontier = suzuki-ninety-permutation-no-go-frontier
  true false true true true true false
  "retire the historical pure Fin90 permutation action as a candidate for the source-paid 12+78 Suzuki multiplicity representation. The canonical mandatory target remains an actual linear S_zeta action on a ninety-dimensional vector carrier. A monomial-basis route, if pursued, must be typed separately with scalar coefficients/phases in addition to the basis permutation. The next same-object payment is a linear evaluation/intertwiner W_zeta ≃ H_zeta tensor S_zeta, followed by the generic isotypic 12+78 split."

suzukiFrontier : Suzuki.SuzukiMultiplicityFrontier
suzukiFrontier = Suzuki.currentSuzukiMultiplicityFrontier

wrongTypeFrontier : WrongType.MultiplicityWrongTypeFrontier
wrongTypeFrontier = WrongType.currentMultiplicityWrongTypeFrontier
