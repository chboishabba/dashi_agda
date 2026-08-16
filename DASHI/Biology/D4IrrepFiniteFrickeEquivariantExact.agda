module DASHI.Biology.D4IrrepFiniteFrickeEquivariantExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Jean-Pierre Serre,
-- "Linear Representations of Finite Groups", Springer, 1977.
-- DOI: 10.1007/978-1-4684-9458-7.
--
-- Nicholas M. Katz and Barry Mazur,
-- "Arithmetic Moduli of Elliptic Curves", Princeton University Press, 1985.
-- DOI: 10.1515/9781400881710.
--
-- Andrew P. Ogg,
-- "Automorphismes de courbes modulaires",
-- Seminaire Delange-Pisot-Poitou 16 (1974-1975), expose 7, pp. 1-8.
-- MR 417184; no DOI assigned.
--
-- DASHI CONTRIBUTION
--
-- The repository already has two ten-state presentations:
--
--   D4IrrepKind x DialecticalOrientation
--   ComplementMode5 x BinaryPhase  <->  T^2 disjoint-union {j}.
--
-- This module constructs a two-sided chart between them and proves the
-- nontrivial equivariance law:
--
--   orientation flip  <->  finite Fricke complement.
--
-- Thus the five D4 representation species and five finite quotient modes can
-- be compared by an actual C2-equivariant carrier equivalence, not by 5 = 5.
-- No claim is made that a quotient mode is itself a linear irreducible
-- subspace or that the finite complement is the analytic Fricke involution.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Product using (_×_; _,_; proj₁; proj₂)

import DASHI.Biology.NonaryCompletionPhaseQuotientExact as Fricke
import DASHI.Biology.TernaryMonsterSymmetryCandidateExact as D4
import DASHI.Foundations.D4SO3NineIrrepRestrictionExact as Spatial

irrepToMode : D4.D4IrrepKind → Fricke.ComplementMode5
irrepToMode D4.A1 = Fricke.mode09
irrepToMode D4.A2 = Fricke.mode18
irrepToMode D4.B1 = Fricke.mode27
irrepToMode D4.B2 = Fricke.mode36
irrepToMode D4.E2 = Fricke.mode45

modeToIrrep : Fricke.ComplementMode5 → D4.D4IrrepKind
modeToIrrep Fricke.mode09 = D4.A1
modeToIrrep Fricke.mode18 = D4.A2
modeToIrrep Fricke.mode27 = D4.B1
modeToIrrep Fricke.mode36 = D4.B2
modeToIrrep Fricke.mode45 = D4.E2

modeAfterIrrep :
  (kind : D4.D4IrrepKind) →
  modeToIrrep (irrepToMode kind) ≡ kind
modeAfterIrrep D4.A1 = refl
modeAfterIrrep D4.A2 = refl
modeAfterIrrep D4.B1 = refl
modeAfterIrrep D4.B2 = refl
modeAfterIrrep D4.E2 = refl

irrepAfterMode :
  (mode : Fricke.ComplementMode5) →
  irrepToMode (modeToIrrep mode) ≡ mode
irrepAfterMode Fricke.mode09 = refl
irrepAfterMode Fricke.mode18 = refl
irrepAfterMode Fricke.mode27 = refl
irrepAfterMode Fricke.mode36 = refl
irrepAfterMode Fricke.mode45 = refl

orientationToPhase :
  D4.DialecticalOrientation → Fricke.BinaryPhase
orientationToPhase D4.positiveOrientation = Fricke.directPhase
orientationToPhase D4.negativeOrientation = Fricke.counterPhase

phaseToOrientation :
  Fricke.BinaryPhase → D4.DialecticalOrientation
phaseToOrientation Fricke.directPhase = D4.positiveOrientation
phaseToOrientation Fricke.counterPhase = D4.negativeOrientation

phaseAfterOrientation :
  (orientation : D4.DialecticalOrientation) →
  phaseToOrientation (orientationToPhase orientation) ≡ orientation
phaseAfterOrientation D4.positiveOrientation = refl
phaseAfterOrientation D4.negativeOrientation = refl

orientationAfterPhase :
  (phase : Fricke.BinaryPhase) →
  orientationToPhase (phaseToOrientation phase) ≡ phase
orientationAfterPhase Fricke.directPhase = refl
orientationAfterPhase Fricke.counterPhase = refl

flipOrientation :
  D4.DialecticalOrientation → D4.DialecticalOrientation
flipOrientation D4.positiveOrientation = D4.negativeOrientation
flipOrientation D4.negativeOrientation = D4.positiveOrientation

flipOrientationInvolutive :
  (orientation : D4.DialecticalOrientation) →
  flipOrientation (flipOrientation orientation) ≡ orientation
flipOrientationInvolutive D4.positiveOrientation = refl
flipOrientationInvolutive D4.negativeOrientation = refl

D4OrientedSector : Set
D4OrientedSector =
  D4.D4IrrepKind × D4.DialecticalOrientation

sectorToCompletedFine :
  D4OrientedSector → Fricke.DecimalCompletionState
sectorToCompletedFine (kind , orientation) =
  Fricke.decodeModePhase
    (irrepToMode kind , orientationToPhase orientation)

completedFineToSector :
  Fricke.DecimalCompletionState → D4OrientedSector
completedFineToSector state =
  modeToIrrep (proj₁ encoded) ,
  phaseToOrientation (proj₂ encoded)
  where
  encoded = Fricke.encodeModePhase state

sectorRoundTrip :
  (sector : D4OrientedSector) →
  completedFineToSector (sectorToCompletedFine sector) ≡ sector
sectorRoundTrip (D4.A1 , D4.positiveOrientation) = refl
sectorRoundTrip (D4.A1 , D4.negativeOrientation) = refl
sectorRoundTrip (D4.A2 , D4.positiveOrientation) = refl
sectorRoundTrip (D4.A2 , D4.negativeOrientation) = refl
sectorRoundTrip (D4.B1 , D4.positiveOrientation) = refl
sectorRoundTrip (D4.B1 , D4.negativeOrientation) = refl
sectorRoundTrip (D4.B2 , D4.positiveOrientation) = refl
sectorRoundTrip (D4.B2 , D4.negativeOrientation) = refl
sectorRoundTrip (D4.E2 , D4.positiveOrientation) = refl
sectorRoundTrip (D4.E2 , D4.negativeOrientation) = refl

completedFineRoundTrip :
  (state : Fricke.DecimalCompletionState) →
  sectorToCompletedFine (completedFineToSector state) ≡ state
completedFineRoundTrip Fricke.d0 = refl
completedFineRoundTrip Fricke.d1 = refl
completedFineRoundTrip Fricke.d2 = refl
completedFineRoundTrip Fricke.d3 = refl
completedFineRoundTrip Fricke.d4 = refl
completedFineRoundTrip Fricke.d5 = refl
completedFineRoundTrip Fricke.d6 = refl
completedFineRoundTrip Fricke.d7 = refl
completedFineRoundTrip Fricke.d8 = refl
completedFineRoundTrip Fricke.j9 = refl

flipSector : D4OrientedSector → D4OrientedSector
flipSector (kind , orientation) =
  kind , flipOrientation orientation

sectorComplementEquivariant :
  (sector : D4OrientedSector) →
  sectorToCompletedFine (flipSector sector)
  ≡ Fricke.complementState (sectorToCompletedFine sector)
sectorComplementEquivariant (D4.A1 , D4.positiveOrientation) = refl
sectorComplementEquivariant (D4.A1 , D4.negativeOrientation) = refl
sectorComplementEquivariant (D4.A2 , D4.positiveOrientation) = refl
sectorComplementEquivariant (D4.A2 , D4.negativeOrientation) = refl
sectorComplementEquivariant (D4.B1 , D4.positiveOrientation) = refl
sectorComplementEquivariant (D4.B1 , D4.negativeOrientation) = refl
sectorComplementEquivariant (D4.B2 , D4.positiveOrientation) = refl
sectorComplementEquivariant (D4.B2 , D4.negativeOrientation) = refl
sectorComplementEquivariant (D4.E2 , D4.positiveOrientation) = refl
sectorComplementEquivariant (D4.E2 , D4.negativeOrientation) = refl

modeForSector :
  D4OrientedSector → Fricke.ComplementMode5
modeForSector sector =
  Fricke.complementMode (sectorToCompletedFine sector)

modeForSectorIsIrrepMode :
  (kind : D4.D4IrrepKind) →
  (orientation : D4.DialecticalOrientation) →
  modeForSector (kind , orientation) ≡ irrepToMode kind
modeForSectorIsIrrepMode D4.A1 D4.positiveOrientation = refl
modeForSectorIsIrrepMode D4.A1 D4.negativeOrientation = refl
modeForSectorIsIrrepMode D4.A2 D4.positiveOrientation = refl
modeForSectorIsIrrepMode D4.A2 D4.negativeOrientation = refl
modeForSectorIsIrrepMode D4.B1 D4.positiveOrientation = refl
modeForSectorIsIrrepMode D4.B1 D4.negativeOrientation = refl
modeForSectorIsIrrepMode D4.B2 D4.positiveOrientation = refl
modeForSectorIsIrrepMode D4.B2 D4.negativeOrientation = refl
modeForSectorIsIrrepMode D4.E2 D4.positiveOrientation = refl
modeForSectorIsIrrepMode D4.E2 D4.negativeOrientation = refl

modeForSectorIgnoresOrientation :
  (sector : D4OrientedSector) →
  modeForSector (flipSector sector) ≡ modeForSector sector
modeForSectorIgnoresOrientation sector
  rewrite sectorComplementEquivariant sector =
  Fricke.complementPreservesMode (sectorToCompletedFine sector)

-- Under the reference chart, the five finite modes carry the actual
-- multiplicities of the spatial SO(3) j=4 -> D4 restriction.
j4MultiplicityAtMode : Fricke.ComplementMode5 → Nat
j4MultiplicityAtMode mode =
  Spatial.j4D4Multiplicity (modeToIrrep mode)

j4Mode09MultiplicityIsTwo :
  j4MultiplicityAtMode Fricke.mode09 ≡ 2
j4Mode09MultiplicityIsTwo = refl

j4Mode18MultiplicityIsOne :
  j4MultiplicityAtMode Fricke.mode18 ≡ 1
j4Mode18MultiplicityIsOne = refl

j4Mode27MultiplicityIsOne :
  j4MultiplicityAtMode Fricke.mode27 ≡ 1
j4Mode27MultiplicityIsOne = refl

j4Mode36MultiplicityIsOne :
  j4MultiplicityAtMode Fricke.mode36 ≡ 1
j4Mode36MultiplicityIsOne = refl

j4Mode45MultiplicityIsTwo :
  j4MultiplicityAtMode Fricke.mode45 ≡ 2
j4Mode45MultiplicityIsTwo = refl

record D4FiniteFrickeEquivariantEquivalence : Set where
  field
    encode : D4OrientedSector → Fricke.DecimalCompletionState
    decode : Fricke.DecimalCompletionState → D4OrientedSector
    decodeEncode :
      (sector : D4OrientedSector) →
      decode (encode sector) ≡ sector
    encodeDecode :
      (state : Fricke.DecimalCompletionState) →
      encode (decode state) ≡ state
    equivariant :
      (sector : D4OrientedSector) →
      encode (flipSector sector)
      ≡ Fricke.complementState (encode sector)

referenceD4FiniteFrickeEquivariantEquivalence :
  D4FiniteFrickeEquivariantEquivalence
referenceD4FiniteFrickeEquivariantEquivalence =
  record
    { encode = sectorToCompletedFine
    ; decode = completedFineToSector
    ; decodeEncode = sectorRoundTrip
    ; encodeDecode = completedFineRoundTrip
    ; equivariant = sectorComplementEquivariant
    }

record D4FiniteFrickeBoundary : Set where
  field
    c2EquivariantTenStateChartConstructed : Bool
    c2EquivariantTenStateChartConstructedIsTrue :
      c2EquivariantTenStateChartConstructed ≡ true
    modeAssignmentClaimedCanonicalFromSources : Bool
    modeAssignmentClaimedCanonicalFromSourcesIsFalse :
      modeAssignmentClaimedCanonicalFromSources ≡ false
    finiteModeIsLiteralIrrepSubspace : Bool
    finiteModeIsLiteralIrrepSubspaceIsFalse :
      finiteModeIsLiteralIrrepSubspace ≡ false
    finiteComplementIsAnalyticFricke : Bool
    finiteComplementIsAnalyticFrickeIsFalse :
      finiteComplementIsAnalyticFricke ≡ false

canonicalD4FiniteFrickeBoundary : D4FiniteFrickeBoundary
canonicalD4FiniteFrickeBoundary =
  record
    { c2EquivariantTenStateChartConstructed = true
    ; c2EquivariantTenStateChartConstructedIsTrue = refl
    ; modeAssignmentClaimedCanonicalFromSources = false
    ; modeAssignmentClaimedCanonicalFromSourcesIsFalse = refl
    ; finiteModeIsLiteralIrrepSubspace = false
    ; finiteModeIsLiteralIrrepSubspaceIsFalse = refl
    ; finiteComplementIsAnalyticFricke = false
    ; finiteComplementIsAnalyticFrickeIsFalse = refl
    }
