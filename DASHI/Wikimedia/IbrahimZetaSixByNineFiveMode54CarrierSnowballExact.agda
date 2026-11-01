module DASHI.Wikimedia.IbrahimZetaSixByNineFiveMode54CarrierSnowballExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Product using (_×_; _,_)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Attribution
import DASHI.Core.SnowballAttributionProvenanceInvariantExact as AttributionSnowball
import DASHI.Foundations.SSPTritCarrier as SSP
import DASHI.Foundations.Base369FiveModePhaseQuotientExact as Five
import DASHI.Foundations.Base369Ternary27HypervoxelFabricGeometryExact as Geometry
import DASHI.Moonshine.Base369ZetaHeisenbergFiftyFourCarrierExact as Zeta
import DASHI.Moonshine.Base369MonsterFiftyFourFiveModeResidualActionBidiExact as Base
import DASHI.Wikimedia.IbrahimZeta54AlbertPair53SnowballAttributionBidiExact as Albert

------------------------------------------------------------------------
-- EXACT 6 x 9 CARRIER CHART
--
-- Zeta side:
--   ZetaTrit6 x Nonary9Point
--
-- Base residual-action skeleton:
--   SecondarySector6 x ModePhaseQuotient9.
--
-- This owner pays a finite two-sided carrier chart chosen so that
--
--   (zetaSheet, zeroTrit)          <-> distinguishedSector
--   (zeroTrit, zeroTrit) nonary    <-> identityMode
--
-- and therefore the already-selected zeta-sheet origin is exactly the Base369
-- distinguished invariant point.  This is a carrier/address recognition only;
-- it does not make the chosen six-way chart a representation-theoretic
-- identification and does not inhabit the actual Monster action recognition.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- 1. Nine-state chart. Center maps to the existing identityMode.
------------------------------------------------------------------------

nonaryToModePhase : Zeta.Nonary9Point → Five.ModePhaseQuotient9
nonaryToModePhase (Zeta.nonary9Point SSP.sspNegOne SSP.sspNegOne) = Five.A2negative
nonaryToModePhase (Zeta.nonary9Point SSP.sspNegOne SSP.sspZero) = Five.A2positive
nonaryToModePhase (Zeta.nonary9Point SSP.sspNegOne SSP.sspPosOne) = Five.B1negative
nonaryToModePhase (Zeta.nonary9Point SSP.sspZero SSP.sspNegOne) = Five.B1positive
nonaryToModePhase (Zeta.nonary9Point SSP.sspZero SSP.sspZero) = Five.identityMode
nonaryToModePhase (Zeta.nonary9Point SSP.sspZero SSP.sspPosOne) = Five.B2negative
nonaryToModePhase (Zeta.nonary9Point SSP.sspPosOne SSP.sspNegOne) = Five.B2positive
nonaryToModePhase (Zeta.nonary9Point SSP.sspPosOne SSP.sspZero) = Five.Enegative
nonaryToModePhase (Zeta.nonary9Point SSP.sspPosOne SSP.sspPosOne) = Five.Epositive

modePhaseToNonary : Five.ModePhaseQuotient9 → Zeta.Nonary9Point
modePhaseToNonary Five.A2negative = Zeta.nonary9Point SSP.sspNegOne SSP.sspNegOne
modePhaseToNonary Five.A2positive = Zeta.nonary9Point SSP.sspNegOne SSP.sspZero
modePhaseToNonary Five.B1negative = Zeta.nonary9Point SSP.sspNegOne SSP.sspPosOne
modePhaseToNonary Five.B1positive = Zeta.nonary9Point SSP.sspZero SSP.sspNegOne
modePhaseToNonary Five.identityMode = Zeta.nonary9Point SSP.sspZero SSP.sspZero
modePhaseToNonary Five.B2negative = Zeta.nonary9Point SSP.sspZero SSP.sspPosOne
modePhaseToNonary Five.B2positive = Zeta.nonary9Point SSP.sspPosOne SSP.sspNegOne
modePhaseToNonary Five.Enegative = Zeta.nonary9Point SSP.sspPosOne SSP.sspZero
modePhaseToNonary Five.Epositive = Zeta.nonary9Point SSP.sspPosOne SSP.sspPosOne

nonaryModePhaseRoundTrip :
  (p : Zeta.Nonary9Point) → modePhaseToNonary (nonaryToModePhase p) ≡ p
nonaryModePhaseRoundTrip (Zeta.nonary9Point SSP.sspNegOne SSP.sspNegOne) = refl
nonaryModePhaseRoundTrip (Zeta.nonary9Point SSP.sspNegOne SSP.sspZero) = refl
nonaryModePhaseRoundTrip (Zeta.nonary9Point SSP.sspNegOne SSP.sspPosOne) = refl
nonaryModePhaseRoundTrip (Zeta.nonary9Point SSP.sspZero SSP.sspNegOne) = refl
nonaryModePhaseRoundTrip (Zeta.nonary9Point SSP.sspZero SSP.sspZero) = refl
nonaryModePhaseRoundTrip (Zeta.nonary9Point SSP.sspZero SSP.sspPosOne) = refl
nonaryModePhaseRoundTrip (Zeta.nonary9Point SSP.sspPosOne SSP.sspNegOne) = refl
nonaryModePhaseRoundTrip (Zeta.nonary9Point SSP.sspPosOne SSP.sspZero) = refl
nonaryModePhaseRoundTrip (Zeta.nonary9Point SSP.sspPosOne SSP.sspPosOne) = refl

modePhaseNonaryRoundTrip :
  (s : Five.ModePhaseQuotient9) → nonaryToModePhase (modePhaseToNonary s) ≡ s
modePhaseNonaryRoundTrip Five.identityMode = refl
modePhaseNonaryRoundTrip Five.A2negative = refl
modePhaseNonaryRoundTrip Five.A2positive = refl
modePhaseNonaryRoundTrip Five.B1negative = refl
modePhaseNonaryRoundTrip Five.B1positive = refl
modePhaseNonaryRoundTrip Five.B2negative = refl
modePhaseNonaryRoundTrip Five.B2positive = refl
modePhaseNonaryRoundTrip Five.Enegative = refl
modePhaseNonaryRoundTrip Five.Epositive = refl

centerMapsToIdentity :
  nonaryToModePhase (Zeta.nonary9Point SSP.sspZero SSP.sspZero) ≡ Five.identityMode
centerMapsToIdentity = refl

------------------------------------------------------------------------
-- 2. Six-state chart. One zeta/trit coordinate is deliberately distinguished.
------------------------------------------------------------------------

zetaTritToSecondarySector : Zeta.ZetaTrit6 → Base.SecondarySector6
zetaTritToSecondarySector (Zeta.zetaTrit6 Zeta.zetaSheet SSP.sspNegOne) =
  Base.completeSector Five.A1
zetaTritToSecondarySector (Zeta.zetaTrit6 Zeta.zetaSheet SSP.sspZero) =
  Base.distinguishedSector
zetaTritToSecondarySector (Zeta.zetaTrit6 Zeta.zetaSheet SSP.sspPosOne) =
  Base.completeSector Five.A2
zetaTritToSecondarySector (Zeta.zetaTrit6 Zeta.inverseZetaSheet SSP.sspNegOne) =
  Base.completeSector Five.B1
zetaTritToSecondarySector (Zeta.zetaTrit6 Zeta.inverseZetaSheet SSP.sspZero) =
  Base.completeSector Five.B2
zetaTritToSecondarySector (Zeta.zetaTrit6 Zeta.inverseZetaSheet SSP.sspPosOne) =
  Base.completeSector Five.E

secondarySectorToZetaTrit : Base.SecondarySector6 → Zeta.ZetaTrit6
secondarySectorToZetaTrit (Base.completeSector Five.A1) =
  Zeta.zetaTrit6 Zeta.zetaSheet SSP.sspNegOne
secondarySectorToZetaTrit Base.distinguishedSector =
  Zeta.zetaTrit6 Zeta.zetaSheet SSP.sspZero
secondarySectorToZetaTrit (Base.completeSector Five.A2) =
  Zeta.zetaTrit6 Zeta.zetaSheet SSP.sspPosOne
secondarySectorToZetaTrit (Base.completeSector Five.B1) =
  Zeta.zetaTrit6 Zeta.inverseZetaSheet SSP.sspNegOne
secondarySectorToZetaTrit (Base.completeSector Five.B2) =
  Zeta.zetaTrit6 Zeta.inverseZetaSheet SSP.sspZero
secondarySectorToZetaTrit (Base.completeSector Five.E) =
  Zeta.zetaTrit6 Zeta.inverseZetaSheet SSP.sspPosOne

zetaTritSectorRoundTrip :
  (z : Zeta.ZetaTrit6) → secondarySectorToZetaTrit (zetaTritToSecondarySector z) ≡ z
zetaTritSectorRoundTrip (Zeta.zetaTrit6 Zeta.zetaSheet SSP.sspNegOne) = refl
zetaTritSectorRoundTrip (Zeta.zetaTrit6 Zeta.zetaSheet SSP.sspZero) = refl
zetaTritSectorRoundTrip (Zeta.zetaTrit6 Zeta.zetaSheet SSP.sspPosOne) = refl
zetaTritSectorRoundTrip (Zeta.zetaTrit6 Zeta.inverseZetaSheet SSP.sspNegOne) = refl
zetaTritSectorRoundTrip (Zeta.zetaTrit6 Zeta.inverseZetaSheet SSP.sspZero) = refl
zetaTritSectorRoundTrip (Zeta.zetaTrit6 Zeta.inverseZetaSheet SSP.sspPosOne) = refl

sectorZetaTritRoundTrip :
  (s : Base.SecondarySector6) → zetaTritToSecondarySector (secondarySectorToZetaTrit s) ≡ s
sectorZetaTritRoundTrip (Base.completeSector Five.A1) = refl
sectorZetaTritRoundTrip Base.distinguishedSector = refl
sectorZetaTritRoundTrip (Base.completeSector Five.A2) = refl
sectorZetaTritRoundTrip (Base.completeSector Five.B1) = refl
sectorZetaTritRoundTrip (Base.completeSector Five.B2) = refl
sectorZetaTritRoundTrip (Base.completeSector Five.E) = refl

------------------------------------------------------------------------
-- 3. Product chart: the existing two 54-carrier skeletons are now bijective.
------------------------------------------------------------------------

sixByNineToBase54 : Zeta.SixByNineSite → Base.SecondaryCell54
sixByNineToBase54 (Zeta.sixByNineSite six nine) =
  zetaTritToSecondarySector six , nonaryToModePhase nine

base54ToSixByNine : Base.SecondaryCell54 → Zeta.SixByNineSite
base54ToSixByNine (sector , state) =
  Zeta.sixByNineSite (secondarySectorToZetaTrit sector) (modePhaseToNonary state)

sixByNineBase54RoundTrip :
  (s : Zeta.SixByNineSite) → base54ToSixByNine (sixByNineToBase54 s) ≡ s
sixByNineBase54RoundTrip (Zeta.sixByNineSite six nine)
  rewrite zetaTritSectorRoundTrip six
        | nonaryModePhaseRoundTrip nine = refl

base54SixByNineRoundTrip :
  (s : Base.SecondaryCell54) → sixByNineToBase54 (base54ToSixByNine s) ≡ s
base54SixByNineRoundTrip (sector , state)
  rewrite sectorZetaTritRoundTrip sector
        | modePhaseNonaryRoundTrip state = refl

zeta54ToBase54 : Zeta.Zeta54Site → Base.SecondaryCell54
zeta54ToBase54 s = sixByNineToBase54 (Zeta.zeta54ToSixByNine s)

base54ToZeta54 : Base.SecondaryCell54 → Zeta.Zeta54Site
base54ToZeta54 s = Zeta.sixByNineToZeta54 (base54ToSixByNine s)

zeta54Base54RoundTrip :
  (s : Zeta.Zeta54Site) → base54ToZeta54 (zeta54ToBase54 s) ≡ s
zeta54Base54RoundTrip s
  rewrite sixByNineBase54RoundTrip (Zeta.zeta54ToSixByNine s)
        | Zeta.zeta54SixByNineRoundTrip s = refl

base54Zeta54RoundTrip :
  (s : Base.SecondaryCell54) → zeta54ToBase54 (base54ToZeta54 s) ≡ s
base54Zeta54RoundTrip s
  rewrite Zeta.sixByNineZeta54RoundTrip (base54ToSixByNine s)
        | base54SixByNineRoundTrip s = refl

------------------------------------------------------------------------
-- 4. The removed point is the existing Base369 distinguished invariant cell.
------------------------------------------------------------------------

zetaRemovedPointMapsToBaseInvariant :
  zeta54ToBase54 Albert.zetaRemovedScalar54 ≡ Base.distinguishedInvariant54
zetaRemovedPointMapsToBaseInvariant = refl

baseInvariantMapsToZetaRemovedPoint :
  base54ToZeta54 Base.distinguishedInvariant54 ≡ Albert.zetaRemovedScalar54
baseInvariantMapsToZetaRemovedPoint = refl

------------------------------------------------------------------------
-- 5. Attribution/QID/OEIS/Dewey snowball around the finite D4 label carrier.
------------------------------------------------------------------------

serreFiniteRepresentationSource : Attribution.AttributedSource
serreFiniteRepresentationSource = Attribution.mkDOISource
  "Jean-Pierre Serre"
  "Linear Representations of Finite Groups"
  "Graduate Texts in Mathematics 42, Springer"
  "1977"
  "10.1007/978-1-4684-9458-7"
  "https://doi.org/10.1007/978-1-4684-9458-7"
  Attribution.academicBookSource
  "finite-group representation/character reference for the D4 A1,A2,B1,B2,E label family; does not make the chosen six-way zeta chart a representation isomorphism"
  Attribution.publicAttribution

serreFiniteRepresentationAttribution =
  AttributionSnowball.canonicalSourceRoleSnowballReceipt serreFiniteRepresentationSource

record D4CarrierSnowballCoordinates : Set where
  constructor d4-carrier-snowball-coordinates
  field
    dihedralD4Qid : String
    genericDihedralGroupQid : String
    finiteRepresentationDOI : String
    localFiveIrrepLabels : String
    relevantOEIS : String
    deweyForExactSerreEdition : String
    d4LieAlgebraSequenceRejectedAsSameObject : Bool
    metadataCreatesCarrierBijection : Bool
    metadataCreatesMonsterAction : Bool
open D4CarrierSnowballCoordinates public

canonicalD4CarrierSnowballCoordinates : D4CarrierSnowballCoordinates
canonicalD4CarrierSnowballCoordinates = d4-carrier-snowball-coordinates
  "Q115556877"
  "Q558339"
  "10.1007/978-1-4684-9458-7"
  "A1,A2,B1,B2,E"
  "unresolved same-object OEIS for the five finite D4 irrep labels; do not substitute a Lie-D4 representation-dimension sequence"
  "unresolved authoritative catalogue Dewey for this exact Serre edition"
  true false false

------------------------------------------------------------------------
-- 6. WrongType boundaries.
------------------------------------------------------------------------

data SixWayChartCreatesRepresentationIso : Set where
data DihedralD4EqualsLieD4 : Set where
data ZetaPhaseEqualsD4IrrepLabel : Set where
data CarrierBijectionCreatesMonsterAction : Set where
data DistinguishedPointCreatesFixedAction : Set where

sixWayChartDoesNotCreateRepresentationIso : SixWayChartCreatesRepresentationIso → ⊥
sixWayChartDoesNotCreateRepresentationIso ()

dihedralD4DoesNotBecomeLieD4 : DihedralD4EqualsLieD4 → ⊥
dihedralD4DoesNotBecomeLieD4 ()

zetaPhaseDoesNotBecomeD4Label : ZetaPhaseEqualsD4IrrepLabel → ⊥
zetaPhaseDoesNotBecomeD4Label ()

carrierBijectionDoesNotCreateMonsterAction : CarrierBijectionCreatesMonsterAction → ⊥
carrierBijectionDoesNotCreateMonsterAction ()

distinguishedPointDoesNotCreateFixedAction : DistinguishedPointCreatesFixedAction → ⊥
distinguishedPointDoesNotCreateFixedAction ()

record ZetaFiveMode54Frontier : Set where
  constructor zeta-five-mode54-frontier
  field
    nineStateBijectionPaid : Bool
    sixStateBijectionPaid : Bool
    sixByNineToBase54BijectionPaid : Bool
    zeta54ToBase54BijectionPaid : Bool
    removedPointMatchesBaseDistinguishedInvariantCarrierPaid : Bool
    finiteD4SourceDOIPaid : Bool
    dihedralD4QidPaid : Bool
    exactD4OEISPaid : Bool
    authoritativeDeweyPaid : Bool
    residual53BijectionPaid : Bool
    inclusionCommutesAt53Paid : Bool
    actualMonsterActionPaid : Bool
    nextResidual : String
open ZetaFiveMode54Frontier public

currentZetaFiveMode54Frontier : ZetaFiveMode54Frontier
currentZetaFiveMode54Frontier = zeta-five-mode54-frontier
  true true true true true
  true true false false
  false false false
  "the full 54 carrier and its deleted point are now the same finite object across the zeta and Base369 skeletons. Next construct the induced 53-carrier bijection: complete A1/A2 sectors plus the eight non-identity distinguished states form the 26-point left residual, while complete B1/B2/E sectors form the right 27-point sheet. Prove that this map commutes with includeResidual53/includeZetaResidual53. Only then instantiate the existing Base369ExceptionalSkeletonBidi carrier fields; same-action recognition remains a separate unpaid theorem."
