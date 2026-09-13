module DASHI.Wikimedia.IbrahimZeta54AlbertPair53SnowballAttributionBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Attribution
import DASHI.Core.SnowballAttributionProvenanceInvariantExact as AttributionSnowball
import DASHI.Foundations.Base369Ternary27HypervoxelFabricGeometryExact as Geometry
import DASHI.Foundations.ExceptionalAlbertFreudenthalResidualExact as Exceptional
import DASHI.Moonshine.Base369ZetaHeisenbergFiftyFourCarrierExact as Zeta
import DASHI.Wikimedia.IbrahimTernary27OriginTraceless26AlbertShapeBidiExact as Shape

------------------------------------------------------------------------
-- ZETA54 -> ALBERT PAIR54 -> REDUCED53 ON THE SAME FINITE CARRIER
--
-- Existing repo-native inputs:
--
--   Zeta54Site = {zeta,zeta^-1} x T3^3
--   T3^3       <-> ScalarLine + NonOrigin26
--   AlbertPair54 = Albert27(left) + Albert27(right)
--   ReducedAlbertPair53 = J0(left) + Albert27(right).
--
-- Choose zeta as the left sheet and zeta^-1 as the right sheet.  This yields
-- an exact two-sided carrier map Zeta54Site <-> AlbertPair54.  Deleting exactly
-- the zeta-sheet origin yields the corresponding 53-carrier and a commuting
-- inclusion square with ReducedAlbertPair53.
--
-- This is stronger than 54=27+27 and 53=26+27 arithmetic, but weaker than an
-- Albert/Jordan recognition: no Jordan product, norm, F4/E6 action, Monster
-- action, or action intertwiner is constructed here.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- 1. Instantiate the two Albert summands with the already proved cube shape.
------------------------------------------------------------------------

cubeAlbertPair : Exceptional.AlbertPairCarrier
Exceptional.AlbertPairCarrier.leftAlbert cubeAlbertPair = Shape.cubeAlbertCarrier
Exceptional.AlbertPairCarrier.rightAlbert cubeAlbertPair = Shape.cubeAlbertCarrier

CubeAlbertPair54 : Set
CubeAlbertPair54 = Exceptional.AlbertPair54 cubeAlbertPair

CubeReducedAlbert53 : Set
CubeReducedAlbert53 = Exceptional.ReducedAlbertPair53 cubeAlbertPair

------------------------------------------------------------------------
-- 2. Exact 54-carrier bijection: zeta sheet = left, inverse-zeta = right.
------------------------------------------------------------------------

zeta54ToAlbertPair54 : Zeta.Zeta54Site → CubeAlbertPair54
zeta54ToAlbertPair54 (Zeta.zeta54Site Zeta.zetaSheet p) =
  inj₁ (Shape.toAlbertShape p)
zeta54ToAlbertPair54 (Zeta.zeta54Site Zeta.inverseZetaSheet p) =
  inj₂ (Shape.toAlbertShape p)

albertPair54ToZeta54 : CubeAlbertPair54 → Zeta.Zeta54Site
albertPair54ToZeta54 (inj₁ a) =
  Zeta.zeta54Site Zeta.zetaSheet (Shape.fromAlbertShape a)
albertPair54ToZeta54 (inj₂ a) =
  Zeta.zeta54Site Zeta.inverseZetaSheet (Shape.fromAlbertShape a)

zeta54Albert54RoundTrip :
  (s : Zeta.Zeta54Site) →
  albertPair54ToZeta54 (zeta54ToAlbertPair54 s) ≡ s
zeta54Albert54RoundTrip (Zeta.zeta54Site Zeta.zetaSheet p)
  rewrite Shape.fromAfterTo p = refl
zeta54Albert54RoundTrip (Zeta.zeta54Site Zeta.inverseZetaSheet p)
  rewrite Shape.fromAfterTo p = refl

albert54Zeta54RoundTrip :
  (a : CubeAlbertPair54) →
  zeta54ToAlbertPair54 (albertPair54ToZeta54 a) ≡ a
albert54Zeta54RoundTrip (inj₁ a)
  rewrite Shape.toAfterFrom a = refl
albert54Zeta54RoundTrip (inj₂ a)
  rewrite Shape.toAfterFrom a = refl

------------------------------------------------------------------------
-- 3. Delete exactly the left/zeta scalar-origin point.
------------------------------------------------------------------------

ZetaResidual53 : Set
ZetaResidual53 = Shape.NonOrigin26 ⊎ Geometry.Ternary27Point

zetaRemovedScalar54 : Zeta.Zeta54Site
zetaRemovedScalar54 = Zeta.zeta54Site Zeta.zetaSheet Geometry.origin

includeZetaResidual53 : ZetaResidual53 → Zeta.Zeta54Site
includeZetaResidual53 (inj₁ q) =
  Zeta.zeta54Site Zeta.zetaSheet (Shape.nonOriginToPoint q)
includeZetaResidual53 (inj₂ p) =
  Zeta.zeta54Site Zeta.inverseZetaSheet p

zetaResidual53ToAlbert53 : ZetaResidual53 → CubeReducedAlbert53
zetaResidual53ToAlbert53 (inj₁ q) = inj₁ q
zetaResidual53ToAlbert53 (inj₂ p) = inj₂ (Shape.toAlbertShape p)

albert53ToZetaResidual53 : CubeReducedAlbert53 → ZetaResidual53
albert53ToZetaResidual53 (inj₁ q) = inj₁ q
albert53ToZetaResidual53 (inj₂ a) = inj₂ (Shape.fromAlbertShape a)

zeta53Albert53RoundTrip :
  (s : ZetaResidual53) →
  albert53ToZetaResidual53 (zetaResidual53ToAlbert53 s) ≡ s
zeta53Albert53RoundTrip (inj₁ q) = refl
zeta53Albert53RoundTrip (inj₂ p)
  rewrite Shape.fromAfterTo p = refl

albert53Zeta53RoundTrip :
  (a : CubeReducedAlbert53) →
  zetaResidual53ToAlbert53 (albert53ToZetaResidual53 a) ≡ a
albert53Zeta53RoundTrip (inj₁ q) = refl
albert53Zeta53RoundTrip (inj₂ a)
  rewrite Shape.toAfterFrom a = refl

------------------------------------------------------------------------
-- 4. The residual inclusion commutes with the Albert-pair inclusion.
------------------------------------------------------------------------

includeReducedAlbert53 : CubeReducedAlbert53 → CubeAlbertPair54
includeReducedAlbert53 (inj₁ q) = inj₁ (inj₂ q)
includeReducedAlbert53 (inj₂ a) = inj₂ a

residualInclusionCommutes :
  (s : ZetaResidual53) →
  zeta54ToAlbertPair54 (includeZetaResidual53 s)
  ≡ includeReducedAlbert53 (zetaResidual53ToAlbert53 s)
residualInclusionCommutes (inj₁ q) = refl
residualInclusionCommutes (inj₂ p) = refl

removedZetaOriginMapsToLeftAlbertScalar :
  zeta54ToAlbertPair54 zetaRemovedScalar54
  ≡ inj₁ (inj₁ Exceptional.scalarLine)
removedZetaOriginMapsToLeftAlbertScalar = Shape.originMapsToScalar

------------------------------------------------------------------------
-- 5. Snowball attribution: source identity != theorem payment.
------------------------------------------------------------------------

albertJacobson1957 : Attribution.AttributedSource
albertJacobson1957 = Attribution.mkDOISource
  "A. A. Albert; Nathan Jacobson"
  "On Reduced Exceptional Simple Jordan Algebras"
  "Annals of Mathematics 66(3), 400-417"
  "1957"
  "10.2307/1969898"
  "https://doi.org/10.2307/1969898"
  Attribution.academicArticleSource
  "primary historical source for reduced exceptional simple Jordan algebras; does not identify the DASHI ternary/zeta carrier with an Albert algebra"
  Attribution.publicAttribution

jacobsonF4Source : Attribution.AttributedSource
jacobsonF4Source = Attribution.mkDOISource
  "Nathan Jacobson"
  "Some groups of transformations defined by Jordan algebras. II. Groups of type F4"
  "Journal fuer die reine und angewandte Mathematik 204, 74-98"
  "1960"
  "10.1515/crll.1960.204.74"
  "https://doi.org/10.1515/crll.1960.204.74"
  Attribution.academicArticleSource
  "primary historical source for the F4 transformation-group/Jordan-algebra relation; not an action receipt for the DASHI carrier"
  Attribution.publicAttribution

springerVeldkampReference : Attribution.AttributedSource
springerVeldkampReference = Attribution.mkDOISource
  "Tonny A. Springer; Ferdinand D. Veldkamp"
  "Octonions, Jordan Algebras and Exceptional Groups"
  "Springer Monographs in Mathematics"
  "2000"
  "10.1007/978-3-662-12622-6"
  "https://doi.org/10.1007/978-3-662-12622-6"
  Attribution.academicBookSource
  "reference source covering Albert algebras and exceptional groups; citation does not construct the local product, norm, or intertwiner"
  Attribution.publicAttribution

albertJacobsonAttribution =
  AttributionSnowball.canonicalSourceRoleSnowballReceipt albertJacobson1957
jacobsonF4Attribution =
  AttributionSnowball.canonicalSourceRoleSnowballReceipt jacobsonF4Source
springerVeldkampAttribution =
  AttributionSnowball.canonicalSourceRoleSnowballReceipt springerVeldkampReference

record ExceptionalCarrierExternalCoordinates : Set where
  constructor exceptional-carrier-external-coordinates
  field
    jordanAlgebraQid : String
    f4Qid : String
    e6Qid : String
    albertAlgebraQid : String
    f4IrrepDimensionOEIS : String
    e6IrrepDimensionOEIS : String
    primaryAlbertJordanDOI : String
    primaryF4DOI : String
    referenceAlbertExceptionalDOI : String
    deweyJordanAlbert : String
    deweyExceptionalLie : String
    unresolvedMetadataExplicit : Bool
    externalCoordinatesCreateAction : Bool
open ExceptionalCarrierExternalCoordinates public

canonicalExceptionalCarrierExternalCoordinates : ExceptionalCarrierExternalCoordinates
canonicalExceptionalCarrierExternalCoordinates = exceptional-carrier-external-coordinates
  "Q649977"
  "Q869077"
  "Q1054513"
  "unresolved exact Albert-algebra QID; do not substitute the Jordan-algebra QID"
  "A121738"
  "A121737"
  "10.2307/1969898"
  "10.1515/crll.1960.204.74"
  "10.1007/978-3-662-12622-6"
  "unresolved authoritative catalogue Dewey for Albert/Jordan source"
  "unresolved source-specific Dewey; do not infer from a generic Lie-theory book"
  true
  false

------------------------------------------------------------------------
-- 6. WrongType / promotion firewalls.
------------------------------------------------------------------------

data CarrierBijectionCreatesJordanProduct : Set where
data RemovedOriginCreatesJordanUnit : Set where
data ZetaSheetsCreateE6MinusculePair : Set where
data CarrierRecognitionCreatesF4Action : Set where
data CarrierRecognitionCreatesMonsterAction : Set where
data SourceMetadataCreatesIntertwiner : Set where

carrierBijectionDoesNotCreateJordanProduct : CarrierBijectionCreatesJordanProduct → ⊥
carrierBijectionDoesNotCreateJordanProduct ()

removedOriginDoesNotCreateJordanUnit : RemovedOriginCreatesJordanUnit → ⊥
removedOriginDoesNotCreateJordanUnit ()

zetaSheetsDoNotCreateE6Pair : ZetaSheetsCreateE6MinusculePair → ⊥
zetaSheetsDoNotCreateE6Pair ()

carrierDoesNotCreateF4Action : CarrierRecognitionCreatesF4Action → ⊥
carrierDoesNotCreateF4Action ()

carrierDoesNotCreateMonsterAction : CarrierRecognitionCreatesMonsterAction → ⊥
carrierDoesNotCreateMonsterAction ()

metadataDoesNotCreateIntertwiner : SourceMetadataCreatesIntertwiner → ⊥
metadataDoesNotCreateIntertwiner ()

record ZetaAlbertPairFrontier : Set where
  constructor zeta-albert-pair-frontier
  field
    zeta54ToAlbertPair54BijectionPaid : Bool
    zeta53ToReducedAlbert53BijectionPaid : Bool
    residualInclusionCommutesPaid : Bool
    removedZetaOriginMatchesRemovedLeftScalarPaid : Bool
    primaryAlbertJordanSourcePaid : Bool
    primaryF4SourcePaid : Bool
    referenceExceptionalSourcePaid : Bool
    qidCoordinatesPaid : Bool
    oeisCoordinatesPaid : Bool
    authoritativeDeweyPaid : Bool
    jordanProductPaid : Bool
    f4ActionPaid : Bool
    e6ActionPaid : Bool
    monsterSameActionPaid : Bool
    nextResidual : String
open ZetaAlbertPairFrontier public

currentZetaAlbertPairFrontier : ZetaAlbertPairFrontier
currentZetaAlbertPairFrontier = zeta-albert-pair-frontier
  true true true true
  true true true true true false
  false false false false
  "carrier/deletion debt is paid on the literal zeta x ternary object. Next compare this exact Zeta54Site/Residual53 commuting square with Base369MonsterFiftyFourFiveModeResidualActionBidiExact.SecondaryCell54/ResidualCell53. Search first for an existing bijection between the zeta six-by-nine chart and the five-mode-plus-distinguished six-by-nine skeleton; only after that same carrier is paid should the existing 54->53 same-action recognition be instantiated. Separately snowball the missing Albert-specific QID and authoritative Dewey without allowing metadata to promote the action."
