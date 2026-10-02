module DASHI.Physics.CondensedMatter.GaoFe5GeTe2Sqrt3R30SameObjectWeldExact where

------------------------------------------------------------------------
-- Fe5GeTe2 SOURCE / GEOMETRY WELD
--
-- This module connects the source-paid label
--
--   sqrt(3) x sqrt(3) R30-degree charge order
--
-- to the repository's exact generic hexagonal supercell mathematics.
--
-- The weld is intentionally typed as a geometry interpretation contract:
-- the source pays the observed symmetry label and band folding, while the
-- repository pays the exact matrix, metric, reciprocal transform, and C3
-- quotient mathematics for that label.
--
-- It does NOT assert that the finite C3 carrier is the full ARPES dataset or
-- that the generic hexagonal matrix derives the material's microscopic
-- Hamiltonian.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Physics.CondensedMatter.GaoFe5GeTe2FlatBandChargeOrderSourceReplayExact as Source
import DASHI.Physics.CondensedMatter.HexagonalSqrt3R30ReciprocalFoldingExact as Hex
import DASHI.Physics.CondensedMatter.ThreeFoldBandFoldingExact as Fold
import DASHI.Physics.Common.FiniteThreeCycleTorusExact as Torus

------------------------------------------------------------------------
-- 1. Source object remains the authority for the experimental observation.
------------------------------------------------------------------------

sourceReplay : Source.Fe5GeTe2SourceReplay
sourceReplay = Source.canonicalFe5GeTe2SourceReplay

sourceChargeOrderLabel : String
sourceChargeOrderLabel = Source.chargeOrderSymmetry sourceReplay

sourceBandFoldingWindowMeV : Nat
sourceBandFoldingWindowMeV =
  Source.bandFoldingWindowBelowFermiMeV sourceReplay

sourceBandFoldingWindowIsThirty :
  sourceBandFoldingWindowMeV ≡ 30
sourceBandFoldingWindowIsThirty = refl

------------------------------------------------------------------------
-- 2. Exact generic geometry packet for the reported symmetry class.
------------------------------------------------------------------------

record Sqrt3R30GeometryPacket : Set where
  constructor sqrt3-r30-geometry-packet
  field
    realSpaceDeterminantThree : Hex.det2 Hex.superA1 Hex.superA2 ≡ Hex.threeℤ
    sqrt3MetricScale :
      Hex.hexNormSq Hex.superA1
      ≡ Hex.threeℤ Hex.*ℤ Hex.hexNormSq Hex.primitiveA1
    r30MetricSquare :
      (+ 4) Hex.*ℤ
        (Hex.hexDot Hex.primitiveA1 Hex.superA1
         Hex.*ℤ
         Hex.hexDot Hex.primitiveA1 Hex.superA1)
      ≡
      Hex.threeℤ Hex.*ℤ
        (Hex.hexNormSq Hex.primitiveA1
         Hex.*ℤ
         Hex.hexNormSq Hex.superA1)
    reciprocalMTransposeNTimes :
      Hex.dotCoordinates Hex.superA1 Hex.reciprocalNumeratorB1 ≡ Hex.threeℤ
    reciprocalCrossTermZero :
      Hex.dotCoordinates Hex.superA1 Hex.reciprocalNumeratorB2 ≡ Hex.zeroℤ

canonicalSqrt3R30GeometryPacket : Sqrt3R30GeometryPacket
canonicalSqrt3R30GeometryPacket =
  sqrt3-r30-geometry-packet
    Hex.supercellDeterminantIsThree
    Hex.supercellSqrt3ScaleCertificate
    Hex.r30MetricSquareCertificate
    Hex.mtN11IsThree
    Hex.mtN12IsZero

------------------------------------------------------------------------
-- 3. Three-class folding is now sourced from the literal supercell quotient,
--    not merely from an arbitrary Fin 3 collapse.
------------------------------------------------------------------------

data LiteralFoldClass : Set where
  classMinus classZero classPlus : LiteralFoldClass

literalFoldClass : Torus.Torus3x3 → LiteralFoldClass
literalFoldClass point with Hex.foldClass point
... | Torus.residueMinus = classMinus
... | Torus.residueZero = classZero
... | Torus.residuePlus = classPlus

literalFoldClassInvariantUnderA1 :
  (point : Torus.Torus3x3) →
  literalFoldClass (Hex.translateSuperA1 point)
  ≡ literalFoldClass point
literalFoldClassInvariantUnderA1 point
  rewrite Hex.foldClassInvariantUnderSuperA1 point = refl

literalFoldClassInvariantUnderA2 :
  (point : Torus.Torus3x3) →
  literalFoldClass (Hex.translateSuperA2 point)
  ≡ literalFoldClass point
literalFoldClassInvariantUnderA2 point
  rewrite Hex.foldClassInvariantUnderSuperA2 point = refl

minusRepresentativeHasMinusClass :
  literalFoldClass Hex.foldRepresentativeMinus ≡ classMinus
minusRepresentativeHasMinusClass = refl

zeroRepresentativeHasZeroClass :
  literalFoldClass Hex.foldRepresentativeZero ≡ classZero
zeroRepresentativeHasZeroClass = refl

plusRepresentativeHasPlusClass :
  literalFoldClass Hex.foldRepresentativePlus ≡ classPlus
plusRepresentativeHasPlusClass = refl

------------------------------------------------------------------------
-- 4. Source / theorem authority split.
------------------------------------------------------------------------

data ClaimOwner : Set where
  experimentalARPESOwner : ClaimOwner
  exactSupercellAlgebraOwner : ClaimOwner
  interpretationOwner : ClaimOwner

flatBandObservedOwner : ClaimOwner
flatBandObservedOwner = experimentalARPESOwner

chargeOrderObservedOwner : ClaimOwner
chargeOrderObservedOwner = experimentalARPESOwner

sqrt3R30MatrixIdentityOwner : ClaimOwner
sqrt3R30MatrixIdentityOwner = exactSupercellAlgebraOwner

kondoLikePhenomenologyOwner : ClaimOwner
kondoLikePhenomenologyOwner = interpretationOwner

record Fe5GeTe2Sqrt3R30WeldBoundary : Set where
  constructor fe5gete2-sqrt3-r30-weld-boundary
  field
    sourcePaysChargeOrderLabel : Bool
    sourcePaysBandFoldingObservation : Bool
    sourcePaysFlatBandNestingObservation : Bool
    repositoryPaysExactHexagonalMatrix : Bool
    repositoryPaysExactReciprocalTransform : Bool
    repositoryPaysThreeClassFiniteFolding : Bool
    genericGeometryIsClaimedToBeRawARPESData : Bool
    determinantThreeAloneIsClaimedToProveMaterialStructure : Bool
    exactGeometryIsClaimedToDeriveMicroscopicHamiltonian : Bool
    sourceInterpretationIsClaimedToBeRepositoryDerivation : Bool

canonicalFe5GeTe2Sqrt3R30WeldBoundary :
  Fe5GeTe2Sqrt3R30WeldBoundary
canonicalFe5GeTe2Sqrt3R30WeldBoundary =
  fe5gete2-sqrt3-r30-weld-boundary
    true true true
    true true true
    false false false false

------------------------------------------------------------------------
-- 5. Compatibility with the earlier generic three-fold surface.
------------------------------------------------------------------------

record GenericToLiteralFoldingUpgrade : Set where
  constructor generic-to-literal-folding-upgrade
  field
    earlierGenericThreeFoldSurfaceStillValid : Bool
    literalHexagonalProducerNowAvailable : Bool
    genericSurfaceWasNotRetroactivelyPhysicalProof : Bool

canonicalGenericToLiteralFoldingUpgrade : GenericToLiteralFoldingUpgrade
canonicalGenericToLiteralFoldingUpgrade =
  generic-to-literal-folding-upgrade true true true

earlierGenericThreeFoldPresentation :
  Fold.ThreeFoldPresentation
    (Data.Fin.Base.Fin 3)
    Fold.OneFoldedPoint
earlierGenericThreeFoldPresentation =
  Fold.canonicalThreeFoldPresentation
