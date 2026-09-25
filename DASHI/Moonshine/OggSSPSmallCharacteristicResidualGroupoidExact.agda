module DASHI.Moonshine.OggSSPSmallCharacteristicResidualGroupoidExact where

------------------------------------------------------------------------
-- SMALL-CHARACTERISTIC RESIDUAL GROUPOID TEST
--
-- ATTRIBUTION BOUNDARY
--
-- External arithmetic input is consumed through
--   OggSSPMonstrousExponent369GluingExact
-- which in turn consumes the attributed Duncan--Swisher owner
--   MonsterOrderExponentCorrectionExact.
--
-- Everything below -- the C2 actions, orbit presentations, and the comparison
-- with the Base369 residual carriers -- is a DASHI cross-module extension.
-- No external source is credited with the 369/groupoid interpretation.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)
open import Data.Empty using (⊥)
open import Data.Product using (_×_; _,_; proj₁; proj₂)

import DASHI.Interop.SourceAttributionShapePolicyExact as AttributionPolicy
import DASHI.Core.OrbitStabilizerResidualPresentationExact as Generic
import DASHI.Core.ResidualSymmetryCollisionFibreExact as Symmetry
import DASHI.Foundations.BalancedTernaryOrbitStabilizerResidualBridgeExact as C2Bridge
import DASHI.Biology.TriadicKernelLiftQuotientExact as Triadic
import DASHI.Moonshine.QuadraticApproximationPrimeCompressionBidiExact as Compression
import DASHI.Moonshine.OggSSPMonstrousExponent369GluingExact as Exponent369
import DASHI.Moonshine.OggSSPMonstrousExponentSourceAttributionExact as Source


residualGroupoidClaimOrigin : Source.ClaimOrigin
residualGroupoidClaimOrigin = Source.repositoryNewExtension

sameObjectRecognitionClaimOrigin : Source.ClaimOrigin
sameObjectRecognitionClaimOrigin = Source.openRecognitionConjecture

------------------------------------------------------------------------
-- 1. Attribution shape is internal proof lineage, not a fresh source claim.
------------------------------------------------------------------------

thisModuleAttributionShape :
  AttributionPolicy.RequiredAttributionShape
thisModuleAttributionShape =
  AttributionPolicy.requiredAttributionShape
    AttributionPolicy.internalDerivedTheorem

thisModuleUsesInternalProofLineage :
  thisModuleAttributionShape
  ≡ AttributionPolicy.proofLineageNoNewExternalCitation
thisModuleUsesInternalProofLineage = refl

------------------------------------------------------------------------
-- 2. p=3: the three constant ternary sections under global inversion.
--
-- We identify a constant triple with its common trit.  C2 acts by sign
-- inversion.  The zero constant is fixed; the two nonzero constants form one
-- two-point orbit.  Hence the orbit set has exactly two constructors.
------------------------------------------------------------------------

ConstantTernaryState : Set
ConstantTernaryState = Triadic.KernelTrit

actConstantC2 : C2Bridge.C2 → ConstantTernaryState → ConstantTernaryState
actConstantC2 C2Bridge.identity t = t
actConstantC2 C2Bridge.flip t = Triadic.negateTrit t

constantIdentityActs :
  (t : ConstantTernaryState) →
  actConstantC2 C2Bridge.identity t ≡ t
constantIdentityActs t = refl

constantCombineActs :
  (g h : C2Bridge.C2) (t : ConstantTernaryState) →
  actConstantC2 (C2Bridge.combineC2 g h) t
  ≡ actConstantC2 g (actConstantC2 h t)
constantCombineActs C2Bridge.identity h t = refl
constantCombineActs C2Bridge.flip C2Bridge.identity t = refl
constantCombineActs C2Bridge.flip C2Bridge.flip t =
  sym (Triadic.negateTritInvolutive t)

constantInverseLeftActs :
  (g : C2Bridge.C2) (t : ConstantTernaryState) →
  actConstantC2 (C2Bridge.inverseC2 g) (actConstantC2 g t) ≡ t
constantInverseLeftActs C2Bridge.identity t = refl
constantInverseLeftActs C2Bridge.flip t = Triadic.negateTritInvolutive t

constantInverseRightActs :
  (g : C2Bridge.C2) (t : ConstantTernaryState) →
  actConstantC2 g (actConstantC2 (C2Bridge.inverseC2 g) t) ≡ t
constantInverseRightActs C2Bridge.identity t = refl
constantInverseRightActs C2Bridge.flip t = Triadic.negateTritInvolutive t

constantC2Action :
  Symmetry.InvertibleSymmetryAction ConstantTernaryState C2Bridge.C2
constantC2Action =
  Symmetry.invertibleSymmetryAction
    C2Bridge.identity
    C2Bridge.combineC2
    C2Bridge.inverseC2
    actConstantC2
    constantIdentityActs
    constantCombineActs
    constantInverseLeftActs
    constantInverseRightActs

data ConstantTernaryOrbit : Set where
  zeroConstantOrbit : ConstantTernaryOrbit
  nonzeroConstantOrbit : ConstantTernaryOrbit

constantOrbitOf : ConstantTernaryState → ConstantTernaryOrbit
constantOrbitOf Triadic.zeroTrit = zeroConstantOrbit
constantOrbitOf Triadic.negativeTrit = nonzeroConstantOrbit
constantOrbitOf Triadic.positiveTrit = nonzeroConstantOrbit

constantRepresentative : ConstantTernaryOrbit → ConstantTernaryState
constantRepresentative zeroConstantOrbit = Triadic.zeroTrit
constantRepresentative nonzeroConstantOrbit = Triadic.positiveTrit

constantOrbitInvariant :
  (g : C2Bridge.C2) (t : ConstantTernaryState) →
  constantOrbitOf (actConstantC2 g t) ≡ constantOrbitOf t
constantOrbitInvariant C2Bridge.identity t = refl
constantOrbitInvariant C2Bridge.flip Triadic.zeroTrit = refl
constantOrbitInvariant C2Bridge.flip Triadic.negativeTrit = refl
constantOrbitInvariant C2Bridge.flip Triadic.positiveTrit = refl

constantRepresentativeInOrbit :
  (o : ConstantTernaryOrbit) →
  constantOrbitOf (constantRepresentative o) ≡ o
constantRepresentativeInOrbit zeroConstantOrbit = refl
constantRepresentativeInOrbit nonzeroConstantOrbit = refl

constantTransporter : ConstantTernaryState → C2Bridge.C2
constantTransporter Triadic.zeroTrit = C2Bridge.identity
constantTransporter Triadic.positiveTrit = C2Bridge.identity
constantTransporter Triadic.negativeTrit = C2Bridge.flip

constantTransporterHits :
  (t : ConstantTernaryState) →
  actConstantC2
    (constantTransporter t)
    (constantRepresentative (constantOrbitOf t))
  ≡ t
constantTransporterHits Triadic.zeroTrit = refl
constantTransporterHits Triadic.positiveTrit = refl
constantTransporterHits Triadic.negativeTrit = refl

constantTernaryOrbitPresentation :
  Generic.OrbitPresentation constantC2Action
constantTernaryOrbitPresentation =
  Generic.orbitPresentation
    ConstantTernaryOrbit
    constantOrbitOf
    constantRepresentative
    constantOrbitInvariant
    constantRepresentativeInOrbit
    constantTransporter
    constantTransporterHits

constantTernaryPi0Count : Nat
constantTernaryPi0Count = 2

p3ResidualEqualsConstantTernaryPi0 :
  Exponent369.p3ExceptionalResidual ≡ constantTernaryPi0Count
p3ResidualEqualsConstantTernaryPi0 = refl

------------------------------------------------------------------------
-- 3. Stabilizer split at p=3.
------------------------------------------------------------------------

constantStabilizerSize : ConstantTernaryOrbit → Nat
constantStabilizerSize zeroConstantOrbit = 2
constantStabilizerSize nonzeroConstantOrbit = 1

zeroConstantHasEnhancedC2Stabilizer :
  constantStabilizerSize zeroConstantOrbit ≡ 2
zeroConstantHasEnhancedC2Stabilizer = refl

nonzeroConstantHasTrivialStabilizer :
  constantStabilizerSize nonzeroConstantOrbit ≡ 1
nonzeroConstantHasTrivialStabilizer = refl

------------------------------------------------------------------------
-- 4. p=2 naive candidate: strict binary sheet x five NineOrbit labels.
--
-- The obvious C2 action flips only the binary sheet.  It leaves the already
-- quotiented five-orbit label fixed.  Therefore this ten-object carrier has
-- FIVE connected C2 orbits, not ten.
------------------------------------------------------------------------

P2ResidualObject : Set
P2ResidualObject = Compression.StrictSignedSide × Triadic.NineOrbit

flipStrictSide :
  Compression.StrictSignedSide → Compression.StrictSignedSide
flipStrictSide Compression.lowerSide = Compression.upperSide
flipStrictSide Compression.upperSide = Compression.lowerSide

actP2ResidualC2 : C2Bridge.C2 → P2ResidualObject → P2ResidualObject
actP2ResidualC2 C2Bridge.identity state = state
actP2ResidualC2 C2Bridge.flip (side , orbit) =
  flipStrictSide side , orbit

p2IdentityActs :
  (state : P2ResidualObject) →
  actP2ResidualC2 C2Bridge.identity state ≡ state
p2IdentityActs state = refl

p2CombineActs :
  (g h : C2Bridge.C2) (state : P2ResidualObject) →
  actP2ResidualC2 (C2Bridge.combineC2 g h) state
  ≡ actP2ResidualC2 g (actP2ResidualC2 h state)
p2CombineActs C2Bridge.identity h state = refl
p2CombineActs C2Bridge.flip C2Bridge.identity state = refl
p2CombineActs C2Bridge.flip C2Bridge.flip (Compression.lowerSide , orbit) = refl
p2CombineActs C2Bridge.flip C2Bridge.flip (Compression.upperSide , orbit) = refl

p2InverseLeftActs :
  (g : C2Bridge.C2) (state : P2ResidualObject) →
  actP2ResidualC2
    (C2Bridge.inverseC2 g)
    (actP2ResidualC2 g state)
  ≡ state
p2InverseLeftActs C2Bridge.identity state = refl
p2InverseLeftActs C2Bridge.flip (Compression.lowerSide , orbit) = refl
p2InverseLeftActs C2Bridge.flip (Compression.upperSide , orbit) = refl

p2InverseRightActs :
  (g : C2Bridge.C2) (state : P2ResidualObject) →
  actP2ResidualC2 g
    (actP2ResidualC2 (C2Bridge.inverseC2 g) state)
  ≡ state
p2InverseRightActs C2Bridge.identity state = refl
p2InverseRightActs C2Bridge.flip (Compression.lowerSide , orbit) = refl
p2InverseRightActs C2Bridge.flip (Compression.upperSide , orbit) = refl

p2ResidualC2Action :
  Symmetry.InvertibleSymmetryAction P2ResidualObject C2Bridge.C2
p2ResidualC2Action =
  Symmetry.invertibleSymmetryAction
    C2Bridge.identity
    C2Bridge.combineC2
    C2Bridge.inverseC2
    actP2ResidualC2
    p2IdentityActs
    p2CombineActs
    p2InverseLeftActs
    p2InverseRightActs

p2OrbitOf : P2ResidualObject → Triadic.NineOrbit
p2OrbitOf = proj₂

p2Representative : Triadic.NineOrbit → P2ResidualObject
p2Representative orbit = Compression.lowerSide , orbit

p2OrbitInvariant :
  (g : C2Bridge.C2) (state : P2ResidualObject) →
  p2OrbitOf (actP2ResidualC2 g state) ≡ p2OrbitOf state
p2OrbitInvariant C2Bridge.identity state = refl
p2OrbitInvariant C2Bridge.flip (side , orbit) = refl

p2RepresentativeInOrbit :
  (orbit : Triadic.NineOrbit) →
  p2OrbitOf (p2Representative orbit) ≡ orbit
p2RepresentativeInOrbit orbit = refl

p2Transporter : P2ResidualObject → C2Bridge.C2
p2Transporter (Compression.lowerSide , orbit) = C2Bridge.identity
p2Transporter (Compression.upperSide , orbit) = C2Bridge.flip

p2TransporterHits :
  (state : P2ResidualObject) →
  actP2ResidualC2
    (p2Transporter state)
    (p2Representative (p2OrbitOf state))
  ≡ state
p2TransporterHits (Compression.lowerSide , orbit) = refl
p2TransporterHits (Compression.upperSide , orbit) = refl

p2ResidualOrbitPresentation :
  Generic.OrbitPresentation p2ResidualC2Action
p2ResidualOrbitPresentation =
  Generic.orbitPresentation
    Triadic.NineOrbit
    p2OrbitOf
    p2Representative
    p2OrbitInvariant
    p2RepresentativeInOrbit
    p2Transporter
    p2TransporterHits

p2ResidualObjectCount : Nat
p2ResidualObjectCount = 10

p2ResidualPi0Count : Nat
p2ResidualPi0Count = 5

p2ResidualEqualsObjectCount :
  Exponent369.p2ExceptionalResidual ≡ p2ResidualObjectCount
p2ResidualEqualsObjectCount = refl

data NaiveP2Pi0EqualsMonsterResidual : Set where

naiveP2Pi0DoesNotEqualMonsterResidual :
  p2ResidualPi0Count ≡ Exponent369.p2ExceptionalResidual → ⊥
naiveP2Pi0DoesNotEqualMonsterResidual ()

------------------------------------------------------------------------
-- 5. Consequence / frontier.
------------------------------------------------------------------------

record SmallCharacteristicResidualGroupoidBoundary : Set where
  constructor small-characteristic-residual-groupoid-boundary
  field
    p3ConstantTernaryC2ActionConstructed : Bool
    p3ResidualIsLiteralPi0Count : Bool
    p3ZeroOrbitHasEnhancedStabilizer : Bool
    p2TenObjectCarrierConstructed : Bool
    p2TenObjectsMatchArithmeticResidual : Bool
    p2NaiveBinaryFlipPi0Count : Nat
    p2NaiveBinaryFlipPi0EqualsResidual : Bool
    p2NeedsRicherGluingRecognition : Bool
    externalArithmeticAttributedUpstream : Bool
    groupoidInterpretationIsDASHIExtension : Bool

canonicalSmallCharacteristicResidualGroupoidBoundary :
  SmallCharacteristicResidualGroupoidBoundary
canonicalSmallCharacteristicResidualGroupoidBoundary =
  small-characteristic-residual-groupoid-boundary
    true true true
    true true
    5 false true
    true true
