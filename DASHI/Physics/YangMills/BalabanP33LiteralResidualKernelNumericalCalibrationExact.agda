module DASHI.Physics.YangMills.BalabanP33LiteralResidualKernelNumericalCalibrationExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Tadeusz Bałaban,
-- "Propagators for Lattice Gauge Theories in a Background Field",
-- Communications in Mathematical Physics 99 (1985), 389--434.
-- DOI: 10.1007/BF01240355.
--
-- Tosio Kato,
-- "Perturbation Theory for Linear Operators",
-- Springer Classics in Mathematics, 1995 reprint.
-- DOI: 10.1007/978-3-642-66282-9.
--
-- DASHI CONTRIBUTION
--
-- Construct the literal finite side-four residual matrix
--
--   R = I - H G*,
--
-- on the repository's actual three-component SU(2) positive-bond coordinate
-- carrier.  The carrier has exactly
--
--   3 * 4 * 4^4 = 3072
--
-- coordinates.  A deliberately conservative full-row support estimate has
-- block radius r0=8, because every coordinate of the side-four periodic torus
-- is at cyclic distance at most two and there are four spacetime coordinates.
--
-- Choosing the geometric weight base s=2 gives the exact inflation
--
--   s^r0 = 2^8 = 256.
--
-- Therefore the literal entry threshold
--
--   epsilon_* = 1 / 1572864
--
-- satisfies
--
--   N epsilon_* s^r0 = 1/2.
--
-- Under the model decay epsilon(M) <= 2^-M, the explicit collar M=21 gives
-- epsilon(21)=1/2097152 and the stronger row coefficient 3/8.  This does not
-- assert that the physical local inverse already has that decay.  It replaces
-- the formerly unspecified numerical target by one exact target: prove the
-- physical entry estimate at collar 21, or improve N/r0 and recalibrate.
--
-- In exponential notation s=e^mu, the selected weight is mu=log 2.  The
-- logarithm identity is kept as the analytic interpretation of the entirely
-- rational weight calculation; no unimplemented real exponential is used in
-- the finite proof.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Data.Integer.Base using (+_)
open import Data.List.Base using (length)
open import Data.Nat.Base using (_≤_; z≤n; s≤s)
import Data.Nat.Properties as NatP
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_; _≤_; _/_; NonNegative)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong; subst; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier
import DASHI.Physics.YangMills.BalabanFourDimensionalHaloOverlapExact as Count
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreCarrier as Block
import DASHI.Physics.YangMills.BalabanP33LiteralBondCellIncidenceExact as Cell
import DASHI.Physics.YangMills.BalabanP33PhysicalSU2FiniteCoordinatesExact as Physical
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact as Sums

------------------------------------------------------------------------
-- Literal matrix residual R = I - H G*.
------------------------------------------------------------------------

lieCoordinateDecidableEquality :
  DecidableEquality Physical.LieCoordinate3
lieCoordinateDecidableEquality Physical.coordinateX Physical.coordinateX = yes refl
lieCoordinateDecidableEquality Physical.coordinateX Physical.coordinateY = no (λ ())
lieCoordinateDecidableEquality Physical.coordinateX Physical.coordinateZ = no (λ ())
lieCoordinateDecidableEquality Physical.coordinateY Physical.coordinateX = no (λ ())
lieCoordinateDecidableEquality Physical.coordinateY Physical.coordinateY = yes refl
lieCoordinateDecidableEquality Physical.coordinateY Physical.coordinateZ = no (λ ())
lieCoordinateDecidableEquality Physical.coordinateZ Physical.coordinateX = no (λ ())
lieCoordinateDecidableEquality Physical.coordinateZ Physical.coordinateY = no (λ ())
lieCoordinateDecidableEquality Physical.coordinateZ Physical.coordinateZ = yes refl

bondCellDecidableEquality : DecidableEquality Cell.BondCell4
bondCellDecidableEquality =
  productDecidableEquality cyclicIndexDecidableEquality
    (periodicTorus4DecidableEquality Block.side4)

physicalCoordinateDecidableEquality :
  DecidableEquality Physical.PhysicalSU2Coordinate4
physicalCoordinateDecidableEquality =
  productDecidableEquality lieCoordinateDecidableEquality
    bondCellDecidableEquality

identityEntry :
  Physical.PhysicalSU2Coordinate4 →
  Physical.PhysicalSU2Coordinate4 → ℚ
identityEntry left right with physicalCoordinateDecidableEquality left right
... | yes _ = 1ℚ
... | no _ = 0ℚ

composeMatrix :
  Physical.PhysicalSU2Matrix4 →
  Physical.PhysicalSU2Matrix4 →
  Physical.PhysicalSU2Matrix4
composeMatrix left right row column =
  Sums.sumRational Physical.physicalSU2Coordinates4
    (λ middle → left row middle * right middle column)

literalResidualKernel :
  Physical.PhysicalSU2Matrix4 →
  Physical.PhysicalSU2Matrix4 →
  Physical.PhysicalSU2Matrix4
literalResidualKernel hessian localParametrix row column =
  identityEntry row column
  - composeMatrix hessian localParametrix row column

literalResidualEntryExact :
  ∀ hessian localParametrix row column →
  literalResidualKernel hessian localParametrix row column
  ≡ identityEntry row column
    - Sums.sumRational Physical.physicalSU2Coordinates4
        (λ middle → hessian row middle * localParametrix middle column)
literalResidualEntryExact hessian localParametrix row column = refl

------------------------------------------------------------------------
-- Exact cardinality N = 3072.
------------------------------------------------------------------------

periodicSide4SiteCount :
  length (Block.physicalBlockSites Block.side4) ≡ 256
periodicSide4SiteCount =
  Count.haloOffsetEnumerationLength Block.side4

bondCellCount : length Cell.bondCells4 ≡ 1024
bondCellCount
  rewrite Count.lengthCartesian
    (allCyclicIndices four)
    (Block.physicalBlockSites Block.side4)
  | Count.lengthAllCyclicIndices four
  | periodicSide4SiteCount = refl

physicalCoordinateCount :
  length Physical.physicalSU2Coordinates4 ≡ 3072
physicalCoordinateCount
  rewrite Count.lengthCartesian
    Physical.lieCoordinates3 Cell.bondCells4
  | bondCellCount = refl

supportCountN : Nat
supportCountN = 3072

supportCountExact :
  length Physical.physicalSU2Coordinates4 ≡ supportCountN
supportCountExact = physicalCoordinateCount

------------------------------------------------------------------------
-- Literal side-four periodic block distance and r0=8.
------------------------------------------------------------------------

cyclicDistance4 : Axis4 → Axis4 → Nat
cyclicDistance4 zeroᵢ zeroᵢ = 0
cyclicDistance4 zeroᵢ (sucᵢ zeroᵢ) = 1
cyclicDistance4 zeroᵢ (sucᵢ (sucᵢ zeroᵢ)) = 2
cyclicDistance4 zeroᵢ (sucᵢ (sucᵢ (sucᵢ zeroᵢ))) = 1
cyclicDistance4 (sucᵢ zeroᵢ) zeroᵢ = 1
cyclicDistance4 (sucᵢ zeroᵢ) (sucᵢ zeroᵢ) = 0
cyclicDistance4 (sucᵢ zeroᵢ) (sucᵢ (sucᵢ zeroᵢ)) = 1
cyclicDistance4 (sucᵢ zeroᵢ) (sucᵢ (sucᵢ (sucᵢ zeroᵢ))) = 2
cyclicDistance4 (sucᵢ (sucᵢ zeroᵢ)) zeroᵢ = 2
cyclicDistance4 (sucᵢ (sucᵢ zeroᵢ)) (sucᵢ zeroᵢ) = 1
cyclicDistance4 (sucᵢ (sucᵢ zeroᵢ)) (sucᵢ (sucᵢ zeroᵢ)) = 0
cyclicDistance4 (sucᵢ (sucᵢ zeroᵢ))
    (sucᵢ (sucᵢ (sucᵢ zeroᵢ))) = 1
cyclicDistance4 (sucᵢ (sucᵢ (sucᵢ zeroᵢ))) zeroᵢ = 1
cyclicDistance4 (sucᵢ (sucᵢ (sucᵢ zeroᵢ))) (sucᵢ zeroᵢ) = 2
cyclicDistance4 (sucᵢ (sucᵢ (sucᵢ zeroᵢ)))
    (sucᵢ (sucᵢ zeroᵢ)) = 1
cyclicDistance4 (sucᵢ (sucᵢ (sucᵢ zeroᵢ)))
    (sucᵢ (sucᵢ (sucᵢ zeroᵢ))) = 0

cyclicDistance4AtMostTwo : ∀ left right →
  cyclicDistance4 left right ≤ 2
cyclicDistance4AtMostTwo zeroᵢ zeroᵢ = z≤n
cyclicDistance4AtMostTwo zeroᵢ (sucᵢ zeroᵢ) = s≤s z≤n
cyclicDistance4AtMostTwo zeroᵢ (sucᵢ (sucᵢ zeroᵢ)) = s≤s (s≤s z≤n)
cyclicDistance4AtMostTwo zeroᵢ (sucᵢ (sucᵢ (sucᵢ zeroᵢ))) = s≤s z≤n
cyclicDistance4AtMostTwo (sucᵢ zeroᵢ) zeroᵢ = s≤s z≤n
cyclicDistance4AtMostTwo (sucᵢ zeroᵢ) (sucᵢ zeroᵢ) = z≤n
cyclicDistance4AtMostTwo (sucᵢ zeroᵢ) (sucᵢ (sucᵢ zeroᵢ)) = s≤s z≤n
cyclicDistance4AtMostTwo (sucᵢ zeroᵢ)
    (sucᵢ (sucᵢ (sucᵢ zeroᵢ))) = s≤s (s≤s z≤n)
cyclicDistance4AtMostTwo (sucᵢ (sucᵢ zeroᵢ)) zeroᵢ = s≤s (s≤s z≤n)
cyclicDistance4AtMostTwo (sucᵢ (sucᵢ zeroᵢ)) (sucᵢ zeroᵢ) = s≤s z≤n
cyclicDistance4AtMostTwo (sucᵢ (sucᵢ zeroᵢ))
    (sucᵢ (sucᵢ zeroᵢ)) = z≤n
cyclicDistance4AtMostTwo (sucᵢ (sucᵢ zeroᵢ))
    (sucᵢ (sucᵢ (sucᵢ zeroᵢ))) = s≤s z≤n
cyclicDistance4AtMostTwo (sucᵢ (sucᵢ (sucᵢ zeroᵢ))) zeroᵢ = s≤s z≤n
cyclicDistance4AtMostTwo (sucᵢ (sucᵢ (sucᵢ zeroᵢ)))
    (sucᵢ zeroᵢ) = s≤s (s≤s z≤n)
cyclicDistance4AtMostTwo (sucᵢ (sucᵢ (sucᵢ zeroᵢ)))
    (sucᵢ (sucᵢ zeroᵢ)) = s≤s z≤n
cyclicDistance4AtMostTwo (sucᵢ (sucᵢ (sucᵢ zeroᵢ)))
    (sucᵢ (sucᵢ (sucᵢ zeroᵢ))) = z≤n

blockDistance4 :
  Block.PhysicalBlockL Block.side4 →
  Block.PhysicalBlockL Block.side4 → Nat
blockDistance4
    (pair (pair x0 x1) (pair x2 x3))
    (pair (pair y0 y1) (pair y2 y3)) =
  cyclicDistance4 x0 y0
  + (cyclicDistance4 x1 y1
    + (cyclicDistance4 x2 y2 + cyclicDistance4 x3 y3))

blockDistance4AtMostEight : ∀ left right →
  blockDistance4 left right ≤ 8
blockDistance4AtMostEight
    (pair (pair x0 x1) (pair x2 x3))
    (pair (pair y0 y1) (pair y2 y3)) =
  NatP.+-mono-≤
    (cyclicDistance4AtMostTwo x0 y0)
    (NatP.+-mono-≤
      (cyclicDistance4AtMostTwo x1 y1)
      (NatP.+-mono-≤
        (cyclicDistance4AtMostTwo x2 y2)
        (cyclicDistance4AtMostTwo x3 y3)))

coordinateBlock :
  Physical.PhysicalSU2Coordinate4 → Block.PhysicalBlockL Block.side4
coordinateBlock (pair coordinate (pair axis site)) = site

physicalCoordinateDistance :
  Physical.PhysicalSU2Coordinate4 →
  Physical.PhysicalSU2Coordinate4 → Nat
physicalCoordinateDistance left right =
  blockDistance4 (coordinateBlock left) (coordinateBlock right)

supportRadiusR0 : Nat
supportRadiusR0 = 8

fullRowSupportRadiusExact : ∀ left right →
  physicalCoordinateDistance left right ≤ supportRadiusR0
fullRowSupportRadiusExact left right =
  blockDistance4AtMostEight (coordinateBlock left) (coordinateBlock right)

------------------------------------------------------------------------
-- Exact numerical calibration.
------------------------------------------------------------------------

weightBase weightInflation epsilonThreshold epsilonAtCollar21 : ℚ
weightBase = + 2 / 1
weightInflation = + 256 / 1
epsilonThreshold = + 1 / 1572864
epsilonAtCollar21 = + 1 / 2097152

collarM : Nat
collarM = 21

weightInflationIsTwoPowerEight :
  weightInflation
  ≡ weightBase * (weightBase * (weightBase * (weightBase
      * (weightBase * (weightBase * (weightBase * weightBase))))))
weightInflationIsTwoPowerEight = ℚRing.solve []

supportCountAsRational : ℚ
supportCountAsRational = Sums.natAsRational supportCountN

supportCountValueExact :
  supportCountAsRational ≡ + 3072 / 1
supportCountValueExact = refl

thresholdSpendsExactlyHalf :
  supportCountAsRational * epsilonThreshold * weightInflation
  ≡ + 1 / 2
thresholdSpendsExactlyHalf = ℚRing.solve []

collar21SpendsThreeEighths :
  supportCountAsRational * epsilonAtCollar21 * weightInflation
  ≡ + 3 / 8
collar21SpendsThreeEighths = ℚRing.solve []

threeEighthsBelowHalf : (+ 3 / 8) ≤ (+ 1 / 2)
threeEighthsBelowHalf =
  let
    instance
      oneEighthNN : NonNegative (+ 1 / 8)
      oneEighthNN = ℚ.nonNegative (ℚP.nonNegative⁻¹ (+ 1 / 8))
  in
  subst
    (λ upper → (+ 3 / 8) ≤ upper)
    (ℚRing.solve [])
    (ℚP.p≤p+q (+ 3 / 8) (+ 1 / 8))

collar21HalfContractionArithmetic :
  supportCountAsRational * epsilonAtCollar21 * weightInflation
  ≤ + 1 / 2
collar21HalfContractionArithmetic =
  subst
    (λ lower → lower ≤ (+ 1 / 2))
    (sym collar21SpendsThreeEighths)
    threeEighthsBelowHalf

record PhysicalResidualEntryAtCollar21
    (hessian localParametrix : Physical.PhysicalSU2Matrix4) : Set₁ where
  field
    exponentialWeight :
      Physical.PhysicalSU2Coordinate4 → ℚ
    weightNonnegative : ∀ coordinate →
      0ℚ ≤ exponentialWeight coordinate
    weightedEntryBound : ∀ left right →
      ℚ.∣ literalResidualKernel hessian localParametrix left right ∣
        * exponentialWeight right
      ≤ (epsilonAtCollar21 * weightInflation)
        * exponentialWeight left

open PhysicalResidualEntryAtCollar21 public

-- The data above is exactly the remaining physical entry estimate.  Together
-- with supportCountExact and collar21HalfContractionArithmetic it instantiates
-- BalabanP33FiniteWeightedSupportCountHalfExact without any further numerical
-- choice.

literalResidualKernelFormulaLevel : ProofLevel
literalResidualKernelFormulaLevel = machineChecked

literalSide4CoordinateCount3072Level : ProofLevel
literalSide4CoordinateCount3072Level = machineChecked

literalFullRowRadius8Level : ProofLevel
literalFullRowRadius8Level = machineChecked

literalResidualNumericalCalibrationLevel : ProofLevel
literalResidualNumericalCalibrationLevel = machineChecked

physicalCollar21EntryEstimateLevel : ProofLevel
physicalCollar21EntryEstimateLevel = conditional
