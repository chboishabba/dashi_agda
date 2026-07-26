module DASHI.Physics.YangMills.BalabanPath4SU2ConcreteCoarseBlockExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational using (ℚ; 0ℚ; _+_; _-_; _*_; _≤_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier
open import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact
  using (SiteField; sumRational; sumRationalCong)
open import DASHI.Physics.YangMills.BalabanFiniteSumFubiniExact
  using (sumRationalZero)
open import DASHI.Physics.YangMills.BalabanPath4AxisAverageExact
open import DASHI.Physics.YangMills.BalabanPhysicalAxisPartitionExact
  using (globalBlockInner)
open import DASHI.Physics.YangMills.BalabanPath4PhysicalMartingaleOrthogonalityExact
  using
    ( FieldEqual
    ; axisAverage4RespectsPointwise
    ; projectedFixedPointwise
    ; commutingProjectPreservesFixedPointwise
    ; innerSubtractLeft
    ; innerRespectsRightPointwise
    )
open import DASHI.Physics.YangMills.BalabanPath4BondHodgeCoercivityExact
  using (RationalBondField4; bondComponent)
open import DASHI.Physics.YangMills.BalabanConfiguredSide4PeriodicVectorCalculusExact
  using (scalarBondInner)
open import DASHI.Physics.YangMills.BalabanPath4SU2PhysicalTangentExact
open import DASHI.Physics.YangMills.BalabanPath4SU2PeriodicHodgeProducerExact
  using (physicalTangentInner)
open import DASHI.Physics.YangMills.BalabanPath4SU2CompleteGaugeFixedHessianExact
  using
    ( LiteralCoarseBlockData
    ; zeroPhysicalSU2Tangent4
    ; scalarBondInnerZeroRight
    ; physicalTangentInnerNonnegative
    ; completeLiteralGaugeFixedHessianData
    ; completeUniformReferenceHodgeCoercivity
    )
open import DASHI.Physics.YangMills.BalabanSU2GaugeFixedHessianQuadraticExact
  using (GaugeFixedHessianQuadraticData; gaugeFixedHessianQuadraticForm)
open import DASHI.Physics.YangMills.BalabanConfiguredRGSide4Certificate
  using (configuredPathCoercivityConstant)

------------------------------------------------------------------------
-- The coarse carrier is the literal range of the four commuting coordinate
-- conditional expectations.  Keeping the fixed-point proof in the carrier makes
-- Q* an actual inclusion and avoids quotient or function-extensionality axioms.
------------------------------------------------------------------------

record CoarseScalar4 : Set where
  constructor coarseScalar4
  field
    coarseField : SiteField side4
    coarseFixed : ∀ axis site →
      axisAverage4 coarseField axis site ≡ coarseField site

open CoarseScalar4 public

CoarseSU2Bond4 : Set
CoarseSU2Bond4 = SU2Component → Axis4 → CoarseScalar4

axis0 axis1 axis2 axis3 : Axis4
axis0 = zeroᵢ
axis1 = sucᵢ zeroᵢ
axis2 = sucᵢ (sucᵢ zeroᵢ)
axis3 = sucᵢ (sucᵢ (sucᵢ zeroᵢ))

average0123Fixed0 : ∀ siteField →
  FieldEqual (axisAverage4 (average0123 siteField) axis0)
    (average0123 siteField)
average0123Fixed0 siteField =
  commutingProjectPreservesFixedPointwise
    axis0 axis3 (average012 siteField)
    (DASHI.Physics.YangMills.BalabanPath4PhysicalMartingaleOrthogonalityExact.average012Fixed0
      siteField)

average0123Fixed1 : ∀ siteField →
  FieldEqual (axisAverage4 (average0123 siteField) axis1)
    (average0123 siteField)
average0123Fixed1 siteField =
  commutingProjectPreservesFixedPointwise
    axis1 axis3 (average012 siteField)
    (DASHI.Physics.YangMills.BalabanPath4PhysicalMartingaleOrthogonalityExact.average012Fixed1
      siteField)

average0123Fixed2 : ∀ siteField →
  FieldEqual (axisAverage4 (average0123 siteField) axis2)
    (average0123 siteField)
average0123Fixed2 siteField =
  commutingProjectPreservesFixedPointwise
    axis2 axis3 (average012 siteField)
    (projectedFixedPointwise axis2 (average01 siteField))

average0123Fixed3 : ∀ siteField →
  FieldEqual (axisAverage4 (average0123 siteField) axis3)
    (average0123 siteField)
average0123Fixed3 siteField =
  projectedFixedPointwise axis3 (average012 siteField)

average0123Fixed : ∀ siteField axis site →
  axisAverage4 (average0123 siteField) axis site
  ≡ average0123 siteField site
average0123Fixed siteField zeroᵢ = average0123Fixed0 siteField
average0123Fixed siteField (sucᵢ zeroᵢ) = average0123Fixed1 siteField
average0123Fixed siteField (sucᵢ (sucᵢ zeroᵢ)) = average0123Fixed2 siteField
average0123Fixed siteField (sucᵢ (sucᵢ (sucᵢ zeroᵢ))) =
  average0123Fixed3 siteField

literalBlockAverageQ : PhysicalSU2Tangent4 → CoarseSU2Bond4
literalBlockAverageQ tangent component bondAxis =
  coarseScalar4
    (average0123 (bondComponent (tangent component) bondAxis))
    (average0123Fixed (bondComponent (tangent component) bondAxis))

literalBlockAverageAdjointQStar : CoarseSU2Bond4 → PhysicalSU2Tangent4
literalBlockAverageAdjointQStar coarse component (pair site bondAxis) =
  coarseField (coarse component bondAxis) site

------------------------------------------------------------------------
-- Fully averaged fields are exactly fixed by Q*Q.
------------------------------------------------------------------------

average0123OfFixed : ∀ siteField →
  (∀ axis site → axisAverage4 siteField axis site ≡ siteField site) →
  FieldEqual (average0123 siteField) siteField
average0123OfFixed siteField fixed site =
  trans
    (axisAverage4RespectsPointwise axis3
      (axisAverage4RespectsPointwise axis2
        (axisAverage4RespectsPointwise axis1 (fixed axis0))) site)
    (trans
      (axisAverage4RespectsPointwise axis3
        (axisAverage4RespectsPointwise axis2 (fixed axis1)) site)
      (trans
        (axisAverage4RespectsPointwise axis3 (fixed axis2) site)
        (fixed axis3 site)))

blockAverageCoisometry : ∀ coarse component bondAxis site →
  coarseField
    (literalBlockAverageQ
      (literalBlockAverageAdjointQStar coarse) component bondAxis) site
  ≡ coarseField (coarse component bondAxis) site
blockAverageCoisometry coarse component bondAxis =
  average0123OfFixed
    (coarseField (coarse component bondAxis))
    (coarseFixed (coarse component bondAxis))

blockAverageProjectionIdempotent : ∀ tangent component bondAxis site →
  literalBlockAverageAdjointQStar
    (literalBlockAverageQ
      (literalBlockAverageAdjointQStar (literalBlockAverageQ tangent)))
    component (pair site bondAxis)
  ≡ literalBlockAverageAdjointQStar (literalBlockAverageQ tangent)
    component (pair site bondAxis)
blockAverageProjectionIdempotent tangent component bondAxis site =
  blockAverageCoisometry (literalBlockAverageQ tangent)
    component bondAxis site

------------------------------------------------------------------------
-- Q and Q* are adjoint for the repository's literal fine inner product.
------------------------------------------------------------------------

projectOncePairingExact : ∀ axis siteField fixedField →
  FieldEqual (axisAverage4 fixedField axis) fixedField →
  globalBlockInner siteField fixedField
  ≡ globalBlockInner (axisAverage4 siteField axis) fixedField
projectOncePairingExact axis siteField fixedField fixed =
  sym
    (trans
      (DASHI.Physics.YangMills.BalabanPhysicalAxisPartitionExact.physicalAxisAverage4SelfAdjoint
        axis siteField fixedField)
      (innerRespectsRightPointwise siteField fixed))

average0123PairingExact : ∀ siteField fixedField →
  (∀ axis site → axisAverage4 fixedField axis site ≡ fixedField site) →
  globalBlockInner siteField fixedField
  ≡ globalBlockInner (average0123 siteField) fixedField
average0123PairingExact siteField fixedField fixed =
  trans
    (projectOncePairingExact axis0 siteField fixedField (fixed axis0))
    (trans
      (projectOncePairingExact axis1 (average0 siteField) fixedField (fixed axis1))
      (trans
        (projectOncePairingExact axis2 (average01 siteField) fixedField (fixed axis2))
        (projectOncePairingExact axis3 (average012 siteField) fixedField
          (fixed axis3))))

coarseScalarAdjoint : (Axis4 → CoarseScalar4) → RationalBondField4
coarseScalarAdjoint coarse (pair site bondAxis) =
  coarseField (coarse bondAxis) site

scalarBlockProjection : RationalBondField4 → RationalBondField4
scalarBlockProjection field (pair site bondAxis) =
  average0123 (bondComponent field bondAxis) site

scalarBlockAverageAdjointExact : ∀ fine coarse →
  scalarBondInner fine (coarseScalarAdjoint coarse)
  ≡ scalarBondInner (scalarBlockProjection fine) (coarseScalarAdjoint coarse)
scalarBlockAverageAdjointExact fine coarse =
  sumRationalCong
    (allCyclicIndices four)
    (λ bondAxis →
      globalBlockInner (bondComponent fine bondAxis)
        (coarseField (coarse bondAxis)))
    (λ bondAxis →
      globalBlockInner (average0123 (bondComponent fine bondAxis))
        (coarseField (coarse bondAxis)))
    (λ bondAxis →
      average0123PairingExact
        (bondComponent fine bondAxis)
        (coarseField (coarse bondAxis))
        (coarseFixed (coarse bondAxis)))

concreteCoarseInner : CoarseSU2Bond4 → CoarseSU2Bond4 → ℚ
concreteCoarseInner left right =
  physicalTangentInner
    (literalBlockAverageAdjointQStar left)
    (literalBlockAverageAdjointQStar right)

blockAverageAdjointExact : ∀ fine coarse →
  physicalTangentInner fine (literalBlockAverageAdjointQStar coarse)
  ≡ concreteCoarseInner (literalBlockAverageQ fine) coarse
blockAverageAdjointExact fine coarse =
  cong₂ _+_
    (scalarBlockAverageAdjointExact
      (fine component1) (coarse component1))
    (cong₂ _+_
      (scalarBlockAverageAdjointExact
        (fine component2) (coarse component2))
      (scalarBlockAverageAdjointExact
        (fine component3) (coarse component3)))

------------------------------------------------------------------------
-- Orthogonal fine fluctuation and exact reconstruction.
------------------------------------------------------------------------

fineProjection : PhysicalSU2Tangent4 → PhysicalSU2Tangent4
fineProjection tangent =
  literalBlockAverageAdjointQStar (literalBlockAverageQ tangent)

fineFluctuation : PhysicalSU2Tangent4 → PhysicalSU2Tangent4
fineFluctuation tangent component bond =
  tangent component bond - fineProjection tangent component bond

fineProjectionReconstruction : ∀ tangent component bond →
  fineFluctuation tangent component bond
    + fineProjection tangent component bond
  ≡ tangent component bond
fineProjectionReconstruction tangent component bond =
  ℚRing.solve-∀
    (tangent component bond)
    (fineProjection tangent component bond)

average0123ResidualOrthogonal : ∀ siteField fixedField →
  (∀ axis site → axisAverage4 fixedField axis site ≡ fixedField site) →
  globalBlockInner
    (DASHI.Physics.YangMills.BalabanPath4PhysicalMartingaleOrthogonalityExact.subtractField
      siteField (average0123 siteField))
    fixedField
  ≡ 0ℚ
average0123ResidualOrthogonal siteField fixedField fixed =
  trans
    (innerSubtractLeft siteField (average0123 siteField) fixedField)
    (trans
      (cong
        (λ value → globalBlockInner siteField fixedField - value)
        (sym (average0123PairingExact siteField fixedField fixed)))
      (ℚP.+-inverseʳ (globalBlockInner siteField fixedField)))

scalarBlockKernelOrthogonal : ∀ fine coarse →
  scalarBondInner
    (λ bond → fine bond - scalarBlockProjection fine bond)
    (coarseScalarAdjoint coarse)
  ≡ 0ℚ
scalarBlockKernelOrthogonal fine coarse =
  trans
    (sumRationalCong
      (allCyclicIndices four)
      (λ bondAxis →
        globalBlockInner
          (DASHI.Physics.YangMills.BalabanPath4PhysicalMartingaleOrthogonalityExact.subtractField
            (bondComponent fine bondAxis)
            (average0123 (bondComponent fine bondAxis)))
          (coarseField (coarse bondAxis)))
      (λ _ → 0ℚ)
      (λ bondAxis →
        average0123ResidualOrthogonal
          (bondComponent fine bondAxis)
          (coarseField (coarse bondAxis))
          (coarseFixed (coarse bondAxis))))
    (sumRationalZero (allCyclicIndices four))

blockAverageKernelOrthogonal : ∀ fine coarse →
  physicalTangentInner (fineFluctuation fine)
    (literalBlockAverageAdjointQStar coarse)
  ≡ 0ℚ
blockAverageKernelOrthogonal fine coarse =
  trans
    (cong₂ _+_
      (scalarBlockKernelOrthogonal
        (fine component1) (coarse component1))
      (cong₂ _+_
        (scalarBlockKernelOrthogonal
          (fine component2) (coarse component2))
        (scalarBlockKernelOrthogonal
          (fine component3) (coarse component3))))
    (ℚRing.solve-∀)

------------------------------------------------------------------------
-- Concrete zero, LiteralCoarseBlockData instance, and C1 coercivity on ker Q.
------------------------------------------------------------------------

zeroSiteField4 : SiteField side4
zeroSiteField4 site = 0ℚ

axisAverage4Zero : ∀ axis site →
  axisAverage4 zeroSiteField4 axis site ≡ 0ℚ
axisAverage4Zero axis site =
  trans
    (cong (quarter *_)
      (sumRationalZero (allCyclicIndices side4)))
    (ℚRing.solve-∀)

zeroCoarseSU2Bond4 : CoarseSU2Bond4
zeroCoarseSU2Bond4 component bondAxis =
  coarseScalar4 zeroSiteField4 axisAverage4Zero

concreteLiteralCoarseBlockData : LiteralCoarseBlockData CoarseSU2Bond4
concreteLiteralCoarseBlockData = record
  { averageOperator = literalBlockAverageQ
  ; averageAdjointOperator = literalBlockAverageAdjointQStar
  ; innerCoarseOperator = concreteCoarseInner
  ; coarseZeroOperator = zeroCoarseSU2Bond4
  ; averageAdjointExact = blockAverageAdjointExact
  ; innerCoarseZeroExact = scalarBondInnerZeroRight zeroPhysicalSU2Tangent4
  ; coarseNormNonnegativeExact = λ coarse →
      physicalTangentInnerNonnegative
        (literalBlockAverageAdjointQStar coarse)
  }

concreteGaugeFixedHessianData :
  GaugeFixedHessianQuadraticData
    PhysicalSU2Tangent4
    DASHI.Physics.YangMills.BalabanPath4SU2PeriodicHodgeProducerExact.Lie3SiteField
    CoarseSU2Bond4 ℚ
concreteGaugeFixedHessianData =
  completeLiteralGaugeFixedHessianData concreteLiteralCoarseBlockData

CoarseAverageZero : PhysicalSU2Tangent4 → Set
CoarseAverageZero tangent =
  ∀ component bondAxis site →
  coarseField (literalBlockAverageQ tangent component bondAxis) site ≡ 0ℚ

coarseAverageZeroImpliesPhysicalBlockAverageZero : ∀ tangent →
  CoarseAverageZero tangent → PhysicalBlockAverageZero tangent
coarseAverageZeroImpliesPhysicalBlockAverageZero tangent averageZero
  component bondAxis site =
  averageZero component bondAxis site

fineFluctuationCoercivity : ∀ tangent →
  CoarseAverageZero tangent →
  configuredPathCoercivityConstant * physicalUnweightedNormSq tangent
  ≤ gaugeFixedHessianQuadraticForm concreteGaugeFixedHessianData tangent
fineFluctuationCoercivity tangent averageZero =
  completeUniformReferenceHodgeCoercivity
    concreteLiteralCoarseBlockData tangent
    (coarseAverageZeroImpliesPhysicalBlockAverageZero tangent averageZero)

concreteCoarseBlockCarrierLevel : ProofLevel
concreteCoarseBlockCarrierLevel = machineChecked

concreteBlockAverageAdjointLevel : ProofLevel
concreteBlockAverageAdjointLevel = machineChecked

concreteBlockAverageCoisometryLevel : ProofLevel
concreteBlockAverageCoisometryLevel = machineChecked

concreteCoarseFineOrthogonalityLevel : ProofLevel
concreteCoarseFineOrthogonalityLevel = machineChecked

concreteFineFluctuationCoercivityLevel : ProofLevel
concreteFineFluctuationCoercivityLevel = machineChecked
