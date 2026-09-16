{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP116PhysicalDecoupledComparisonRound261Exact where

------------------------------------------------------------------------
-- ROUND261 / LITERAL CMP116 HESSIAN -> DECOUPLED CAUCHY COMPARISON -> ℚ DEBT
--
-- Round260 correctly requires a COMPARISON debt plus a REFERENCE anchor.  This
-- module pays only the comparison side.  It does not invent or select the
-- reference anchor.
--
-- Existing machinery already proves:
--
--   marked substituted-background stability
--       -> Cauchy coefficient-domain comparison.
--
-- Existing Round103 machinery already owns the literal physical CMP116 Hessian
-- carrier.  The only cross-layer weld introduced here is an explicit same-
-- object identity between the physical selected/reference Hessian difference
-- and the norm of that decoupled coefficient difference.
--
-- A second, separate receipt coarsens the resulting REAL source majorant to an
-- embedded rational shell debt.  Therefore
--
--   source comparison != rational shell != reference anchor.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
open import Data.Rational.Base using (ℚ; 0ℚ; _≤_)

open import DASHI.Foundations.RealAnalysisAxioms using
  (ℝ; 0ℝ; _*ℝ_; _-ℝ_; absℝ; _≤ℝ_; ≤ℝ-trans)
import DASHI.Foundations.FinitePolydiscCauchyAxioms as Cauchy

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanCMP109116LiteralDifferentiatedCarrierRound103Exact as Carrier
import DASHI.Physics.YangMills.BalabanCMP109116SourceContinuationRound103Exact as Source
import DASHI.Physics.YangMills.BalabanDecoupledActivityHessian as Decoupled
import DASHI.Physics.YangMills.BalabanA2RationalShellBudgetToRealRound108Exact as Embed

------------------------------------------------------------------------
-- Same-object physical / decoupled comparison surface.
------------------------------------------------------------------------

record CMP116PhysicalDecoupledComparison
    {carrier : Carrier.LiteralDifferentiatedEffectiveDensityCarrier}
    (D : Decoupled.DecoupledActivityHessianData) : Set₁ where
  field
    selectedDomain referenceDomain : Decoupled.DomainSequence D
    component : Decoupled.Component D

    selectedBackground referenceBackground :
      Source.Background (Carrier.source carrier)
    physicalU physicalV : Source.Tangent (Carrier.source carrier)

    decoupledU decoupledV : Decoupled.FieldVariation D

    lipschitz markedInput : ℝ
    substitutionDistance :
      Cauchy.BoundaryAssignment
        (Decoupled.cauchy D)
        (Decoupled.componentIndices D component) → ℝ

    lipschitzNonnegative : 0ℝ ≤ℝ lipschitz
    substitutionDistanceNonnegative :
      ∀ s → 0ℝ ≤ℝ substitutionDistance s
    markedInputNonnegative : 0ℝ ≤ℝ markedInput

    -- Source-facing local D²E stability on the decoupling boundary.
    boundaryHessianStable :
      ∀ s →
      Cauchy.normValue (Decoupled.cauchy D)
        (Cauchy._-Value_ (Decoupled.cauchy D)
          (Cauchy.evaluate
            (Decoupled.cauchy D)
            (Decoupled.asFunction D selectedDomain component decoupledU decoupledV)
            (Cauchy.boundaryAssignment (Decoupled.cauchy D) s))
          (Cauchy.evaluate
            (Decoupled.cauchy D)
            (Decoupled.asFunction D referenceDomain component decoupledU decoupledV)
            (Cauchy.boundaryAssignment (Decoupled.cauchy D) s)))
      ≤ℝ lipschitz *ℝ substitutionDistance s

    -- Source-facing CMP116 marked substituted-background comparison.
    substitutionIsMarked :
      ∀ s → substitutionDistance s ≤ℝ markedInput

    -- SAME-OBJECT WELD.  This is not derived from numerical coincidence.  It
    -- identifies the literal selected/reference physical Hessian difference
    -- with the exact decoupled coefficient difference being source-bounded.
    physicalDifferenceIsDecoupledCoefficientNorm :
      absℝ
        (Carrier.cmp116PhysicalMarkedHessian carrier
          selectedBackground physicalU physicalV
        -ℝ Carrier.cmp116PhysicalMarkedHessian carrier
          referenceBackground physicalU physicalV)
      ≡
      Cauchy.normValue (Decoupled.cauchy D)
        (Cauchy._-Value_ (Decoupled.cauchy D)
          (Decoupled.decoupledHessianCoefficient
            D selectedDomain component decoupledU decoupledV)
          (Decoupled.decoupledHessianCoefficient
            D referenceDomain component decoupledU decoupledV))

open CMP116PhysicalDecoupledComparison public

physicalComparisonRealMajorized :
  ∀ {carrier}
    {D : Decoupled.DecoupledActivityHessianData} →
  (dataSet : CMP116PhysicalDecoupledComparison {carrier = carrier} D) →
  absℝ
    (Carrier.cmp116PhysicalMarkedHessian carrier
      (selectedBackground dataSet) (physicalU dataSet) (physicalV dataSet)
    -ℝ Carrier.cmp116PhysicalMarkedHessian carrier
      (referenceBackground dataSet) (physicalU dataSet) (physicalV dataSet))
  ≤ℝ
  lipschitz dataSet *ℝ markedInput dataSet
physicalComparisonRealMajorized {D = D} dataSet
  rewrite physicalDifferenceIsDecoupledCoefficientNorm dataSet =
  Decoupled.markedSubstitutionStabilityLiftsToCoefficient
    D
    (selectedDomain dataSet)
    (referenceDomain dataSet)
    (component dataSet)
    (decoupledU dataSet)
    (decoupledV dataSet)
    (lipschitz dataSet)
    (markedInput dataSet)
    (substitutionDistance dataSet)
    (lipschitzNonnegative dataSet)
    (substitutionDistanceNonnegative dataSet)
    (markedInputNonnegative dataSet)
    (boundaryHessianStable dataSet)
    (substitutionIsMarked dataSet)

------------------------------------------------------------------------
-- Real source majorant -> rational comparison debt.
------------------------------------------------------------------------

record RationalizedCMP116PhysicalComparison
    {carrier : Carrier.LiteralDifferentiatedEffectiveDensityCarrier}
    {D : Decoupled.DecoupledActivityHessianData}
    (dataSet : CMP116PhysicalDecoupledComparison {carrier = carrier} D)
    (embedding : Embed.OrderedRationalRealRingEmbedding) : Set₁ where
  field
    comparisonDebt : ℚ
    comparisonDebtNonnegative : 0ℚ ≤ comparisonDebt

    -- This is the exact real->rational coarsening / same-shell payment.  It is
    -- deliberately separate from the physical Cauchy comparison above.
    realSourceMajorantBelowEmbeddedDebt :
      lipschitz dataSet *ℝ markedInput dataSet
      ≤ℝ Embed.embed embedding comparisonDebt

open RationalizedCMP116PhysicalComparison public

physicalComparisonRationalMajorized :
  ∀ {carrier D embedding}
    {dataSet : CMP116PhysicalDecoupledComparison {carrier = carrier} D} →
  (rationalized : RationalizedCMP116PhysicalComparison dataSet embedding) →
  absℝ
    (Carrier.cmp116PhysicalMarkedHessian carrier
      (selectedBackground dataSet) (physicalU dataSet) (physicalV dataSet)
    -ℝ Carrier.cmp116PhysicalMarkedHessian carrier
      (referenceBackground dataSet) (physicalU dataSet) (physicalV dataSet))
  ≤ℝ
  Embed.embed embedding (comparisonDebt rationalized)
physicalComparisonRationalMajorized {dataSet = dataSet} rationalized =
  ≤ℝ-trans
    (physicalComparisonRealMajorized dataSet)
    (realSourceMajorantBelowEmbeddedDebt rationalized)

------------------------------------------------------------------------
-- Status / firewalls.
------------------------------------------------------------------------

physicalDecoupledComparisonCompilerLevel : ProofLevel
physicalDecoupledComparisonCompilerLevel = machineChecked

physicalDifferenceCoefficientIdentityLevel : ProofLevel
physicalDifferenceCoefficientIdentityLevel = conditional

markedSubstitutionSourceEstimateLevel : ProofLevel
markedSubstitutionSourceEstimateLevel = conditional

realSourceMajorantToRationalShellLevel : ProofLevel
realSourceMajorantToRationalShellLevel = conditional


data CMP109CMP116IdentityMeansDecoupledCoefficientIdentityPermission : Set where

data RealComparisonMeansRationalShellPermission : Set where

data RationalComparisonMeansReferenceAnchorPermission : Set where

data SourceComparisonMeansAbsoluteHessianPermission : Set where

literalSecondVariationDoesNotAutomaticallyIdentifyDecoupledCoefficient :
  CMP109CMP116IdentityMeansDecoupledCoefficientIdentityPermission → ⊥
literalSecondVariationDoesNotAutomaticallyIdentifyDecoupledCoefficient ()

realComparisonDoesNotManufactureRationalShell :
  RealComparisonMeansRationalShellPermission → ⊥
realComparisonDoesNotManufactureRationalShell ()

rationalComparisonDoesNotManufactureReferenceAnchor :
  RationalComparisonMeansReferenceAnchorPermission → ⊥
rationalComparisonDoesNotManufactureReferenceAnchor ()

comparisonStillDoesNotGiveAbsoluteHessian :
  SourceComparisonMeansAbsoluteHessianPermission → ⊥
comparisonStillDoesNotGiveAbsoluteHessian ()

record CMP116PhysicalComparisonBoundary261 : Set where
  constructor cmp116-physical-comparison-boundary261
  field
    literalPhysicalHessianReused : Bool
    decoupledCauchyCompilerReused : Bool
    physicalCoefficientIdentityExplicit : Bool
    markedSubstitutionEstimateExplicit : Bool
    rationalCoarseningSeparate : Bool
    referenceAnchorIncludedHere : Bool
    absoluteHessianClaimedHere : Bool

canonicalCMP116PhysicalComparisonBoundary261 : CMP116PhysicalComparisonBoundary261
canonicalCMP116PhysicalComparisonBoundary261 =
  cmp116-physical-comparison-boundary261
    true true true true true false false
