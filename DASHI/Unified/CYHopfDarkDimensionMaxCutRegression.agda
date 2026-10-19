module DASHI.Unified.CYHopfDarkDimensionMaxCutRegression where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Bool using (false; true)

import DASHI.Geometry.CalabiYauPhysicalProducerCompilerExact as CY
import DASHI.Geometry.CalabiYauPhysicalProducerCutset as Physical
import DASHI.Mathematics.Topology.HopfU1PrincipalBundleObligationsExact as Hopf
import DASHI.Mathematics.Topology.HopfU1CurvatureNaturalityExact as Curvature
import DASHI.Physics.Electromagnetism.U1AsSU2AbelianRestrictionExact as EM
import DASHI.Physics.YangMills.BalabanSU2LieAlgebraCarrier as Lie
import DASHI.Physics.YangMills.BalabanSU2LieBracket as Bracket
import DASHI.Empirical.DarkDimensionToyDiscriminatorExact as Dark
import DASHI.Physics.Closure.DarkDimensionStringPromotionBoundaryExact as String

-- Regress existing negative physical-promotion contracts.
noCYVacuumFromDimensionCounting :
  Physical.CalabiYauPhysicalBoundary.dimensionIdentitySuppliesPhysicalModel
    Physical.canonicalCalabiYauPhysicalBoundary ≡ false
noCYVacuumFromDimensionCounting =
  CY.structuralGeometryAloneDoesNotPayPhysicalModel

u1InsideSU2Exists :
  Hopf.HopfPromotionBoundary.concreteU1InsideSU2
    Hopf.canonicalHopfPromotionBoundary ≡ true
u1InsideSU2Exists = refl

smoothHopfNotManufactured :
  Hopf.HopfPromotionBoundary.smoothHopfFromSubgroupAlone
    Hopf.canonicalHopfPromotionBoundary ≡ false
smoothHopfNotManufactured = refl

stringOriginNotInferred :
  String.stringTheoryPromotionPermitted
    String.canonicalDarkDimensionPromotionStatus ≡ false
stringOriginNotInferred = Dark.canonicalStringPromotionStillBlocked

cartanBracketCancellationRegression :
  (a b : EM.U1LieAlgebra) →
  Bracket.lieBracket (EM.embedU1Lie a) (EM.embedU1Lie b)
    ≡ Lie.lieZero
cartanBracketCancellationRegression = Curvature.cartanSelfInteractionVanishes
