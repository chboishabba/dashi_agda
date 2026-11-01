module DASHI.Physics.Laws.ExistingPhysicsAdapter where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.List using (List)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Physics.AxiomSet as Axiom
import DASHI.Geometry.DifferentialGeometryParity as DifferentialGeometry
import DASHI.Physics.Closure.CrossDomainVariationalSpine as Variational
import DASHI.Physics.Closure.KnownLimitsRecovery as Limits
import DASHI.Physics.GR as GR
import DASHI.Promotion.MaxwellHodgeSourceConservationObligations as Maxwell
import DASHI.Physics.Closure.NavierStokesWeakSolutionInterface as NavierStokes
import DASHI.Physics.YangMills.YMMassGapRoute as YangMills
import DASHI.Physics.QFT.AQFTTypedNetSurface as AQFT
import DASHI.Promotion.StandardModelFirstPrinciplesGapIndex as StandardModel

-- Adapter into the already-implemented repository lanes.  This is intentionally
-- proof-relevant: a consumer must provide the exact existing object, status, or
-- blocker surface rather than a Boolean saying that a topic is present.
record ExistingPhysicsAdapter : Setω where
  field
    axiomStatus : Axiom.AxiomLawSurfaceStatus
    differentialGeometryStatus :
      DifferentialGeometry.DifferentialGeometryParityStatus
    variationalSpine : Variational.CrossDomainVariationalSpineBoundary
    knownLimits : Limits.KnownLimitsRecoveryWitness
    grAdapter : GR.GRAdapter
    maxwellObligations : List Maxwell.ConservationObligationRow
    navierStokesCarrier : NavierStokes.NavierStokesCarrier
    yangMillsRoute : (N : Nat) → YangMills.YMMassGapRoute N
    aqftStatus : AQFT.AQFTTypedNetSurfaceStatus
    standardModelGapRow : StandardModel.FirstPrinciplesGapRow

-- A canonical status snapshot can be constructed from existing repository
-- values without claiming the missing variational, empirical, or continuum
-- witnesses needed by the full adapter.
record CanonicalPhysicsStatusSnapshot : Setω where
  field
    axiomStatus : Axiom.AxiomLawSurfaceStatus
    knownLimits : Limits.KnownLimitsRecoveryWitness
    grAdapter   : GR.GRAdapter
    maxwellObligations : List Maxwell.ConservationObligationRow
    navierStokesCarrier : NavierStokes.NavierStokesCarrier
    yangMillsRoute : (N : Nat) → YangMills.YMMassGapRoute N
    aqftStatus : AQFT.AQFTTypedNetSurfaceStatus
    standardModelGaugeGap : StandardModel.FirstPrinciplesGapRow

canonicalPhysicsStatusSnapshot : CanonicalPhysicsStatusSnapshot
canonicalPhysicsStatusSnapshot = record
  { axiomStatus = Axiom.canonicalAxiomLawSurfaceStatus
  ; knownLimits = Limits.canonicalKnownLimitsRecovery
  ; grAdapter = GR.canonicalGRAdapter
  ; maxwellObligations = Maxwell.canonicalConservationRows
  ; navierStokesCarrier = NavierStokes.canonicalFiniteNavierStokesCarrier
  ; yangMillsRoute = YangMills.canonicalYMMassGapRoute
  ; aqftStatus = AQFT.typedSurfaceOnlyNoInteractingPromotion
  ; standardModelGaugeGap = StandardModel.gaugeGroupUniquenessGapRow
  }
