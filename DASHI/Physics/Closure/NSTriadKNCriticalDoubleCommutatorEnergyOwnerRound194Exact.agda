module DASHI.Physics.Closure.NSTriadKNCriticalDoubleCommutatorEnergyOwnerRound194Exact where

------------------------------------------------------------------------
-- ROUND194 / COMPLETE PRODUCTION-ENERGY OWNER IDENTITY
--
-- R191 gives one energy ledger for the complete double commutator P.
-- R192 splits its full forcing work exactly into self + external owners.
-- This file composes them on the literal Galerkin selected triad:
--
--   d |P|²
--     = 2 sigma |P|²
--       + W(P,F_self)
--       + W(P,F_ext).
--
-- Thus Package A has no remaining owner ambiguity.  There are exactly two
-- forcing-work payments to discharge, and the external one has the explicit
-- signed residual-cell expansion of R193.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; trans)

import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNWaleffeAmplitudeDampedNetworkTangentRound94Exact as R94
import DASHI.Physics.Closure.NSTriadKNPhysicalSelectedTriadNetworkSplitRound95Exact as R95
import DASHI.Physics.Closure.NSTriadKNCriticalNormalizedCurlSlotTangentRound157Exact as R157
import DASHI.Physics.Closure.NSTriadKNCriticalSlotDifferenceEnergyRound158Exact as R158
import DASHI.Physics.Closure.NSTriadKNCriticalSecondSlotDifferenceTangentRound159Exact as R159
import DASHI.Physics.Closure.NSTriadKNCriticalDoubleCommutatorTangentRound190Exact as R190
import DASHI.Physics.Closure.NSTriadKNCriticalDoubleCommutatorEnergyRound191Exact as R191
import DASHI.Physics.Closure.NSTriadKNCriticalDoubleCommutatorOwnerSplitRound192Exact as R192

physicalCompleteProductionEnergyOwnerIdentity :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F} {I : C3.ModeInverseSquare F E}
    (S : Helical.HelicalModeScalars F)
    (cK cP : C3.Carrier F)
    (rhoK rhoP rhoQ : C3.Carrier F)
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (tau : Physical.PhysicalTriadIncidence) →
  let uK = Audit.velocityAt system (Physical.k tau)
      uP = Audit.velocityAt system (Physical.p tau)
      uQ = Audit.velocityAt system (Physical.q tau)
      production = R190.doubleCommutatorAmplitude E S cK cP
        (Physical.k tau) (Physical.p tau) (Physical.q tau) uK uP uQ
      kqSelf = R157.slotDifferenceNetworkForcing E S (Physical.k tau) (Physical.q tau)
        uK uP uQ (R95.selfForcingK system tau) (R95.selfForcingP system tau) (R95.selfForcingQ system tau)
      kqExt = R157.slotDifferenceNetworkForcing E S (Physical.k tau) (Physical.q tau)
        uK uP uQ (R95.externalForcingK system tau) (R95.externalForcingP system tau) (R95.externalForcingQ system tau)
      pqSelf = R159.slotPQDifferenceNetworkForcing E S (Physical.p tau) (Physical.q tau)
        uK uP uQ (R95.selfForcingK system tau) (R95.selfForcingP system tau) (R95.selfForcingQ system tau)
      pqExt = R159.slotPQDifferenceNetworkForcing E S (Physical.p tau) (Physical.q tau)
        uK uP uQ (R95.externalForcingK system tau) (R95.externalForcingP system tau) (R95.externalForcingQ system tau)
      selfF = R190.weightedTwoChannel cK cP kqSelf pqSelf
      extF = R190.weightedTwoChannel cK cP kqExt pqExt
      decay = R94.totalNegativeDecay rhoK rhoP rhoQ
  in
  R158.slotDefectEnergyTangent production
    (R190.doubleCommutatorTangent E S cK cP
      (Physical.k tau) (Physical.p tau) (Physical.q tau) uK uP uQ
      (R94.dampedPlusForcing rhoK uK (R95.fullForcingK system tau))
      (R94.dampedPlusForcing rhoP uP (R95.fullForcingP system tau))
      (R94.dampedPlusForcing rhoQ uQ (R95.fullForcingQ system tau)))
  ≡
  C3.complexAdd
    (C3.complexMultiply (C3.complexAdd decay decay)
      (R158.slotDefectEnergy production))
    (C3.complexAdd
      (R158.forcingWork production selfF)
      (R158.forcingWork production extF))
physicalCompleteProductionEnergyOwnerIdentity {E = E}
    S cK cP rhoK rhoP rhoQ system tau =
  let
    uK = Audit.velocityAt system (Physical.k tau)
    uP = Audit.velocityAt system (Physical.p tau)
    uQ = Audit.velocityAt system (Physical.q tau)
    production = R190.doubleCommutatorAmplitude E S cK cP
      (Physical.k tau) (Physical.p tau) (Physical.q tau) uK uP uQ
    fullF = R190.doubleCommutatorForcing E S cK cP
      (Physical.k tau) (Physical.p tau) (Physical.q tau) uK uP uQ
      (R95.fullForcingK system tau) (R95.fullForcingP system tau) (R95.fullForcingQ system tau)
    decay = R94.totalNegativeDecay rhoK rhoP rhoQ
  in
  trans
    (R191.doubleCommutatorEnergyLedger
      E S cK cP
      (Physical.k tau) (Physical.p tau) (Physical.q tau)
      rhoK rhoP rhoQ uK uP uQ
      (R95.fullForcingK system tau)
      (R95.fullForcingP system tau)
      (R95.fullForcingQ system tau))
    (cong
      (C3.complexAdd
        (C3.complexMultiply (C3.complexAdd decay decay)
          (R158.slotDefectEnergy production)))
      (R192.physicalCombinedForcingWorkIsSelfPlusExternal
        S cK cP system tau))

round194CompleteEnergyOwnerIdentityClosed : Bool
round194CompleteEnergyOwnerIdentityClosed = true

round194OwnerAmbiguityRemaining : Bool
round194OwnerAmbiguityRemaining = false

round194SelfPaymentClosed : Bool
round194SelfPaymentClosed = false

round194ExternalPaymentClosed : Bool
round194ExternalPaymentClosed = false

round194PackageAClosed : Bool
round194PackageAClosed = false

round194ClayPromotion : Bool
round194ClayPromotion = false
