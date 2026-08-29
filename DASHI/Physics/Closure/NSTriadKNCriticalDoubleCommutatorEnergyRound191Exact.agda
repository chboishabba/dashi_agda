module DASHI.Physics.Closure.NSTriadKNCriticalDoubleCommutatorEnergyRound191Exact where

------------------------------------------------------------------------
-- ROUND191 / ENERGY LEDGER FOR THE COMPLETE DOUBLE COMMUTATOR
--
-- Round190 shows that the COMPLETE two-channel critical commutator amplitude
-- obeys one damped-forced equation
--
--   dP = sigma P + F_P.
--
-- Apply the already-proved Round158 complex-square tangent identity directly
-- to P.  The two slot-difference ledgers therefore collapse to one exact
-- production-energy ledger:
--
--   d |P|² = (sigma+sigma)|P|² + W(P,F_P).
--
-- All growth is now owned by ONE signed forcing-work object.  This is a
-- sharper target than estimating the KQ and PQ channels independently.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNWaleffeAmplitudeDampedNetworkTangentRound94Exact as R94
import DASHI.Physics.Closure.NSTriadKNCriticalSlotDifferenceEnergyRound158Exact as R158
import DASHI.Physics.Closure.NSTriadKNCriticalDoubleCommutatorTangentRound190Exact as R190

doubleCommutatorEnergyLedger :
  ∀ {r} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F)
    (S : Helical.HelicalModeScalars F)
    (cK cP : C3.Carrier F)
    (k p q : Z3.FourierMode)
    (rhoK rhoP rhoQ : C3.Carrier F)
    (uK uP uQ fK fP fQ : C3.Complex3 F) →
  let production = R190.doubleCommutatorAmplitude E S cK cP k p q uK uP uQ
      forcing = R190.doubleCommutatorForcing E S cK cP k p q uK uP uQ fK fP fQ
      decay = R94.totalNegativeDecay rhoK rhoP rhoQ
  in
  R158.slotDefectEnergyTangent production
    (R190.doubleCommutatorTangent E S cK cP k p q uK uP uQ
      (R94.dampedPlusForcing rhoK uK fK)
      (R94.dampedPlusForcing rhoP uP fP)
      (R94.dampedPlusForcing rhoQ uQ fQ))
  ≡
  C3.complexAdd
    (C3.complexMultiply (C3.complexAdd decay decay)
      (R158.slotDefectEnergy production))
    (R158.forcingWork production forcing)
doubleCommutatorEnergyLedger
    E S cK cP k p q rhoK rhoP rhoQ uK uP uQ fK fP fQ =
  let
    production = R190.doubleCommutatorAmplitude E S cK cP k p q uK uP uQ
    forcing = R190.doubleCommutatorForcing E S cK cP k p q uK uP uQ fK fP fQ
    decay = R94.totalNegativeDecay rhoK rhoP rhoQ
  in
  trans
    (cong (R158.slotDefectEnergyTangent production)
      (R190.doubleCommutatorDampedNetworkEquation
        E S cK cP k p q rhoK rhoP rhoQ uK uP uQ fK fP fQ))
    (R158.dampedForcedEnergyIdentity decay production forcing
      (R158.totalNegativeDecayIsConjugationFixed rhoK rhoP rhoQ))

round191CompleteProductionEnergyLedgerClosed : Bool
round191CompleteProductionEnergyLedgerClosed = true

round191GrowthOwnedBySingleSignedForcingWork : Bool
round191GrowthOwnedBySingleSignedForcingWork = true

round191CombinedForcingWorkPaymentClosed : Bool
round191CombinedForcingWorkPaymentClosed = false

round191PackageAClosed : Bool
round191PackageAClosed = false

round191ClayPromotion : Bool
round191ClayPromotion = false
