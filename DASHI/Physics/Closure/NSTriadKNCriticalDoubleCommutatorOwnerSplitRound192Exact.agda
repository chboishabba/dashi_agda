module DASHI.Physics.Closure.NSTriadKNCriticalDoubleCommutatorOwnerSplitRound192Exact where

------------------------------------------------------------------------
-- ROUND192 / EXACT SELF-EXTERNAL OWNER SPLIT FOR THE COMPLETE COMMUTATOR
--
-- R190/R191 package the two surviving normalized-curl slot differences into
-- ONE damped-forced critical-production variable P with forcing F_P.
-- R160/R161 already split each constituent forcing into selected-triad self
-- and external-network owners.  Because the same radial coefficients weight
-- both owners and forcing work is additive, the COMPLETE R191 growth term
-- inherits the exact split
--
--   F_P(full) = F_P(self) + F_P(ext),
--   W(P,F_P(full)) = W(P,F_P(self)) + W(P,F_P(ext)).
--
-- This is the right owner surface for the remaining analysis: the self term
-- can be welded to the mature internal payment, while the external term can be
-- reopened on the literal self-orbit-removed residual fibres of R162/R163.
-- No absolute value is introduced.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; trans)

import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplexCommutativeRingExact as Ring
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNPhysicalSelectedTriadNetworkSplitRound95Exact as R95
import DASHI.Physics.Closure.NSTriadKNCriticalNormalizedCurlSlotTangentRound157Exact as R157
import DASHI.Physics.Closure.NSTriadKNCriticalSlotDifferenceEnergyRound158Exact as R158
import DASHI.Physics.Closure.NSTriadKNCriticalSecondSlotDifferenceTangentRound159Exact as R159
import DASHI.Physics.Closure.NSTriadKNCriticalSlotForcingSelfExternalSplitRound160Exact as R160
import DASHI.Physics.Closure.NSTriadKNCriticalForcingWorkOwnerSplitRound161Exact as R161
import DASHI.Physics.Closure.NSTriadKNCriticalDoubleCommutatorTangentRound190Exact as R190

combinedForcingSplits :
  ∀ {r} {F : C3.RealField r}
    (cK cP : C3.Carrier F)
    (kqSelf kqExt pqSelf pqExt : C3.Complex F) →
  R190.weightedTwoChannel cK cP
    (C3.complexAdd kqSelf kqExt)
    (C3.complexAdd pqSelf pqExt)
  ≡ C3.complexAdd
      (R190.weightedTwoChannel cK cP kqSelf pqSelf)
      (R190.weightedTwoChannel cK cP kqExt pqExt)
combinedForcingSplits {F = F} cK cP kqSelf kqExt pqSelf pqExt =
  R.solve 6
    (λ a b ks ke ps pe →
      ((a R.⊗ (ks R.⊕ ke)) R.⊕ (b R.⊗ (ps R.⊕ pe)))
      R.⊜
      (((a R.⊗ ks) R.⊕ (b R.⊗ ps))
        R.⊕ ((a R.⊗ ke) R.⊕ (b R.⊗ pe))))
    refl
    (C3.realEmbed F cK) (C3.realEmbed F cP)
    kqSelf kqExt pqSelf pqExt
  where module R = Ring.Solver F

physicalCombinedFullForcingIsSelfPlusExternal :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F} {I : C3.ModeInverseSquare F E}
    (S : Helical.HelicalModeScalars F)
    (cK cP : C3.Carrier F)
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (tau : Physical.PhysicalTriadIncidence) →
  let uK = Audit.velocityAt system (Physical.k tau)
      uP = Audit.velocityAt system (Physical.p tau)
      uQ = Audit.velocityAt system (Physical.q tau)
      kqSelf = R157.slotDifferenceNetworkForcing E S (Physical.k tau) (Physical.q tau)
        uK uP uQ (R95.selfForcingK system tau) (R95.selfForcingP system tau) (R95.selfForcingQ system tau)
      kqExt = R157.slotDifferenceNetworkForcing E S (Physical.k tau) (Physical.q tau)
        uK uP uQ (R95.externalForcingK system tau) (R95.externalForcingP system tau) (R95.externalForcingQ system tau)
      pqSelf = R159.slotPQDifferenceNetworkForcing E S (Physical.p tau) (Physical.q tau)
        uK uP uQ (R95.selfForcingK system tau) (R95.selfForcingP system tau) (R95.selfForcingQ system tau)
      pqExt = R159.slotPQDifferenceNetworkForcing E S (Physical.p tau) (Physical.q tau)
        uK uP uQ (R95.externalForcingK system tau) (R95.externalForcingP system tau) (R95.externalForcingQ system tau)
  in
  R190.doubleCommutatorForcing E S cK cP
    (Physical.k tau) (Physical.p tau) (Physical.q tau)
    uK uP uQ
    (R95.fullForcingK system tau) (R95.fullForcingP system tau) (R95.fullForcingQ system tau)
  ≡ C3.complexAdd
      (R190.weightedTwoChannel cK cP kqSelf pqSelf)
      (R190.weightedTwoChannel cK cP kqExt pqExt)
physicalCombinedFullForcingIsSelfPlusExternal {E = E} S cK cP system tau =
  let
    uK = Audit.velocityAt system (Physical.k tau)
    uP = Audit.velocityAt system (Physical.p tau)
    uQ = Audit.velocityAt system (Physical.q tau)
    kqSelf = R157.slotDifferenceNetworkForcing E S (Physical.k tau) (Physical.q tau)
      uK uP uQ (R95.selfForcingK system tau) (R95.selfForcingP system tau) (R95.selfForcingQ system tau)
    kqExt = R157.slotDifferenceNetworkForcing E S (Physical.k tau) (Physical.q tau)
      uK uP uQ (R95.externalForcingK system tau) (R95.externalForcingP system tau) (R95.externalForcingQ system tau)
    pqSelf = R159.slotPQDifferenceNetworkForcing E S (Physical.p tau) (Physical.q tau)
      uK uP uQ (R95.selfForcingK system tau) (R95.selfForcingP system tau) (R95.selfForcingQ system tau)
    pqExt = R159.slotPQDifferenceNetworkForcing E S (Physical.p tau) (Physical.q tau)
      uK uP uQ (R95.externalForcingK system tau) (R95.externalForcingP system tau) (R95.externalForcingQ system tau)
  in
  trans
    (cong
      (λ kqFull → R190.weightedTwoChannel cK cP kqFull
        (R159.slotPQDifferenceNetworkForcing E S (Physical.p tau) (Physical.q tau)
          uK uP uQ
          (R95.fullForcingK system tau) (R95.fullForcingP system tau) (R95.fullForcingQ system tau)))
      (R160.physicalKQFullForcingDifferenceIsSelfPlusExternal S system tau))
    (trans
      (cong
        (R190.weightedTwoChannel cK cP (C3.complexAdd kqSelf kqExt))
        (R161.physicalPQFullForcingDifferenceIsSelfPlusExternal S system tau))
      (combinedForcingSplits cK cP kqSelf kqExt pqSelf pqExt))

physicalCombinedForcingWorkIsSelfPlusExternal :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F} {I : C3.ModeInverseSquare F E}
    (S : Helical.HelicalModeScalars F)
    (cK cP : C3.Carrier F)
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
      fullF = R190.doubleCommutatorForcing E S cK cP
        (Physical.k tau) (Physical.p tau) (Physical.q tau) uK uP uQ
        (R95.fullForcingK system tau) (R95.fullForcingP system tau) (R95.fullForcingQ system tau)
  in
  R158.forcingWork production fullF
  ≡ C3.complexAdd
      (R158.forcingWork production selfF)
      (R158.forcingWork production extF)
physicalCombinedForcingWorkIsSelfPlusExternal {E = E} S cK cP system tau =
  let
    uK = Audit.velocityAt system (Physical.k tau)
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
    fullF = R190.doubleCommutatorForcing E S cK cP
      (Physical.k tau) (Physical.p tau) (Physical.q tau) uK uP uQ
      (R95.fullForcingK system tau) (R95.fullForcingP system tau) (R95.fullForcingQ system tau)
  in
  trans
    (cong (R158.forcingWork production)
      (physicalCombinedFullForcingIsSelfPlusExternal S cK cP system tau))
    (R161.forcingWorkAdditive production selfF extF)

round192CompleteForcingOwnerSplitClosed : Bool
round192CompleteForcingOwnerSplitClosed = true

round192CompleteForcingWorkOwnerSplitClosed : Bool
round192CompleteForcingWorkOwnerSplitClosed = true

round192SelfOwnerPaymentClosed : Bool
round192SelfOwnerPaymentClosed = false

round192ExternalOwnerPaymentClosed : Bool
round192ExternalOwnerPaymentClosed = false

round192PackageAClosed : Bool
round192PackageAClosed = false

round192ClayPromotion : Bool
round192ClayPromotion = false
