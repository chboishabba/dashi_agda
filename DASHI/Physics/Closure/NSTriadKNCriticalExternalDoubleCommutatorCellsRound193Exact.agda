module DASHI.Physics.Closure.NSTriadKNCriticalExternalDoubleCommutatorCellsRound193Exact where

------------------------------------------------------------------------
-- ROUND193 / COMPLETE EXTERNAL DOUBLE-COMMUTATOR FORCE AS SIGNED CELLS
--
-- R163 already expands the KQ external normalized-curl forcing difference into
-- six signed folds on the literal K/P/Q self-orbit-removed residual fibres.
-- The complete R190 forcing also contains the cyclic PQ slot difference.  This
-- file derives its six-fold expansion and then combines both channels with the
-- SAME critical radial coefficients.
--
-- Thus the external owner in the one-variable R191/R192 production-energy
-- ledger is no longer opaque:
--
--   F_P^ext = c_k * (six signed KQ folds)
--           + c_p * (six signed PQ folds).
--
-- No absolute value, shell count, or cardinality estimate is introduced.  The
-- next analytic theorem may work directly on this complete signed residual
-- cell network rather than paying KQ and PQ separately.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Relation.Binary.PropositionalEquality using (cong; trans)

import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplexCommutativeRingExact as Ring
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNComplex3BeltramiCrossSuppressionRound93Exact as Cross
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNExternalWaleffeQuarticCellExpansionRound115Exact as R115
import DASHI.Physics.Closure.NSTriadKNHelicitySignNormalizedCurlRound142Exact as R142
import DASHI.Physics.Closure.NSTriadKNCriticalSecondSlotDifferenceTangentRound159Exact as R159
import DASHI.Physics.Closure.NSTriadKNCriticalExternalSlotResidualCarrierRound162Exact as R162
import DASHI.Physics.Closure.NSTriadKNCriticalExternalSlotCellExpansionRound163Exact as R163
import DASHI.Physics.Closure.NSTriadKNCriticalDoubleCommutatorTangentRound190Exact as R190

externalPQSignedCellFold :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F} {I : C3.ModeInverseSquare F E}
    (S : Helical.HelicalModeScalars F)
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (tau : Physical.PhysicalTriadIncidence) →
  R162.ThreeLegExternalResidualWitness system tau → C3.Complex F
externalPQSignedCellFold {E = E} S system tau W =
  let
    uK = Audit.velocityAt system (Physical.k tau)
    uP = Audit.velocityAt system (Physical.p tau)
    uQ = Audit.velocityAt system (Physical.q tau)
    SpUP = R142.normalizedCurl E S (Physical.p tau) uP
    SqUQ = R142.normalizedCurl E S (Physical.q tau) uQ
    Kplus = R115.foldKSlot SpUP uQ (R163.kForces W)
    Kminus = R115.foldKSlot uP SqUQ (R163.kForces W)
    Pplus = R115.foldPSlot uK uQ
      (R163.mapNormalizedCurl E S (Physical.p tau) (R163.pForces W))
    Pminus = R115.foldPSlot uK SqUQ (R163.pForces W)
    Qplus = R115.foldQSlot uK SpUP (R163.qForces W)
    Qminus = R115.foldQSlot uK uP
      (R163.mapNormalizedCurl E S (Physical.q tau) (R163.qForces W))
  in
  C3.complexAdd
    (C3.complexSubtract Kplus Kminus)
    (C3.complexAdd
      (C3.complexSubtract Pplus Pminus)
      (C3.complexSubtract Qplus Qminus))

externalPQSignedCellFoldIsResidualSlotForcing :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F} {I : C3.ModeInverseSquare F E}
    (S : Helical.HelicalModeScalars F)
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (tau : Physical.PhysicalTriadIncidence)
    (W : R162.ThreeLegExternalResidualWitness system tau) →
  externalPQSignedCellFold S system tau W
  ≡
  R159.slotPQDifferenceNetworkForcing E S (Physical.p tau) (Physical.q tau)
    (Audit.velocityAt system (Physical.k tau))
    (Audit.velocityAt system (Physical.p tau))
    (Audit.velocityAt system (Physical.q tau))
    (R162.kResidualVector W) (R162.pResidualVector W) (R162.qResidualVector W)
externalPQSignedCellFoldIsResidualSlotForcing {F = F} {E = E} S system tau W =
  let
    uK = Audit.velocityAt system (Physical.k tau)
    uP = Audit.velocityAt system (Physical.p tau)
    uQ = Audit.velocityAt system (Physical.q tau)
    SpUP = R142.normalizedCurl E S (Physical.p tau) uP
    SqUQ = R142.normalizedCurl E S (Physical.q tau) uQ
    kf = R163.kForces W
    pf = R163.pForces W
    qf = R163.qForces W

    kPlus :
      R115.foldKSlot SpUP uQ kf
      ≡ C3.hermitianPairing3 (R162.kResidualVector W)
          (Cross.complex3Cross SpUP uQ)
    kPlus = R115.foldKSlotIsPairingOfVectorSum SpUP uQ kf

    kMinus :
      R115.foldKSlot uP SqUQ kf
      ≡ C3.hermitianPairing3 (R162.kResidualVector W)
          (Cross.complex3Cross uP SqUQ)
    kMinus = R115.foldKSlotIsPairingOfVectorSum uP SqUQ kf

    pPlus :
      R115.foldPSlot uK uQ
        (R163.mapNormalizedCurl E S (Physical.p tau) pf)
      ≡ C3.hermitianPairing3 uK
          (Cross.complex3Cross
            (R142.normalizedCurl E S (Physical.p tau) (R162.pResidualVector W))
            uQ)
    pPlus = trans
      (R115.foldPSlotIsPairingOfVectorSum uK uQ
        (R163.mapNormalizedCurl E S (Physical.p tau) pf))
      (cong
        (λ v → C3.hermitianPairing3 uK (Cross.complex3Cross v uQ))
        (R163.sumVectorsMapNormalizedCurl E S (Physical.p tau) pf))

    pMinus :
      R115.foldPSlot uK SqUQ pf
      ≡ C3.hermitianPairing3 uK
          (Cross.complex3Cross (R162.pResidualVector W) SqUQ)
    pMinus = R115.foldPSlotIsPairingOfVectorSum uK SqUQ pf

    qPlus :
      R115.foldQSlot uK SpUP qf
      ≡ C3.hermitianPairing3 uK
          (Cross.complex3Cross SpUP (R162.qResidualVector W))
    qPlus = R115.foldQSlotIsPairingOfVectorSum uK SpUP qf

    qMinus :
      R115.foldQSlot uK uP
        (R163.mapNormalizedCurl E S (Physical.q tau) qf)
      ≡ C3.hermitianPairing3 uK
          (Cross.complex3Cross uP
            (R142.normalizedCurl E S (Physical.q tau) (R162.qResidualVector W)))
    qMinus = trans
      (R115.foldQSlotIsPairingOfVectorSum uK uP
        (R163.mapNormalizedCurl E S (Physical.q tau) qf))
      (cong
        (λ v → C3.hermitianPairing3 uK (Cross.complex3Cross uP v))
        (R163.sumVectorsMapNormalizedCurl E S (Physical.q tau) qf))
  in
  rewrite kPlus | kMinus | pPlus | pMinus | qPlus | qMinus =
    R.solve 6
      (λ kp km pp pm qp qm →
        ((kp R.⊕ (R.⊝ km))
          R.⊕ ((pp R.⊕ (R.⊝ pm)) R.⊕ (qp R.⊕ (R.⊝ qm))))
        R.⊜
        (((kp R.⊕ pp) R.⊕ qp)
          R.⊕ (R.⊝ ((km R.⊕ pm) R.⊕ qm))))
      refl
      (C3.hermitianPairing3 (R162.kResidualVector W)
        (Cross.complex3Cross SpUP uQ))
      (C3.hermitianPairing3 (R162.kResidualVector W)
        (Cross.complex3Cross uP SqUQ))
      (C3.hermitianPairing3 uK
        (Cross.complex3Cross
          (R142.normalizedCurl E S (Physical.p tau) (R162.pResidualVector W)) uQ))
      (C3.hermitianPairing3 uK
        (Cross.complex3Cross (R162.pResidualVector W) SqUQ))
      (C3.hermitianPairing3 uK
        (Cross.complex3Cross SpUP (R162.qResidualVector W)))
      (C3.hermitianPairing3 uK
        (Cross.complex3Cross uP
          (R142.normalizedCurl E S (Physical.q tau) (R162.qResidualVector W))))
  where module R = Ring.Solver F

externalDoubleCommutatorSignedCellFold :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F} {I : C3.ModeInverseSquare F E}
    (S : Helical.HelicalModeScalars F)
    (cK cP : C3.Carrier F)
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (tau : Physical.PhysicalTriadIncidence) →
  R162.ThreeLegExternalResidualWitness system tau → C3.Complex F
externalDoubleCommutatorSignedCellFold S cK cP system tau W =
  R190.weightedTwoChannel cK cP
    (R163.externalKQSignedCellFold S system tau W)
    (externalPQSignedCellFold S system tau W)

externalDoubleCommutatorSignedCellFoldIsResidualForcing :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F} {I : C3.ModeInverseSquare F E}
    (S : Helical.HelicalModeScalars F)
    (cK cP : C3.Carrier F)
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (tau : Physical.PhysicalTriadIncidence)
    (W : R162.ThreeLegExternalResidualWitness system tau) →
  externalDoubleCommutatorSignedCellFold S cK cP system tau W
  ≡
  R190.weightedTwoChannel cK cP
    (R159.slotPQDifferenceNetworkForcing E S (Physical.p tau) (Physical.q tau)
      (Audit.velocityAt system (Physical.k tau))
      (Audit.velocityAt system (Physical.p tau))
      (Audit.velocityAt system (Physical.q tau))
      (R162.kResidualVector W) (R162.pResidualVector W) (R162.qResidualVector W))
    (R159.slotPQDifferenceNetworkForcing E S (Physical.p tau) (Physical.q tau)
      (Audit.velocityAt system (Physical.k tau))
      (Audit.velocityAt system (Physical.p tau))
      (Audit.velocityAt system (Physical.q tau))
      (R162.kResidualVector W) (R162.pResidualVector W) (R162.qResidualVector W))
externalDoubleCommutatorSignedCellFoldIsResidualForcing
    S cK cP system tau W
  rewrite R163.externalKQSignedCellFoldIsResidualSlotForcing S system tau W
        | externalPQSignedCellFoldIsResidualSlotForcing S system tau W = refl

round193PQExternalSignedCellExpansionClosed : Bool
round193PQExternalSignedCellExpansionClosed = true

round193CompleteExternalDoubleCommutatorCellExpansionClosed : Bool
round193CompleteExternalDoubleCommutatorCellExpansionClosed = true

round193AbsoluteValueIntroducedBeforeChannelRecombination : Bool
round193AbsoluteValueIntroducedBeforeChannelRecombination = false

round193ExternalCombinedQuadraticPaymentClosed : Bool
round193ExternalCombinedQuadraticPaymentClosed = false

round193PackageAClosed : Bool
round193PackageAClosed = false

round193ClayPromotion : Bool
round193ClayPromotion = false
