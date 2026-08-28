module DASHI.Physics.Closure.NSTriadKNCriticalExternalSlotCellExpansionRound163Exact where

------------------------------------------------------------------------
-- ROUND163 / EXTERNAL NORMALIZED-CURL FORCE AS A SIGNED RESIDUAL CELL SUM
--
-- Round162 puts the external K/P/Q forcings on three literal self-orbit-removed
-- incidence lists.  This module distributes normalized curl through those
-- finite sums and expands the KQ forcing difference into six signed cell folds.
-- No absolute value is taken.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (cong; trans; sym)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadOrbitConstruction as Orbit
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplexCommutativeRingExact as Ring
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNComplex3BeltramiCrossSuppressionRound93Exact as Cross
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNProjectedHelicalSelfForcingVectorRound106Exact as R106
import DASHI.Physics.Closure.NSTriadKNOutputTransverseCrossLerayCancellationRound131Exact as R131
import DASHI.Physics.Closure.NSTriadKNExternalOutputFibreSelfOrbitRemovalRound111Exact as R111
import DASHI.Physics.Closure.NSTriadKNExternalWaleffeQuarticCellExpansionRound115Exact as R115
import DASHI.Physics.Closure.NSTriadKNHelicitySignNormalizedCurlRound142Exact as R142
import DASHI.Physics.Closure.NSTriadKNCriticalNormalizedCurlSlotTangentRound157Exact as R157
import DASHI.Physics.Closure.NSTriadKNCriticalExternalSlotResidualCarrierRound162Exact as R162

mapNormalizedCurl :
  ∀ {r} {F : C3.RealField r} →
  C3.IntegerEmbedding F → Helical.HelicalModeScalars F → Z3.FourierMode →
  List (C3.Complex3 F) → List (C3.Complex3 F)
mapNormalizedCurl E S k [] = []
mapNormalizedCurl E S k (v ∷ rest) =
  R142.normalizedCurl E S k v ∷ mapNormalizedCurl E S k rest

normalizedCurlZero :
  ∀ {r} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F) (S : Helical.HelicalModeScalars F)
    (k : Z3.FourierMode) →
  R142.normalizedCurl E S k (C3.complex3Zero F)
  ≡ C3.complex3Zero F
normalizedCurlZero {F = F} E S k =
  trans
    (cong
      (C3.complex3Scale (C3.realEmbed F (Helical.inverseModeNorm S k)))
      (trans
        (cong (C3.complex3Scale (C3.complexI F))
          (R131.crossZeroRight (C3.modeVector E k)))
        (R106.complex3ScaleZeroVector (C3.complexI F))))
    (R106.complex3ScaleZeroVector
      (C3.realEmbed F (Helical.inverseModeNorm S k)))

sumVectorsMapNormalizedCurl :
  ∀ {r} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F) (S : Helical.HelicalModeScalars F)
    (k : Z3.FourierMode) (forces : List (C3.Complex3 F)) →
  Audit.sumVectors (mapNormalizedCurl E S k forces)
  ≡ R142.normalizedCurl E S k (Audit.sumVectors forces)
sumVectorsMapNormalizedCurl E S k [] = sym (normalizedCurlZero E S k)
sumVectorsMapNormalizedCurl E S k (force ∷ rest) =
  trans
    (cong (C3.complex3Add (R142.normalizedCurl E S k force))
      (sumVectorsMapNormalizedCurl E S k rest))
    (sym (R157.normalizedCurlAdd E S k force (Audit.sumVectors rest)))

kForces :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F} {I : C3.ModeInverseSquare F E}
    {system : Audit.FiniteComplex3GalerkinSystem F E I}
    {tau : Physical.PhysicalTriadIncidence} →
  R162.ThreeLegExternalResidualWitness system tau → List (C3.Complex3 F)
kForces {system = system} {tau = tau} W =
  Audit.mapTriadTerms system
    (R111.externalResidualCarrier system tau
      (R162.kMember W) (R162.kSwapMember W) (R162.kSwapDifferent W))

pForces :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F} {I : C3.ModeInverseSquare F E}
    {system : Audit.FiniteComplex3GalerkinSystem F E I}
    {tau : Physical.PhysicalTriadIncidence} →
  R162.ThreeLegExternalResidualWitness system tau → List (C3.Complex3 F)
pForces {system = system} {tau = tau} W =
  Audit.mapTriadTerms system
    (R111.externalResidualCarrier system (Orbit.pEnergyLeg tau)
      (R162.pMember W) (R162.pSwapMember W) (R162.pSwapDifferent W))

qForces :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F} {I : C3.ModeInverseSquare F E}
    {system : Audit.FiniteComplex3GalerkinSystem F E I}
    {tau : Physical.PhysicalTriadIncidence} →
  R162.ThreeLegExternalResidualWitness system tau → List (C3.Complex3 F)
qForces {system = system} {tau = tau} W =
  Audit.mapTriadTerms system
    (R111.externalResidualCarrier system (Orbit.qEnergyLeg tau)
      (R162.qMember W) (R162.qSwapMember W) (R162.qSwapDifferent W))

externalKQSignedCellFold :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F} {I : C3.ModeInverseSquare F E}
    (S : Helical.HelicalModeScalars F)
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (tau : Physical.PhysicalTriadIncidence) →
  R162.ThreeLegExternalResidualWitness system tau → C3.Complex F
externalKQSignedCellFold {E = E} S system tau W =
  let
    uK = Audit.velocityAt system (Physical.k tau)
    uP = Audit.velocityAt system (Physical.p tau)
    uQ = Audit.velocityAt system (Physical.q tau)
    SkUK = R142.normalizedCurl E S (Physical.k tau) uK
    SqUQ = R142.normalizedCurl E S (Physical.q tau) uQ
    Kplus = R115.foldKSlot uP uQ
      (mapNormalizedCurl E S (Physical.k tau) (kForces W))
    Kminus = R115.foldKSlot uP SqUQ (kForces W)
    Pplus = R115.foldPSlot SkUK uQ (pForces W)
    Pminus = R115.foldPSlot uK SqUQ (pForces W)
    Qplus = R115.foldQSlot SkUK uP (qForces W)
    Qminus = R115.foldQSlot uK uP
      (mapNormalizedCurl E S (Physical.q tau) (qForces W))
  in
  C3.complexAdd
    (C3.complexSubtract Kplus Kminus)
    (C3.complexAdd
      (C3.complexSubtract Pplus Pminus)
      (C3.complexSubtract Qplus Qminus))

externalKQSignedCellFoldIsResidualSlotForcing :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F} {I : C3.ModeInverseSquare F E}
    (S : Helical.HelicalModeScalars F)
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (tau : Physical.PhysicalTriadIncidence)
    (W : R162.ThreeLegExternalResidualWitness system tau) →
  externalKQSignedCellFold S system tau W
  ≡
  R157.slotDifferenceNetworkForcing E S (Physical.k tau) (Physical.q tau)
    (Audit.velocityAt system (Physical.k tau))
    (Audit.velocityAt system (Physical.p tau))
    (Audit.velocityAt system (Physical.q tau))
    (R162.kResidualVector W) (R162.pResidualVector W) (R162.qResidualVector W)
externalKQSignedCellFoldIsResidualSlotForcing {F = F} {E = E} S system tau W =
  let
    uK = Audit.velocityAt system (Physical.k tau)
    uP = Audit.velocityAt system (Physical.p tau)
    uQ = Audit.velocityAt system (Physical.q tau)
    SkUK = R142.normalizedCurl E S (Physical.k tau) uK
    SqUQ = R142.normalizedCurl E S (Physical.q tau) uQ
    kf = kForces W
    pf = pForces W
    qf = qForces W

    kPlus :
      R115.foldKSlot uP uQ (mapNormalizedCurl E S (Physical.k tau) kf)
      ≡ C3.hermitianPairing3
          (R142.normalizedCurl E S (Physical.k tau) (R162.kResidualVector W))
          (Cross.complex3Cross uP uQ)
    kPlus = trans
      (R115.foldKSlotIsPairingOfVectorSum uP uQ
        (mapNormalizedCurl E S (Physical.k tau) kf))
      (cong (λ v → C3.hermitianPairing3 v (Cross.complex3Cross uP uQ))
        (sumVectorsMapNormalizedCurl E S (Physical.k tau) kf))

    kMinus :
      R115.foldKSlot uP SqUQ kf
      ≡ C3.hermitianPairing3 (R162.kResidualVector W)
          (Cross.complex3Cross uP SqUQ)
    kMinus = R115.foldKSlotIsPairingOfVectorSum uP SqUQ kf

    pPlus :
      R115.foldPSlot SkUK uQ pf
      ≡ C3.hermitianPairing3 SkUK
          (Cross.complex3Cross (R162.pResidualVector W) uQ)
    pPlus = R115.foldPSlotIsPairingOfVectorSum SkUK uQ pf

    pMinus :
      R115.foldPSlot uK SqUQ pf
      ≡ C3.hermitianPairing3 uK
          (Cross.complex3Cross (R162.pResidualVector W) SqUQ)
    pMinus = R115.foldPSlotIsPairingOfVectorSum uK SqUQ pf

    qPlus :
      R115.foldQSlot SkUK uP qf
      ≡ C3.hermitianPairing3 SkUK
          (Cross.complex3Cross uP (R162.qResidualVector W))
    qPlus = R115.foldQSlotIsPairingOfVectorSum SkUK uP qf

    qMinus :
      R115.foldQSlot uK uP (mapNormalizedCurl E S (Physical.q tau) qf)
      ≡ C3.hermitianPairing3 uK
          (Cross.complex3Cross uP
            (R142.normalizedCurl E S (Physical.q tau) (R162.qResidualVector W)))
    qMinus = trans
      (R115.foldQSlotIsPairingOfVectorSum uK uP
        (mapNormalizedCurl E S (Physical.q tau) qf))
      (cong (λ v → C3.hermitianPairing3 uK (Cross.complex3Cross uP v))
        (sumVectorsMapNormalizedCurl E S (Physical.q tau) qf))
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
      (C3.hermitianPairing3
        (R142.normalizedCurl E S (Physical.k tau) (R162.kResidualVector W))
        (Cross.complex3Cross uP uQ))
      (C3.hermitianPairing3 (R162.kResidualVector W)
        (Cross.complex3Cross uP SqUQ))
      (C3.hermitianPairing3 SkUK
        (Cross.complex3Cross (R162.pResidualVector W) uQ))
      (C3.hermitianPairing3 uK
        (Cross.complex3Cross (R162.pResidualVector W) SqUQ))
      (C3.hermitianPairing3 SkUK
        (Cross.complex3Cross uP (R162.qResidualVector W)))
      (C3.hermitianPairing3 uK
        (Cross.complex3Cross uP
          (R142.normalizedCurl E S (Physical.q tau) (R162.qResidualVector W))))
  where module R = Ring.Solver F

round163NormalizedCurlDistributesThroughResidualSum : Bool
round163NormalizedCurlDistributesThroughResidualSum = true

round163ExternalKQForcingDifferenceExactSignedCellExpansionClosed : Bool
round163ExternalKQForcingDifferenceExactSignedCellExpansionClosed = true

round163CellwiseAbsoluteValueIntroduced : Bool
round163CellwiseAbsoluteValueIntroduced = false

round163ExternalSignedCellQuadraticVariationPaymentClosed : Bool
round163ExternalSignedCellQuadraticVariationPaymentClosed = false

round163PackageAClosed : Bool
round163PackageAClosed = false

round163ExternalKQForcingDifferenceExactSignedCellExpansionClosedIsTrue :
  round163ExternalKQForcingDifferenceExactSignedCellExpansionClosed ≡ true
round163ExternalKQForcingDifferenceExactSignedCellExpansionClosedIsTrue = refl

round163PackageAClosedIsFalse : round163PackageAClosed ≡ false
round163PackageAClosedIsFalse = refl
