module DASHI.Physics.Closure.NSTriadKNExternalWaleffeQuarticCellExpansionRound115Exact where

------------------------------------------------------------------------
-- ROUND115 / ACTUAL EXTERNAL WALEFFE RESIDUAL AS A FINITE QUARTIC CELL SUM
--
-- Round112 identifies the actual external Waleffe forcing with three literal
-- self-orbit-removed output-fibre sums.  Round114 says that, once those sums
-- are reindexed cellwise, every paired weighted cell has a canonical
-- commutator-plus-defect decomposition.
--
-- The remaining bookkeeping seam is therefore to distribute the Waleffe
-- network functional over the THREE residual convolution lists themselves.
-- This module closes that seam exactly.
--
-- For a selected physical triad tau and a residual incidence sigma, define
--
--   K-cell(sigma) = < N_sigma , u_p x u_q >,
--   P-cell(sigma) = < u_k , N_sigma x u_q >,
--   Q-cell(sigma) = < u_k , u_p x N_sigma >,
--
-- where N_sigma is the repository's literal projected ordered Galerkin term.
-- The external Waleffe forcing is then EXACTLY the finite sum of these three
-- residual cell families.  No absolute value, estimate, statistical closure,
-- or replacement by the old commutator functional occurs here.
--
-- Consequently the next mathematical object is genuinely cell-local:
-- construct a partner map on these actual cells and evaluate
--
--   defect(sigma) = T(partner sigma) + T(sigma).
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym; trans)

import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadOrbitConstruction as Orbit
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNComplex3HermitianAdditiveLaws as Additive
import DASHI.Physics.Closure.NSTriadKNComplex3BeltramiCrossSuppressionRound93Exact as Cross
import DASHI.Physics.Closure.NSTriadKNWaleffeAmplitudeDampedNetworkTangentRound94Exact as Tangent
import DASHI.Physics.Closure.NSTriadKNExternalOutputFibreSelfOrbitRemovalRound111Exact as Residual
import DASHI.Physics.Closure.NSTriadKNExternalWaleffeResidualCarrierRound112Exact as R112

------------------------------------------------------------------------
-- Generic finite linearity in each of the three forcing slots.
------------------------------------------------------------------------

foldKSlot :
  ∀ {r} {F : C3.RealField r} →
  C3.Complex3 F → C3.Complex3 F →
  List (C3.Complex3 F) → C3.Complex F
foldKSlot {F = F} uP uQ [] =
  C3.hermitianPairing3 (C3.complex3Zero F) (Cross.complex3Cross uP uQ)
foldKSlot uP uQ (f ∷ rest) =
  C3.complexAdd
    (C3.hermitianPairing3 f (Cross.complex3Cross uP uQ))
    (foldKSlot uP uQ rest)

foldKSlotIsPairingOfVectorSum :
  ∀ {r} {F : C3.RealField r}
    (uP uQ : C3.Complex3 F)
    (forces : List (C3.Complex3 F)) →
  foldKSlot uP uQ forces
  ≡ C3.hermitianPairing3 (Audit.sumVectors forces)
      (Cross.complex3Cross uP uQ)
foldKSlotIsPairingOfVectorSum uP uQ [] = refl
foldKSlotIsPairingOfVectorSum uP uQ (f ∷ rest) =
  trans
    (cong
      (C3.complexAdd
        (C3.hermitianPairing3 f (Cross.complex3Cross uP uQ)))
      (foldKSlotIsPairingOfVectorSum uP uQ rest))
    (sym
      (Additive.hermitianPairingAddLeft
        f (Audit.sumVectors rest) (Cross.complex3Cross uP uQ)))

foldPSlot :
  ∀ {r} {F : C3.RealField r} →
  C3.Complex3 F → C3.Complex3 F →
  List (C3.Complex3 F) → C3.Complex F
foldPSlot {F = F} uK uQ [] =
  C3.hermitianPairing3 uK
    (Cross.complex3Cross (C3.complex3Zero F) uQ)
foldPSlot uK uQ (f ∷ rest) =
  C3.complexAdd
    (C3.hermitianPairing3 uK (Cross.complex3Cross f uQ))
    (foldPSlot uK uQ rest)

pSlotAdditivity :
  ∀ {r} {F : C3.RealField r}
    (uK uQ a b : C3.Complex3 F) →
  C3.hermitianPairing3 uK
    (Cross.complex3Cross (C3.complex3Add a b) uQ)
  ≡ C3.complexAdd
      (C3.hermitianPairing3 uK (Cross.complex3Cross a uQ))
      (C3.hermitianPairing3 uK (Cross.complex3Cross b uQ))
pSlotAdditivity uK uQ a b =
  trans
    (cong (C3.hermitianPairing3 uK)
      (Tangent.crossAddLeft a b uQ))
    (Additive.hermitianPairingAddRight
      uK (Cross.complex3Cross a uQ) (Cross.complex3Cross b uQ))

foldPSlotIsPairingOfVectorSum :
  ∀ {r} {F : C3.RealField r}
    (uK uQ : C3.Complex3 F)
    (forces : List (C3.Complex3 F)) →
  foldPSlot uK uQ forces
  ≡ C3.hermitianPairing3 uK
      (Cross.complex3Cross (Audit.sumVectors forces) uQ)
foldPSlotIsPairingOfVectorSum uK uQ [] = refl
foldPSlotIsPairingOfVectorSum uK uQ (f ∷ rest) =
  trans
    (cong
      (C3.complexAdd
        (C3.hermitianPairing3 uK (Cross.complex3Cross f uQ)))
      (foldPSlotIsPairingOfVectorSum uK uQ rest))
    (sym (pSlotAdditivity uK uQ f (Audit.sumVectors rest)))

foldQSlot :
  ∀ {r} {F : C3.RealField r} →
  C3.Complex3 F → C3.Complex3 F →
  List (C3.Complex3 F) → C3.Complex F
foldQSlot {F = F} uK uP [] =
  C3.hermitianPairing3 uK
    (Cross.complex3Cross uP (C3.complex3Zero F))
foldQSlot uK uP (f ∷ rest) =
  C3.complexAdd
    (C3.hermitianPairing3 uK (Cross.complex3Cross uP f))
    (foldQSlot uK uP rest)

qSlotAdditivity :
  ∀ {r} {F : C3.RealField r}
    (uK uP a b : C3.Complex3 F) →
  C3.hermitianPairing3 uK
    (Cross.complex3Cross uP (C3.complex3Add a b))
  ≡ C3.complexAdd
      (C3.hermitianPairing3 uK (Cross.complex3Cross uP a))
      (C3.hermitianPairing3 uK (Cross.complex3Cross uP b))
qSlotAdditivity uK uP a b =
  trans
    (cong (C3.hermitianPairing3 uK)
      (Tangent.crossAddRight uP a b))
    (Additive.hermitianPairingAddRight
      uK (Cross.complex3Cross uP a) (Cross.complex3Cross uP b))

foldQSlotIsPairingOfVectorSum :
  ∀ {r} {F : C3.RealField r}
    (uK uP : C3.Complex3 F)
    (forces : List (C3.Complex3 F)) →
  foldQSlot uK uP forces
  ≡ C3.hermitianPairing3 uK
      (Cross.complex3Cross uP (Audit.sumVectors forces))
foldQSlotIsPairingOfVectorSum uK uP [] = refl
foldQSlotIsPairingOfVectorSum uK uP (f ∷ rest) =
  trans
    (cong
      (C3.complexAdd
        (C3.hermitianPairing3 uK (Cross.complex3Cross uP f)))
      (foldQSlotIsPairingOfVectorSum uK uP rest))
    (sym (qSlotAdditivity uK uP f (Audit.sumVectors rest)))

------------------------------------------------------------------------
-- The THREE literal residual incidence carriers from Round112.
------------------------------------------------------------------------

kResidualCarrier :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (tau : Physical.PhysicalTriadIncidence) →
  R112.ThreeLegResidualMembership system tau →
  List Physical.PhysicalTriadIncidence
kResidualCarrier system tau M =
  Residual.externalResidualCarrier system tau
    (R112.kMember M) (R112.kSwapMember M) (R112.kSwapDifferent M)

pResidualCarrier :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (tau : Physical.PhysicalTriadIncidence) →
  R112.ThreeLegResidualMembership system tau →
  List Physical.PhysicalTriadIncidence
pResidualCarrier system tau M =
  Residual.externalResidualCarrier system (Orbit.pEnergyLeg tau)
    (R112.pMember M) (R112.pSwapMember M) (R112.pSwapDifferent M)

qResidualCarrier :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (tau : Physical.PhysicalTriadIncidence) →
  R112.ThreeLegResidualMembership system tau →
  List Physical.PhysicalTriadIncidence
qResidualCarrier system tau M =
  Residual.externalResidualCarrier system (Orbit.qEnergyLeg tau)
    (R112.qMember M) (R112.qSwapMember M) (R112.qSwapDifferent M)

kQuarticCellFold :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (tau : Physical.PhysicalTriadIncidence) →
  R112.ThreeLegResidualMembership system tau → C3.Complex F
kQuarticCellFold system tau M =
  foldKSlot
    (Audit.velocity system (Physical.p tau))
    (Audit.velocity system (Physical.q tau))
    (Audit.mapTriadTerms system (kResidualCarrier system tau M))

pQuarticCellFold :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (tau : Physical.PhysicalTriadIncidence) →
  R112.ThreeLegResidualMembership system tau → C3.Complex F
pQuarticCellFold system tau M =
  foldPSlot
    (Audit.velocity system (Physical.k tau))
    (Audit.velocity system (Physical.q tau))
    (Audit.mapTriadTerms system (pResidualCarrier system tau M))

qQuarticCellFold :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (tau : Physical.PhysicalTriadIncidence) →
  R112.ThreeLegResidualMembership system tau → C3.Complex F
qQuarticCellFold system tau M =
  foldQSlot
    (Audit.velocity system (Physical.k tau))
    (Audit.velocity system (Physical.p tau))
    (Audit.mapTriadTerms system (qResidualCarrier system tau M))

externalResidualQuarticCellSum :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (tau : Physical.PhysicalTriadIncidence) →
  R112.ThreeLegResidualMembership system tau → C3.Complex F
externalResidualQuarticCellSum system tau M =
  C3.complexAdd
    (C3.complexAdd
      (kQuarticCellFold system tau M)
      (pQuarticCellFold system tau M))
    (qQuarticCellFold system tau M)

externalResidualQuarticCellSumIsActualWaleffeForcing :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (tau : Physical.PhysicalTriadIncidence)
    (M : R112.ThreeLegResidualMembership system tau) →
  externalResidualQuarticCellSum system tau M
  ≡ R112.externalResidualNetworkForcing system tau M
externalResidualQuarticCellSumIsActualWaleffeForcing system tau M =
  cong₂ C3.complexAdd
    (cong₂ C3.complexAdd
      (foldKSlotIsPairingOfVectorSum
        (Audit.velocity system (Physical.p tau))
        (Audit.velocity system (Physical.q tau))
        (Audit.mapTriadTerms system (kResidualCarrier system tau M)))
      (foldPSlotIsPairingOfVectorSum
        (Audit.velocity system (Physical.k tau))
        (Audit.velocity system (Physical.q tau))
        (Audit.mapTriadTerms system (pResidualCarrier system tau M))))
    (foldQSlotIsPairingOfVectorSum
      (Audit.velocity system (Physical.k tau))
      (Audit.velocity system (Physical.p tau))
      (Audit.mapTriadTerms system (qResidualCarrier system tau M)))

round115ActualExternalWaleffeResidualExpandedIntoQuarticCells : Bool
round115ActualExternalWaleffeResidualExpandedIntoQuarticCells = true

round115PhysicalCellPartnerDefectIdentified : Bool
round115PhysicalCellPartnerDefectIdentified = false

round115ActualExternalWaleffeResidualExpandedIntoQuarticCellsIsTrue :
  round115ActualExternalWaleffeResidualExpandedIntoQuarticCells ≡ true
round115ActualExternalWaleffeResidualExpandedIntoQuarticCellsIsTrue = refl

round115PhysicalCellPartnerDefectIdentifiedIsFalse :
  round115PhysicalCellPartnerDefectIdentified ≡ false
round115PhysicalCellPartnerDefectIdentifiedIsFalse = refl
