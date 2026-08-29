module DASHI.Physics.Closure.NSTriadKNPhysicalRawCurlPartnerBonyRound186Exact where

------------------------------------------------------------------------
-- ROUND186 / PHYSICAL RAW-CURL PARTNER BLOCKS ON THE BONY GEOMETRY
--
-- Round185 reduces the global fibre problem to three within-class Gram debts.
-- This file removes one remaining abstraction: the partner blocks are now the
-- literal raw p/q curl kernels evaluated on a physical Galerkin incidence and
-- its shared-output swap, and their class is the authoritative Round63/130
-- Bony class.
--
-- Because swap exchanges LH <-> HL and fixes HH->low and comparable, the
-- natural partner-level class space has exactly three elements:
--
--   farLow = LH ∪ HL,  highHigh = HH->low,  comparable = CC.
--
-- The class of a physical partner block is invariant under swapping its two
-- ordered representatives.  No estimate or absolute value is introduced.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadSymmetry as Symmetry
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNAntiParallelHelicitySlotKernelRound145Exact as R145
import DASHI.Physics.Closure.NSTriadKNComLiteralBonyOutputFibrePartitionRound63Exact as Bony
import DASHI.Physics.Closure.NSTriadKNPhysicalBonyTagSwapRound130Exact as R130
import DASHI.Physics.Closure.NSTriadKNRawCurlLowOutputKernelMassRound178Exact as R178
import DASHI.Physics.Closure.NSTriadKNPartnerBlockGramLedgerRound181Exact as R181

F = R178.F

data PartnerBonyClass : Set where
  farLowClass highHighClass comparableClass : PartnerBonyClass

partnerBonyClass : Physical.PhysicalTriadIncidence → PartnerBonyClass
partnerBonyClass tau with Bony.bonyTag tau
... | Bony.lhTag = farLowClass
... | Bony.hlTag = farLowClass
... | Bony.hhToLowTag = highHighClass
... | Bony.comparableTag = comparableClass

partnerBonyClassSwapInvariant :
  (tau : Physical.PhysicalTriadIncidence) →
  partnerBonyClass (Symmetry.swapTriad tau) ≡ partnerBonyClass tau
partnerBonyClassSwapInvariant tau
  with Bony.bonyTag tau | R130.bonyTagSwapEquivariant tau
... | Bony.lhTag | tagEq rewrite tagEq = refl
... | Bony.hlTag | tagEq rewrite tagEq = refl
... | Bony.hhToLowTag | tagEq rewrite tagEq = refl
... | Bony.comparableTag | tagEq rewrite tagEq = refl

record PhysicalRawCurlCellData
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (tau : Physical.PhysicalTriadIncidence) : Set where
  constructor physical-raw-curl-cell-data
  field
    pTransverse :
      Helical.Transverse E (Physical.p tau)
        (Audit.velocity system (Physical.p tau))
    qTransverse :
      Helical.Transverse E (Physical.q tau)
        (Audit.velocity system (Physical.q tau))

open PhysicalRawCurlCellData public

rawCurlCell :
  ∀ {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    {system : Audit.FiniteComplex3GalerkinSystem F E I}
    {tau : Physical.PhysicalTriadIncidence} →
  PhysicalRawCurlCellData system tau → C3.Complex3 F
rawCurlCell {E = E} {system = system} {tau = tau} H =
  R145.slotKernel
    (C3.modeVector E (Physical.p tau))
    (C3.modeVector E (Physical.q tau))
    (Audit.velocity system (Physical.p tau))
    (Audit.velocity system (Physical.q tau))

rawCurlSwapCell :
  ∀ {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    {system : Audit.FiniteComplex3GalerkinSystem F E I}
    {tau : Physical.PhysicalTriadIncidence} →
  PhysicalRawCurlCellData system tau → C3.Complex3 F
rawCurlSwapCell {E = E} {system = system} {tau = tau} H =
  R145.slotKernel
    (C3.modeVector E (Physical.q tau))
    (C3.modeVector E (Physical.p tau))
    (Audit.velocity system (Physical.q tau))
    (Audit.velocity system (Physical.p tau))

physicalRawCurlPartnerBlock :
  ∀ {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    {system : Audit.FiniteComplex3GalerkinSystem F E I}
    {tau : Physical.PhysicalTriadIncidence} →
  PhysicalRawCurlCellData system tau → R181.CellPair
physicalRawCurlPartnerBlock H =
  R181.cell-pair (rawCurlCell H) (rawCurlSwapCell H)

physicalRawCurlPartnerClass :
  ∀ {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    {system : Audit.FiniteComplex3GalerkinSystem F E I}
    {tau : Physical.PhysicalTriadIncidence} →
  PhysicalRawCurlCellData system tau → PartnerBonyClass
physicalRawCurlPartnerClass {tau = tau} H = partnerBonyClass tau

-- This owner is now fully physical at the cell/block level.  The next theorem
-- must aggregate lists of these blocks classwise and pay the corresponding
-- within-class Gram debts; no generic Hilbert-space replacement remains at the
-- block-definition seam.
round186PhysicalRawCurlPartnerBlockConstructed : Bool
round186PhysicalRawCurlPartnerBlockConstructed = true

round186PartnerClassSwapInvariant : Bool
round186PartnerClassSwapInvariant = true

round186ThreeWithinClassPhysicalDebtsRemain : Bool
round186ThreeWithinClassPhysicalDebtsRemain = true

round186PackageAClosed : Bool
round186PackageAClosed = false

round186ClayPromotion : Bool
round186ClayPromotion = false
