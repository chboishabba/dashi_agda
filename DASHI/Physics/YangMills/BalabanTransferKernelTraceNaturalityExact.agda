module DASHI.Physics.YangMills.BalabanTransferKernelTraceNaturalityExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Martin Lüscher,
-- "Construction of a Selfadjoint, Strictly Positive Transfer Matrix for
-- Euclidean Lattice Gauge Theories", Communications in Mathematical Physics
-- 54 (1977), 283--292. DOI: 10.1007/BF01614090.
--
-- Konrad Osterwalder and Erhard Seiler,
-- "Gauge Field Theories on a Lattice", Annals of Physics 110 (1978),
-- 440--471. DOI: 10.1016/0003-4916(78)90039-8.
--
-- Tadeusz Bałaban,
-- "Propagators and Renormalization Transformations for Lattice Gauge
-- Theories. II", Communications in Mathematical Physics 96 (1984), 223--250.
-- DOI: 10.1007/BF01240221.
--
-- DASHI CONTRIBUTION
--
-- The historical W1--W4 route named four physical requirements but encoded
-- them as Boolean receipts.  The actual transfer theorem can be organized as
-- two commuting squares on theorem-bearing maps.
--
-- Write a transfer step as
--
--     observable --kernel--> transfer-integrand --trace--> observable.
--
-- A spatial coarse-to-fine lift B and a corresponding integrand lift B_K give
-- the two source-facing equations
--
--   (K)  B_K (K_c f) = K_f (B f),
--   (Tr) B   (Tr_c h) = Tr_f (B_K h).
--
-- Equation (K) is where temporal-boundary preservation and large-field slab
-- separation have to be proved from the literal Bałaban block action.
-- Equation (Tr) is the actual partition/integration interchange law.
--
-- Their composition gives
--
--     B (T_c f) = T_f (B f)
--
-- with T = Tr o K.  No Boolean compatibility field is involved.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (trans; cong)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanWilsonTransferIntertwinerExact as Transfer

record TransferKernelTraceNaturality
    (Fine Coarse FineKernel CoarseKernel : Set) : Set₁ where
  field
    liftObservable : Coarse → Fine
    liftKernel : CoarseKernel → FineKernel

    fineKernel : Fine → FineKernel
    coarseKernel : Coarse → CoarseKernel

    fineTrace : FineKernel → Fine
    coarseTrace : CoarseKernel → Coarse

    kernelNaturality :
      ∀ coarse →
      liftKernel (coarseKernel coarse)
      ≡ fineKernel (liftObservable coarse)

    traceNaturality :
      ∀ coarseKernelValue →
      liftObservable (coarseTrace coarseKernelValue)
      ≡ fineTrace (liftKernel coarseKernelValue)

open TransferKernelTraceNaturality public

fineTransferFromKernelTrace :
  ∀ {Fine Coarse FineKernel CoarseKernel} →
  TransferKernelTraceNaturality Fine Coarse FineKernel CoarseKernel →
  Fine → Fine
fineTransferFromKernelTrace naturality fine =
  fineTrace naturality (fineKernel naturality fine)

coarseTransferFromKernelTrace :
  ∀ {Fine Coarse FineKernel CoarseKernel} →
  TransferKernelTraceNaturality Fine Coarse FineKernel CoarseKernel →
  Coarse → Coarse
coarseTransferFromKernelTrace naturality coarse =
  coarseTrace naturality (coarseKernel naturality coarse)

kernelTraceNaturalityImpliesTransferIntertwiner :
  ∀ {Fine Coarse FineKernel CoarseKernel} →
  TransferKernelTraceNaturality Fine Coarse FineKernel CoarseKernel →
  Transfer.TransferIntertwiner Fine Coarse
kernelTraceNaturalityImpliesTransferIntertwiner naturality = record
  { Transfer.TransferIntertwiner.liftObservable =
      liftObservable naturality
  ; Transfer.TransferIntertwiner.fineTransfer =
      fineTransferFromKernelTrace naturality
  ; Transfer.TransferIntertwiner.coarseTransfer =
      coarseTransferFromKernelTrace naturality
  ; Transfer.TransferIntertwiner.intertwines = λ coarse →
      trans
        (traceNaturality naturality (coarseKernel naturality coarse))
        (cong
          (fineTrace naturality)
          (kernelNaturality naturality coarse))
  }

kernelTraceDerivedIntertwiningEquation :
  ∀ {Fine Coarse FineKernel CoarseKernel}
    (naturality :
      TransferKernelTraceNaturality Fine Coarse FineKernel CoarseKernel)
    coarse →
  liftObservable naturality
    (coarseTransferFromKernelTrace naturality coarse)
  ≡ fineTransferFromKernelTrace naturality
      (liftObservable naturality coarse)
kernelTraceDerivedIntertwiningEquation naturality coarse =
  Transfer.intertwines
    (kernelTraceNaturalityImpliesTransferIntertwiner naturality)
    coarse

------------------------------------------------------------------------
-- Exact source-facing frontier classification.
------------------------------------------------------------------------

kernelTraceCompositionTheoremLevel : ProofLevel
kernelTraceCompositionTheoremLevel = machineChecked

spatialBalabanBlockPreservesTemporalBoundaryVariablesLevel : ProofLevel
spatialBalabanBlockPreservesTemporalBoundaryVariablesLevel = conditional

balabanBlockCommutesWithTemporalReflectionCutLevel : ProofLevel
balabanBlockCommutesWithTemporalReflectionCutLevel = conditional

largeFieldPolymerExpansionRespectsTransferSlabsLevel : ProofLevel
largeFieldPolymerExpansionRespectsTransferSlabsLevel = conditional

literalBalabanKernelNaturalityLevel : ProofLevel
literalBalabanKernelNaturalityLevel = conditional

balabanIntegrationCommutesWithTransferCompositionLevel : ProofLevel
balabanIntegrationCommutesWithTransferCompositionLevel = conditional
