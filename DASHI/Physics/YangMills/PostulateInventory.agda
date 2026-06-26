module DASHI.Physics.YangMills.PostulateInventory where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

open import DASHI.Geometry.Gauge.SUNPrimitives using (clayYangMillsPromoted)
open import DASHI.Physics.YangMills.ProofTargetSurface
import DASHI.Physics.YangMills.P01P33ProofSurfaces as Surfaces

-- ── PostulateInventory ───────────────────────────────────────────────
-- Complete inventory of all imported postulates, conventions, and source
-- claims consumed by the DASHI YM route.  This file is the canonical audit
-- surface for any external reviewer.
-- The replacement-priority table lives separately in:
--   DASHI.Physics.YangMills.P01P33ReplacementBacklog
-- The lightweight P33 split bridge lives in:
--   DASHI.Physics.YangMills.BalabanP33Bridge
--
-- Every entry is a named import relative to a specific source paper and
-- theorem/proposition number.  Nothing here is a constructive proof
-- internal to DASHI.
--
-- Status: 33/33 entries populated.
--         clayYangMillsPromoted = false (authority/adjudication gate).
-- Provenance split after the low-risk graph/arithmetic pass:
--   internal wrapper/proved: P01-P03, P07, P09, P33
--   paper-import remains on the direct source citations outside that lane.
--
-- Dependency layers (topological, per Eriksson 2602.0096 §2):
--   Layer 0 (unconditional): P01–P09, P20, P28, P32, P33
--   Layer 1 (← Layer 0):     P10–P11, P12–P15, P21, P23–P24, P29
--   Layer 2 (← Layer 1):     P16–P19, P22, P25–P27
--   Layer 3 (← Layers 0–2):  P30
--   Layer 4 (← Layer 3):     P31
--   Authority layer (external, not mathematical): qualifyingJournalPublication,
--     twoYearWaitingPeriodElapsed, globalMathematicsAcceptance

record PostulateInventory : Set where
  field
    -- Layer 0 — Unconditional structural postulates
    -- ────────────────────────────────────────────────
    -- Finite graph (Diestel, YMSupportGraphDistance / BalabanTreeDistanceDiameterCompatibility)
    -- Closed internally by the graph-path / diameter wrappers and proofs.
    p01 : ProofTargetSurface
    p02 : ProofTargetSurface
    p03 : ProofTargetSurface

    -- κ / normalisation (Balaban CMP 95 Prop. 1.2; Eriksson 2602.0069 §3.1)
    p04 : ProofTargetSurface
    p05 : ProofTargetSurface

    -- Polymer entropy / counting (Eriksson 2602.0041 Lem. 5.6; CMP 122 eq. 1.89)
    -- P07/P09 are now internal arithmetic closures; P06/P08 remain paper imports.
    p06 : ProofTargetSurface
    p07 : ProofTargetSurface
    p08 : ProofTargetSurface
    p09 : ProofTargetSurface

    -- Anisotropic subspace classification (Eriksson 2602.0087 Thm 3.6, unconditional)
    p20 : ProofTargetSurface

    -- Lattice Ward identity (Eriksson 2602.0092 Prop 3.2, unconditional, Jacobian-free)
    p28 : ProofTargetSurface

    -- Triangular mixing preventive lock (Eriksson 2602.0096 Thm 8.5+Cor 8.6, unconditional)
    p32 : ProofTargetSurface

    -- Field regularity / uniform link ellipticity.
    -- Composite surface: source ellipticity + internal diameter domination.
    p33 : ProofTargetSurface

    -- Layer 1 — Conditional on Layer 0
    -- ─────────────────────────────────
    -- Large-field suppression (Eriksson 2602.0069 Thm 8.5; 2602.0056 §7)
    p10 : ProofTargetSurface
    p11 : ProofTargetSurface

    -- DLR-LSI branch (Eriksson 2602.0052 Lem. 6.3, Lem. 5.7, Thm 7.1, Cor 7.3)
    p12 : ProofTargetSurface
    p13 : ProofTargetSurface
    p14 : ProofTargetSurface
    p15 : ProofTargetSurface

    -- Anisotropy coefficient bound (Eriksson 2602.0087 Thm 5.4)
    p21 : ProofTargetSurface

    -- Terminal KP bound + assembly map (Eriksson 2602.0091 Thm 1.1+1.2, Thm 1.3)
    p23 : ProofTargetSurface
    p24 : ProofTargetSurface

    -- Symanzik breaking decomposition (Eriksson 2602.0092 Prop 3.4)
    p29 : ProofTargetSurface

    -- Layer 2 — Conditional on Layer 1
    -- ─────────────────────────────────
    -- RG-Cauchy branch (Eriksson 2602.0072 A2, Thm 1.3, Cor 5.1)
    p16 : ProofTargetSurface
    p17 : ProofTargetSurface
    p18 : ProofTargetSurface

    -- Coupling control (Eriksson 2602.0088 Prop 4.1)
    p19 : ProofTargetSurface

    -- Insertion integrability (Eriksson 2602.0087 Thm 6.6)
    p22 : ProofTargetSurface

    -- Fixed-η LSI / mass gap / thermodynamic limit (Eriksson 2602.0089 Thm A, B, C)
    p25 : ProofTargetSurface
    p26 : ProofTargetSurface
    p27 : ProofTargetSurface

    -- Layer 3 — Conditional on Layers 0–2
    -- ────────────────────────────────────
    -- Full O(4) Euclidean covariance (Eriksson 2602.0092 Thm 4.2+Cor 4.3)
    p30 : ProofTargetSurface

    -- Layer 4 — Terminal mathematical sink
    -- ────────────────────────────────────
    -- Wightman axioms + mass gap (Eriksson 2602.0092 Thm 1.1+§5)
    p31 : ProofTargetSurface

    -- ── Equality proofs (all true) ──
    p01IsTrue : proofTargetIsClosed p01 ≡ true
    p02IsTrue : proofTargetIsClosed p02 ≡ true
    p03IsTrue : proofTargetIsClosed p03 ≡ true
    p04IsTrue : proofTargetIsClosed p04 ≡ true
    p05IsTrue : proofTargetIsClosed p05 ≡ true
    p06IsTrue : proofTargetIsClosed p06 ≡ true
    p07IsTrue : proofTargetIsClosed p07 ≡ true
    p08IsTrue : proofTargetIsClosed p08 ≡ true
    p09IsTrue : proofTargetIsClosed p09 ≡ true
    p10IsTrue : proofTargetIsClosed p10 ≡ true
    p11IsTrue : proofTargetIsClosed p11 ≡ true
    p12IsTrue : proofTargetIsClosed p12 ≡ true
    p13IsTrue : proofTargetIsClosed p13 ≡ true
    p14IsTrue : proofTargetIsClosed p14 ≡ true
    p15IsTrue : proofTargetIsClosed p15 ≡ true
    p16IsTrue : proofTargetIsClosed p16 ≡ true
    p17IsTrue : proofTargetIsClosed p17 ≡ true
    p18IsTrue : proofTargetIsClosed p18 ≡ true
    p19IsTrue : proofTargetIsClosed p19 ≡ true
    p20IsTrue : proofTargetIsClosed p20 ≡ true
    p21IsTrue : proofTargetIsClosed p21 ≡ true
    p22IsTrue : proofTargetIsClosed p22 ≡ true
    p23IsTrue : proofTargetIsClosed p23 ≡ true
    p24IsTrue : proofTargetIsClosed p24 ≡ true
    p25IsTrue : proofTargetIsClosed p25 ≡ true
    p26IsTrue : proofTargetIsClosed p26 ≡ true
    p27IsTrue : proofTargetIsClosed p27 ≡ true
    p28IsTrue : proofTargetIsClosed p28 ≡ true
    p29IsTrue : proofTargetIsClosed p29 ≡ true
    p30IsTrue : proofTargetIsClosed p30 ≡ true
    p31IsTrue : proofTargetIsClosed p31 ≡ true
    p32IsTrue : proofTargetIsClosed p32 ≡ true
    p33IsTrue : proofTargetIsClosed p33 ≡ true

    inventoryBoundary : String
    inventoryBoundaryIsCanonical :
      inventoryBoundary ≡
      "P01-P33 inventory stores theorem surfaces, not bare booleans. Each entry records source, statement, assumptions, output conclusion, consuming gate, failure consequence, and closure status."

    -- ── Clay promotion guard ──
    noClayPromotion : clayYangMillsPromoted ≡ false

currentPostulateInventory : PostulateInventory
currentPostulateInventory = record
  { p01 = Surfaces.treePathEdgesExistSurface
  ; p02 = Surfaces.graphDistMinimalitySurface
  ; p03 = Surfaces.treePathBoundedByEdgeCountSurface
  ; p04 = Surfaces.kappaStrictlyPositiveSurface
  ; p05 = Surfaces.kappaNormalisedToOneSurface
  ; p06 = Surfaces.polymerAnimalCountingBoundSurface
  ; p07 = Surfaces.kPSummabilityBoundSurface
  ; p08 = Surfaces.pZeroPositiveSurface
  ; p09 = Surfaces.entropyBeatenByFullDecaySurface
  ; p10 = Surfaces.largeFieldActivityBoundSurface
  ; p11 = Surfaces.absorptionConditionSurface
  ; p12 = Surfaces.dLRLSIFromPolymerDecaySurface
  ; p13 = Surfaces.crossScaleBoundSurface
  ; p14 = Surfaces.dLRLSITheoremSurface
  ; p15 = Surfaces.latticeSpectralGapSurface
  ; p16 = Surfaces.assumptionA2FromKPCertificateSurface
  ; p17 = Surfaces.b6InfluenceBoundSurface
  ; p18 = Surfaces.rGCauchySummabilitySurface
  ; p19 = Surfaces.couplingControlSurface
  ; p20 = Surfaces.anisotropicSubspaceClassificationSurface
  ; p21 = Surfaces.anisotropyCoeffQuadraticBoundSurface
  ; p22 = Surfaces.insertionIntegrabilityBoundSurface
  ; p23 = Surfaces.terminalKPBoundVerifiedSurface
  ; p24 = Surfaces.assemblyMapCompleteSurface
  ; p25 = Surfaces.uniformLSIFixedLatticeSurface
  ; p26 = Surfaces.volumeUniformMassGapFixedLatticeSurface
  ; p27 = Surfaces.thermodynamicLimitUniqueSurface
  ; p28 = Surfaces.rotationalWardIdentitySurface
  ; p29 = Surfaces.symanzikBreakingDecompositionSurface
  ; p30 = Surfaces.oS1EuclideanCovarianceSurface
  ; p31 = Surfaces.wightmanReconstructionWithMassGapSurface
  ; p32 = Surfaces.triangularMixingPreventiveLockSurface
  ; p33 = Surfaces.fieldRegularityImpliesSingleLinkPositivitySurface
  ; p01IsTrue = refl
  ; p02IsTrue = refl
  ; p03IsTrue = refl
  ; p04IsTrue = refl
  ; p05IsTrue = refl
  ; p06IsTrue = refl
  ; p07IsTrue = refl
  ; p08IsTrue = refl
  ; p09IsTrue = refl
  ; p10IsTrue = refl
  ; p11IsTrue = refl
  ; p12IsTrue = refl
  ; p13IsTrue = refl
  ; p14IsTrue = refl
  ; p15IsTrue = refl
  ; p16IsTrue = refl
  ; p17IsTrue = refl
  ; p18IsTrue = refl
  ; p19IsTrue = refl
  ; p20IsTrue = refl
  ; p21IsTrue = refl
  ; p22IsTrue = refl
  ; p23IsTrue = refl
  ; p24IsTrue = refl
  ; p25IsTrue = refl
  ; p26IsTrue = refl
  ; p27IsTrue = refl
  ; p28IsTrue = refl
  ; p29IsTrue = refl
  ; p30IsTrue = refl
  ; p31IsTrue = refl
  ; p32IsTrue = refl
  ; p33IsTrue = refl
  ; inventoryBoundary =
      "P01-P33 inventory stores theorem surfaces, not bare booleans. Each entry records source, statement, assumptions, output conclusion, consuming gate, failure consequence, and closure status."
  ; inventoryBoundaryIsCanonical = refl
  ; noClayPromotion = refl
  }
