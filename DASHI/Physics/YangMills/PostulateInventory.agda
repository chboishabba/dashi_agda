module DASHI.Physics.YangMills.PostulateInventory where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

open import DASHI.Geometry.Gauge.SUNPrimitives using (clayYangMillsPromoted)

-- ── PostulateInventory ───────────────────────────────────────────────
-- Complete inventory of all imported postulates, conventions, and source
-- claims consumed by the DASHI YM route.  This file is the canonical audit
-- surface for any external reviewer.
--
-- Every entry is a named import relative to a specific source paper and
-- theorem/proposition number.  Nothing here is a constructive proof
-- internal to DASHI.
--
-- Status: 33/33 entries populated.
--         clayYangMillsPromoted = false (authority/adjudication gate).
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
    p01 : Bool  -- treePathEdgesExist: every tree edge is a support edge
    p02 : Bool  -- graphDistMinimality: graph distance is minimal among support paths
    p03 : Bool  -- treePathBoundedByEdgeCount: tree-path length ≤ tree edge count

    -- κ / normalisation (Balaban CMP 95 Prop. 1.2; Eriksson 2602.0069 §3.1)
    p04 : Bool  -- kappaStrictlyPositive: κ > 0
    p05 : Bool  -- kappaNormalisedToOne: κ = 1 (DASHI A2 norm convention, Eriksson §12.1)

    -- Polymer entropy / counting (Eriksson 2602.0041 Lem. 5.6; CMP 122 eq. 1.89)
    p06 : Bool  -- ImportedPolymerAnimalCountingBound: # polymers ≤ C_d^n
    p07 : Bool  -- ImportedKPSummabilityBound: Σ_X∋b e^{-p₀} e^{-κ d_k(X)} < ∞
    p08 : Bool  -- pZeroPositive: p₀(g_k) > 0 for β ≥ β₀
    p09 : Bool  -- entropyBeatenByFullDecay: C_d·e^{-κ}·e^{-p₀_min} < 1

    -- Anisotropic subspace classification (Eriksson 2602.0087 Thm 3.6, unconditional)
    p20 : Bool  -- AnisotropicSubspaceClassificationTheorem: dim(O_{6,aniso}) = 1

    -- Lattice Ward identity (Eriksson 2602.0092 Prop 3.2, unconditional, Jacobian-free)
    p28 : Bool  -- ImportedRotationalWardIdentity: ⟨S^η_n, L_μν f⟩ lattice Ward identity

    -- Triangular mixing preventive lock (Eriksson 2602.0096 Thm 8.5+Cor 8.6, unconditional)
    p32 : Bool  -- TriangularMixingPreventiveLock: Z_{4←6} has no d=4 anisotropic sink

    -- Field regularity / uniform link ellipticity (Balaban/Eriksson small-field regularity)
    p33 : Bool  -- FieldRegularityImpliesSingleLinkPositivity: w_k(e) ≥ m_link ≥ 1

    -- Layer 1 — Conditional on Layer 0
    -- ─────────────────────────────────
    -- Large-field suppression (Eriksson 2602.0069 Thm 8.5; 2602.0056 §7)
    p10 : Bool  -- ImportedLargeFieldActivityBound: |R^(k)| ≤ exp(-p₀)·exp(-κ·d_k)
    p11 : Bool  -- ImportedAbsorptionCondition: c·p₀(gₖ) ≥ (d-1) log L + C_abs

    -- DLR-LSI branch (Eriksson 2602.0052 Lem. 6.3, Lem. 5.7, Thm 7.1, Cor 7.3)
    p12 : Bool  -- ImportedDLRLSIFromPolymerDecay: δₖ < αblk/4 via polymer decay + pZeroPositive
    p13 : Bool  -- ImportedCrossScaleBound: Σₖ Dₖ < ∞
    p14 : Bool  -- ImportedDLRLSITheorem: DLR-LSI → DS complete analyticity → exponential clustering
    p15 : Bool  -- ImportedLatticeSpectralGap: ∆_phys ≥ m(β, Nc, d) > 0 (lattice-level)

    -- Anisotropy coefficient bound (Eriksson 2602.0087 Thm 5.4)
    p21 : Bool  -- AnisotropyCoeffQuadraticBound: |c⁽ᵏ⁾_{6,aniso}| ≤ C aₖ²

    -- Terminal KP bound + assembly map (Eriksson 2602.0091 Thm 1.1+1.2, Thm 1.3)
    p23 : Bool  -- TerminalKPBoundVerified: KP criterion (H1)–(H3) verified
    p24 : Bool  -- AssemblyMapComplete: dependency graph 0092→0088/0087→0091→Wightman confirmed

    -- Symanzik breaking decomposition (Eriksson 2602.0092 Prop 3.4)
    p29 : Bool  -- ImportedSymanzikBreakingDecomposition: (δ_μν s_W) = g₀⁻²η²[λ_μν O_aniso + Q^{O(4)} + O(η²)]

    -- Layer 2 — Conditional on Layer 1
    -- ─────────────────────────────────
    -- RG-Cauchy branch (Eriksson 2602.0072 A2, Thm 1.3, Cor 5.1)
    p16 : Bool  -- ImportedAssumptionA2FromKPCertificate: per-link oscillation bound
    p17 : Bool  -- ImportedB6InfluenceBound: Efron-Stein influence seminorm closed
    p18 : Bool  -- ImportedRGCauchySummability: Σ_k δ_k < ∞ → blocked observable Cauchy convergence

    -- Coupling control (Eriksson 2602.0088 Prop 4.1)
    p19 : Bool  -- ImportedCouplingControlProof: g_k ≤ γ₀ uniform in k, Cauchy β-function bound

    -- Insertion integrability (Eriksson 2602.0087 Thm 6.6)
    p22 : Bool  -- InsertionIntegrabilityBound: I^η_{O_aniso}(f) ≤ C(f) < ∞ uniformly in η

    -- Fixed-η LSI / mass gap / thermodynamic limit (Eriksson 2602.0089 Thm A, B, C)
    p25 : Bool  -- UniformLSIFixedLattice: Ent(f²) ≤ (2/ρ̂) ℰ(f,f) with ρ̂ > 0 independent of L
    p26 : Bool  -- VolumeUniformMassGapFixedLattice: m₀ > 0 independent of L
    p27 : Bool  -- ThermodynamicLimitUnique: μ_L → μ_∞ unique, gap persists

    -- Layer 3 — Conditional on Layers 0–2
    -- ────────────────────────────────────
    -- Full O(4) Euclidean covariance (Eriksson 2602.0092 Thm 4.2+Cor 4.3)
    p30 : Bool  -- ImportedOS1EuclideanCovariance: L_μν S_n = 0 in S'(ℝ^{4n})

    -- Layer 4 — Terminal mathematical sink
    -- ────────────────────────────────────
    -- Wightman axioms + mass gap (Eriksson 2602.0092 Thm 1.1+§5)
    p31 : Bool  -- ImportedWightmanReconstructionWithMassGap: (H, U(Λ,a), Ω), ∆_phys > 0

    -- ── Equality proofs (all true) ──
    p01IsTrue : p01 ≡ true
    p02IsTrue : p02 ≡ true
    p03IsTrue : p03 ≡ true
    p04IsTrue : p04 ≡ true
    p05IsTrue : p05 ≡ true
    p06IsTrue : p06 ≡ true
    p07IsTrue : p07 ≡ true
    p08IsTrue : p08 ≡ true
    p09IsTrue : p09 ≡ true
    p10IsTrue : p10 ≡ true
    p11IsTrue : p11 ≡ true
    p12IsTrue : p12 ≡ true
    p13IsTrue : p13 ≡ true
    p14IsTrue : p14 ≡ true
    p15IsTrue : p15 ≡ true
    p16IsTrue : p16 ≡ true
    p17IsTrue : p17 ≡ true
    p18IsTrue : p18 ≡ true
    p19IsTrue : p19 ≡ true
    p20IsTrue : p20 ≡ true
    p21IsTrue : p21 ≡ true
    p22IsTrue : p22 ≡ true
    p23IsTrue : p23 ≡ true
    p24IsTrue : p24 ≡ true
    p25IsTrue : p25 ≡ true
    p26IsTrue : p26 ≡ true
    p27IsTrue : p27 ≡ true
    p28IsTrue : p28 ≡ true
    p29IsTrue : p29 ≡ true
    p30IsTrue : p30 ≡ true
    p31IsTrue : p31 ≡ true
    p32IsTrue : p32 ≡ true
    p33IsTrue : p33 ≡ true

    -- ── Sources (canonical audit string) ──
    sources : String
    sourcesIsCanonical :
      sources ≡
      "P01-P03 (Diestel: treePathEdgesExist, graphDistMinimality, treePathBoundedByEdgeCount); P04-P05 (kappa-normalisation: kappaStrictlyPositive CMP 95 Prop 1.2, kappaNormalisedToOne DASHI A2); P06-P09 (polymer entropy: ImportedPolymerAnimalCountingBound 2602.0041 Lem 5.6, ImportedKPSummabilityBound, pZeroPositive CMP 122 eq 1.89, entropyBeatenByFullDecay beta>=beta0); P10-P11 (large-field: ImportedLargeFieldActivityBound 2602.0069 Thm 8.5, ImportedAbsorptionCondition 2602.0056 sec7); P12-P15 (DLR-LSI: ImportedDLRLSIFromPolymerDecay 2602.0052 Lem 6.3, ImportedCrossScaleBound Lem 5.7, ImportedDLRLSITheorem Thm 7.1, ImportedLatticeSpectralGap Cor 7.3); P16-P18 (RG-Cauchy: ImportedAssumptionA2FromKPCertificate 2602.0072 A2, ImportedB6InfluenceBound Thm 1.3, ImportedRGCauchySummability Cor 5.1); P19 (coupling control: ImportedCouplingControlProof 2602.0088 Prop 4.1); P20 (anisotropic classification: AnisotropicSubspaceClassificationTheorem 2602.0087 Thm 3.6); P21 (coefficient bound: AnisotropyCoeffQuadraticBound 2602.0087 Thm 5.4); P22 (insertion integrability: InsertionIntegrabilityBound 2602.0087 Thm 6.6); P23-P24 (terminal KP + assembly: TerminalKPBoundVerified 2602.0091 Thm 1.1+1.2, AssemblyMapComplete Thm 1.3); P25-P27 (fixed-eta: UniformLSIFixedLattice 2602.0089 Thm A, VolumeUniformMassGapFixedLattice Thm B, ThermodynamicLimitUnique Thm C); P28 (Ward identity: ImportedRotationalWardIdentity 2602.0092 Prop 3.2); P29 (Symanzik: ImportedSymanzikBreakingDecomposition 2602.0092 Prop 3.4); P30 (OS1: ImportedOS1EuclideanCovariance 2602.0092 Thm 4.2+Cor 4.3); P31 (Wightman: ImportedWightmanReconstructionWithMassGap 2602.0092 Thm 1.1+sec5); P32 (triangular lock: TriangularMixingPreventiveLock 2602.0096 Thm 8.5+Cor 8.6); P33 (link ellipticity: FieldRegularityImpliesSingleLinkPositivity Balaban/Eriksson small-field regularity)"

    -- ── Clay promotion guard ──
    noClayPromotion : clayYangMillsPromoted ≡ false

currentPostulateInventory : PostulateInventory
currentPostulateInventory = record
  { p01 = true
  ; p02 = true
  ; p03 = true
  ; p04 = true
  ; p05 = true
  ; p06 = true
  ; p07 = true
  ; p08 = true
  ; p09 = true
  ; p10 = true
  ; p11 = true
  ; p12 = true
  ; p13 = true
  ; p14 = true
  ; p15 = true
  ; p16 = true
  ; p17 = true
  ; p18 = true
  ; p19 = true
  ; p20 = true
  ; p21 = true
  ; p22 = true
  ; p23 = true
  ; p24 = true
  ; p25 = true
  ; p26 = true
  ; p27 = true
  ; p28 = true
  ; p29 = true
  ; p30 = true
  ; p31 = true
  ; p32 = true
  ; p33 = true
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
  ; sources =
      "P01-P03 (Diestel: treePathEdgesExist, graphDistMinimality, treePathBoundedByEdgeCount); P04-P05 (kappa-normalisation: kappaStrictlyPositive CMP 95 Prop 1.2, kappaNormalisedToOne DASHI A2); P06-P09 (polymer entropy: ImportedPolymerAnimalCountingBound 2602.0041 Lem 5.6, ImportedKPSummabilityBound, pZeroPositive CMP 122 eq 1.89, entropyBeatenByFullDecay beta>=beta0); P10-P11 (large-field: ImportedLargeFieldActivityBound 2602.0069 Thm 8.5, ImportedAbsorptionCondition 2602.0056 sec7); P12-P15 (DLR-LSI: ImportedDLRLSIFromPolymerDecay 2602.0052 Lem 6.3, ImportedCrossScaleBound Lem 5.7, ImportedDLRLSITheorem Thm 7.1, ImportedLatticeSpectralGap Cor 7.3); P16-P18 (RG-Cauchy: ImportedAssumptionA2FromKPCertificate 2602.0072 A2, ImportedB6InfluenceBound Thm 1.3, ImportedRGCauchySummability Cor 5.1); P19 (coupling control: ImportedCouplingControlProof 2602.0088 Prop 4.1); P20 (anisotropic classification: AnisotropicSubspaceClassificationTheorem 2602.0087 Thm 3.6); P21 (coefficient bound: AnisotropyCoeffQuadraticBound 2602.0087 Thm 5.4); P22 (insertion integrability: InsertionIntegrabilityBound 2602.0087 Thm 6.6); P23-P24 (terminal KP + assembly: TerminalKPBoundVerified 2602.0091 Thm 1.1+1.2, AssemblyMapComplete Thm 1.3); P25-P27 (fixed-eta: UniformLSIFixedLattice 2602.0089 Thm A, VolumeUniformMassGapFixedLattice Thm B, ThermodynamicLimitUnique Thm C); P28 (Ward identity: ImportedRotationalWardIdentity 2602.0092 Prop 3.2); P29 (Symanzik: ImportedSymanzikBreakingDecomposition 2602.0092 Prop 3.4); P30 (OS1: ImportedOS1EuclideanCovariance 2602.0092 Thm 4.2+Cor 4.3); P31 (Wightman: ImportedWightmanReconstructionWithMassGap 2602.0092 Thm 1.1+sec5); P32 (triangular lock: TriangularMixingPreventiveLock 2602.0096 Thm 8.5+Cor 8.6); P33 (link ellipticity: FieldRegularityImpliesSingleLinkPositivity Balaban/Eriksson small-field regularity)"
  ; sourcesIsCanonical = refl
  ; noClayPromotion = refl
  }
