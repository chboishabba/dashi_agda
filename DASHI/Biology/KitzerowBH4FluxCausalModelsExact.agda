module DASHI.Biology.KitzerowBH4FluxCausalModelsExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

import DASHI.Biology.KitzerowBH4SynthesisRegenerationExact as Cycle
import DASHI.Biology.KitzerowBH4ReactionCascadeBridgeExact as Bridge
import DASHI.Biology.KitzerowBH4LineageRegressionExact as Lineage

------------------------------------------------------------------------
-- Symbolic flux layer.  These are typed coordinates and conservation roles;
-- they are not fabricated numerical kinetic parameters.
------------------------------------------------------------------------

data FluxRole : Set where
  synthesisFlux : FluxRole
  recycleFlux : FluxRole
  pahFlux : FluxRole
  thFlux : FluxRole
  tphFlux : FluxRole
  nosFlux : FluxRole
  agmoFlux : FluxRole
  otherSinkFlux : FluxRole

record FluxCoordinate : Set where
  constructor fluxCoordinate
  field
    key : String
    role : FluxRole
    reactionReference : String
    compartmentReference : String
    measurementReference : String
    numericCalibrationReference : String

open FluxCoordinate public

jSynth jRecycle jPAH jTH jTPH jNOS jAGMO jOther : FluxCoordinate
jSynth = fluxCoordinate "J_synth" synthesisFlux "GCH1/PTPS/SPR de-novo supply" "cell-type compartment required" "BH4 production flux assay required" "unpaid"
jRecycle = fluxCoordinate "J_recycle" recycleFlux "PCD/DHPR recycling" "cell-type compartment required" "BH2->BH4 isotope/redox flux assay required" "unpaid"
jPAH = fluxCoordinate "J_PAH" pahFlux "PAH hydroxylation" "liver/cell context required" "phenylalanine->tyrosine flux assay required" "unpaid"
jTH = fluxCoordinate "J_TH" thFlux "TH hydroxylation" "catecholaminergic cell context required" "tyrosine->L-DOPA flux assay required" "unpaid"
jTPH = fluxCoordinate "J_TPH" tphFlux "TPH hydroxylation" "serotonergic/peripheral cell context required" "tryptophan->5-HTP flux assay required" "unpaid"
jNOS = fluxCoordinate "J_NOS" nosFlux "NOS coupled/uncoupled branch" "NOS isoform/cell context required" "NO/superoxide plus isotope/redox flux assay required" "unpaid"
jAGMO = fluxCoordinate "J_AGMO" agmoFlux "AGMO ether-lipid cleavage" "membrane/cell context required" "ether-lipid turnover flux assay required" "unpaid"
jOther = fluxCoordinate "J_other" otherSinkFlux "other BH4 loss/turnover sinks" "compartment required" "total pool residual assay required" "unpaid"

canonicalBH4FluxCoordinates : List FluxCoordinate
canonicalBH4FluxCoordinates =
  jSynth ∷ jRecycle ∷ jPAH ∷ jTH ∷ jTPH ∷ jNOS ∷ jAGMO ∷ jOther ∷ []

record BH4PoolBalance : Set where
  constructor bh4PoolBalance
  field
    stateVariableReference : String
    symbolicBalance : String
    sourceTermsReference : String
    sinkTermsReference : String
    concentrationCalibrationReference : String
    timeSeriesReference : String
    massBalanceStructureExplicit : Bool
    massBalanceStructureExplicitIsTrue : massBalanceStructureExplicit ≡ true
    numericFluxesMeasured : Bool
    numericFluxesMeasuredIsFalse : numericFluxesMeasured ≡ false

open BH4PoolBalance public

canonicalBH4PoolBalance : BH4PoolBalance
canonicalBH4PoolBalance = bh4PoolBalance
  "compartment-resolved [BH4](t) with BH2/qBH2/redox context"
  "d[BH4]/dt = J_synth + J_recycle - J_PAH - J_TH - J_TPH - J_NOS - J_AGMO - J_other"
  "Cycle GCH1/PTPS/SPR and PCD/DHPR owners"
  "Bridge AAAH/NOS/AGMO consumers plus explicitly retained other sink"
  "unpaid: measured BH4/BH2 concentration by compartment/cell type"
  "unpaid: longitudinal perturbation-resolved pool/flux measurements"
  true refl false refl

------------------------------------------------------------------------
-- Competing causal architectures.
------------------------------------------------------------------------

data BH4CausalArchitecture : Set where
  upstreamAllocator : BH4CausalArchitecture
  downstreamConsequence : BH4CausalArchitecture
  parallelRedoxMarker : BH4CausalArchitecture
  contextSpecificSubgroup : BH4CausalArchitecture

record CausalModelReceipt : Set where
  constructor causalModelReceipt
  field
    architecture : BH4CausalArchitecture
    modelKey : String
    upstreamDriverReference : String
    bh4RoleReference : String
    branchPredictionReference : String
    timingPredictionReference : String
    rescuePredictionReference : String
    separatingExperimentReference : String
    currentlyEstablished : Bool

open CausalModelReceipt public

h1Allocator h2Downstream h3Parallel h4Context : CausalModelReceipt
h1Allocator = causalModelReceipt upstreamAllocator "H1 upstream BH4 allocator"
  "chronic allostatic/redox demand changes BH4 synthesis/recycle availability"
  "BH4 is a shared limiting/allocating state affecting multiple consumer fluxes"
  "controlled BH4/redox perturbation causes coordinated branch-specific flux redistribution"
  "BH4/redox changes precede predicted downstream branch changes"
  "restoring BH4 supply/recycling should reverse mediated branch effects when context permits"
  "joint perturbation + isotope/flux readout across AAAH/NOS/AGMO"
  false
h2Downstream = causalModelReceipt downstreamConsequence "H2 BH4 downstream consequence"
  "genotype/circuit/inflammatory mechanisms alter metabolism first"
  "BH4 changes are downstream consequences rather than common allocator"
  "upstream disease perturbation changes branches without BH4 mediation"
  "branch/pathology change precedes BH4 pool change"
  "BH4 restoration does not generally normalize upstream causal state"
  "intervene on BH4 while independently holding upstream disease driver"
  false
h3Parallel = causalModelReceipt parallelRedoxMarker "H3 parallel redox marker"
  "common oxidative/redox stress drives BH4 and downstream branches in parallel"
  "BH4 tracks redox state but does not mediate most branch covariance"
  "BH4 and branch signals co-move under stress but selective BH4 perturbation weakly changes branch flux"
  "shared redox driver can precede both"
  "redox normalization changes both even when direct BH4 manipulation does not"
  "orthogonal BH4 versus redox-factorial perturbation"
  false
h4Context = causalModelReceipt contextSpecificSubgroup "H4 context-specific BH4 mechanism"
  "BH4 mediation exists only in selected genotype/development/sex/cell/region contexts"
  "BH4 is causal in a bounded subgroup rather than universal upstream mechanism"
  "strong mediated effects in stratified contexts and weak/null effects elsewhere"
  "timing depends on developmental/cell context"
  "rescue works only in mechanism-positive strata"
  "pre-specified stratified perturbation with interaction tests"
  false

canonicalBH4CausalModels : List CausalModelReceipt
canonicalBH4CausalModels = h1Allocator ∷ h2Downstream ∷ h3Parallel ∷ h4Context ∷ []

record BH4FluxModel : Set where
  constructor bh4FluxModel
  field
    poolBalance : BH4PoolBalance
    fluxCoordinates : List FluxCoordinate
    causalModels : List CausalModelReceipt
    numericBranchFluxCalibrated : Bool
    numericBranchFluxCalibratedIsFalse : numericBranchFluxCalibrated ≡ false
    competingArchitecturesExplicit : Bool
    competingArchitecturesExplicitIsTrue : competingArchitecturesExplicit ≡ true
    symbolicMassBalanceProvesAllocatorModel : Bool
    symbolicMassBalanceProvesAllocatorModelIsFalse : symbolicMassBalanceProvesAllocatorModel ≡ false
    wholeAutismModelPromoted : Bool
    wholeAutismModelPromotedIsFalse : wholeAutismModelPromoted ≡ false

open BH4FluxModel public

canonicalBH4FluxModel : BH4FluxModel
canonicalBH4FluxModel = bh4FluxModel
  canonicalBH4PoolBalance canonicalBH4FluxCoordinates canonicalBH4CausalModels
  false refl true refl false refl false refl
