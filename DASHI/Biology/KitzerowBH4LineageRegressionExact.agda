module DASHI.Biology.KitzerowBH4LineageRegressionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

import DASHI.Chemistry.AtomicMolecularReactionLineageHyperfabricExact as Lineage
import DASHI.Chemistry.ElectronBondTransportExact as Electron
import DASHI.Biology.AtomicMolecularBiologicalIncorporationHyperfabricExact as Bio
import DASHI.Biology.KitzerowBH4ReactionChemistryExact as ReactionChem
import DASHI.Biology.KitzerowBH4SynthesisRegenerationExact as Cycle
import DASHI.Biology.KitzerowBH4ReactionCascadeBridgeExact as CascadeBridge

------------------------------------------------------------------------
-- BH4 / redox lineage regression.
--
-- The same explicit BH4 species is produced/recycled and consumed by multiple
-- reactions.  Electron/redox carriers are retained independently.  This pays
-- the material/electronic lineage seam without promoting the unmeasured claim
-- that stress reallocates flux among AAAH/NOS/AGMO branches.
------------------------------------------------------------------------

nadphToNadpElectronLineage : Lineage.ElectronLineage
nadphToNadpElectronLineage =
  Lineage.electronLineage
    "BH4-redox-NADPH-electron-lineage"
    "NADPH donor pool"
    "BH4 synthesis / hydroxylase / NOS acceptor-side reaction coordinates"
    "reduced nicotinamide electronic state"
    "oxidized NADP+ electronic state"
    "hydride/electron-pair bookkeeping; exact wavefunction trajectory not asserted"
    "NADPH -> NADP+ reducing-equivalent transfer"
    "reaction-level source atlas / future quantitative redox assay"

nadhToNadElectronLineage : Lineage.ElectronLineage
nadhToNadElectronLineage =
  Lineage.electronLineage
    "BH4-recycle-NADH-electron-lineage"
    "NADH donor pool"
    "DHPR BH2 -> BH4 regeneration"
    "reduced nicotinamide electronic state"
    "oxidized NAD+ electronic state"
    "hydride/electron-pair bookkeeping; exact wavefunction trajectory not asserted"
    "NADH -> NAD+ reducing-equivalent transfer"
    "DHPR reaction identity / future quantitative redox assay"

sprElectronTransfer : Electron.ElectronTransferReceipt
sprElectronTransfer =
  Electron.electronTransferReceipt
    Cycle.sprReaction
    nadphToNadpElectronLineage
    Electron.hydrideTransfer
    4
    "two NADPH reducing-equivalent donors in the net SPR representation"
    "6-pyruvoyltetrahydropterin / BH4-forming reduction coordinate"
    "NADPH reduced state"
    "pterin reduction state"
    "SPR active-site/cofactor context"
    "net proton bookkeeping explicit in Cycle.sprReaction"
    "no external electrode reservoir asserted"
    "electron-equivalent bookkeeping retained separately from atom balance"
    "source-backed reaction identity; quantitative electron partition remains open"

dhprElectronTransfer : Electron.ElectronTransferReceipt
dhprElectronTransfer =
  Electron.electronTransferReceipt
    Cycle.dhprReaction
    nadhToNadElectronLineage
    Electron.hydrideTransfer
    2
    "NADH reducing-equivalent donor"
    "BH2 / BH4 regeneration coordinate"
    "NADH reduced state"
    "BH2 reduction state"
    "DHPR active-site context"
    "H+ appears explicitly in the net regeneration transition"
    "no external electrode reservoir asserted"
    "electron-equivalent bookkeeping retained separately from atom balance"
    "source-backed reaction identity; quantitative electron partition remains open"

canonicalBH4ElectronTransfers : List Electron.ElectronTransferReceipt
canonicalBH4ElectronTransfers = sprElectronTransfer ∷ dhprElectronTransfer ∷ []

record KitzerowBH4LineageRegression : Set where
  constructor kitzerowBH4LineageRegression
  field
    sharedSpeciesReference : String
    supplyAndRecycleReference : String
    consumerBranchReference : String
    electronTransfers : List Electron.ElectronTransferReceipt
    electronRedoxLineageRetained : Bool
    electronRedoxLineageRetainedIsTrue : electronRedoxLineageRetained ≡ true
    sameBH4SpeciesAcrossSupplyRecycleConsumers : Bool
    sameBH4SpeciesAcrossSupplyRecycleConsumersIsTrue :
      sameBH4SpeciesAcrossSupplyRecycleConsumers ≡ true
    sharedBH4SpeciesProvesFluxReallocation : Bool
    sharedBH4SpeciesProvesFluxReallocationIsFalse :
      sharedBH4SpeciesProvesFluxReallocation ≡ false
    formalElectronBookkeepingProvesMeasuredBranchFlux : Bool
    formalElectronBookkeepingProvesMeasuredBranchFluxIsFalse :
      formalElectronBookkeepingProvesMeasuredBranchFlux ≡ false
    reactionLineageProvesAutismCausation : Bool
    reactionLineageProvesAutismCausationIsFalse :
      reactionLineageProvesAutismCausation ≡ false
    quantitativeNextReceipt : String

open KitzerowBH4LineageRegression public

canonicalKitzerowBH4LineageRegression : KitzerowBH4LineageRegression
canonicalKitzerowBH4LineageRegression =
  kitzerowBH4LineageRegression
    "ReactionChem.bh4 is the shared literal 6R-BH4 species"
    "Cycle.canonicalBH4SupplyAndRecycleTransitions"
    "CascadeBridge AAAH/NOS/AGMO reaction-backed branches"
    canonicalBH4ElectronTransfers
    true refl
    true refl
    false refl
    false refl
    false refl
    "measure compartment-resolved BH4/BH2, NAD(P)H redox state and branch-specific flux J_AAAH/J_NOS/J_AGMO under controlled stress/redox perturbation; then re-audit allocation causality"
