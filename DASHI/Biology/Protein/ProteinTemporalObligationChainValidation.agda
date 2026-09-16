module DASHI.Biology.Protein.ProteinTemporalObligationChainValidation where

-- RED-first validation root for the parent-level protein temporal chain.
-- The production owner must reuse the existing translation, conformation,
-- function, cell-state and open-metabolism surfaces rather than replacing them.

import DASHI.Biology.Protein.TranslationContext
import DASHI.Biology.Protein.ProteinConformationAttractor
import DASHI.Biology.Protein.ProteinFunctionProjection
import DASHI.Biology.Protein.ProteinRecoveryBoundary
import DASHI.Biology.Protein.ProteinSituatedHyperfabricExact
import DASHI.Biology.Cell.OpenMetabolicNetwork
import DASHI.Biology.Cell.CellStateAttractor

import DASHI.Biology.Protein.ProteinTemporalObligationChainExact as Chain

-- Pin the intended generic surface and the fail-closed boundary.
chainSurface : Set₁
chainSurface = Chain.ProteinTemporalObligationChain

obligationSurface : Set₁
obligationSurface = Chain.ProteinTemporalObligations

boundarySurface : Chain.ProteinTemporalObligationBoundary
boundarySurface = Chain.canonicalProteinTemporalObligationBoundary

-- The chain is deliberately obligation-bearing rather than a deterministic
-- biology pipeline.  These negative surfaces must remain exposed.
genomeDoesNotDetermineExpression = Chain.genomeDoesNotDetermineExpressedProtein
substrateDoesNotDetermineFlux = Chain.substrateDoesNotDetermineFlux
conformationDoesNotDetermineFunction = Chain.conformationDoesNotDetermineFunction
visibleStateDoesNotDetermineHistory = Chain.visibleStateDoesNotDetermineHistory

-- Reuse receipts: the generic owner points at the established domain carriers.
translationReuse : Set₁
translationReuse = Chain.translationContextSurface

conformationReuse : Set₁
conformationReuse = Chain.conformationSystemSurface

functionReuse : Set₁
functionReuse = Chain.functionSystemSurface

metabolismReuse : Set₁
metabolismReuse = Chain.metabolismSurface

cellReuse : Set₁
cellReuse = Chain.cellStateSurface
