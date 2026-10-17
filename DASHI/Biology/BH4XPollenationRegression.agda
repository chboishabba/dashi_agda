module DASHI.Biology.BH4XPollenationRegression where

open import DASHI.Core.Prelude

import DASHI.Core.XPollenationExact as X
import DASHI.Biology.BH4XPollenationKineticAdjudicationExact as BH4

------------------------------------------------------------------------
-- RED-first contract for the generic xPollenation ABI and BH4 consumer.
------------------------------------------------------------------------

qidAdjacencyDoesNotCreateSameObject :
  X.qidAdjacencyCreatesSameObject X.canonicalXPollenationBoundary ≡ false
qidAdjacencyDoesNotCreateSameObject = refl

cidDoesNotCreateSemanticIdentity :
  X.cidCreatesSemanticIdentity X.canonicalXPollenationBoundary ≡ false
cidDoesNotCreateSemanticIdentity = refl

da51DoesNotCreateExternalIdentity :
  X.da51CreatesExternalIdentity X.canonicalXPollenationBoundary ≡ false
da51DoesNotCreateExternalIdentity = refl

edgeDoesNotCreateProof :
  X.edgeCreatesProof X.canonicalXPollenationBoundary ≡ false
edgeDoesNotCreateProof = refl

edgeDoesNotCreatePayment :
  X.edgeCreatesConsumerPayment X.canonicalXPollenationBoundary ≡ false
edgeDoesNotCreatePayment = refl

bh4NeighbourhoodDoesNotCreateFlux :
  BH4.neighbourhoodCreatesFluxBound BH4.canonicalBH4XPollenationBoundary ≡ false
bh4NeighbourhoodDoesNotCreateFlux = refl

rheaDoesNotCollapseIsoforms :
  BH4.rheaReactionCollapsesIsoformContext BH4.canonicalBH4XPollenationBoundary ≡ false
rheaDoesNotCollapseIsoforms = refl

sabioDoesNotPayFlux :
  BH4.sabioAssociationCreatesFluxPayment BH4.canonicalBH4XPollenationBoundary ≡ false
sabioDoesNotPayFlux = refl

oeisDoesNotCreateBiochemicalIdentity :
  BH4.oeisMatchCreatesBiochemicalIdentity BH4.canonicalBH4XPollenationBoundary ≡ false
oeisDoesNotCreateBiochemicalIdentity = refl

allFiniteReactionsAddressed : BH4.finiteReactionNeighbourhoodCount ≡ 12
allFiniteReactionsAddressed = refl
