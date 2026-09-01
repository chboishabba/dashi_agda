module DASHI.Interop.ContextualFractranPNFHyperfabric369Exact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)

import DASHI.Interop.PNFHyperfabric369 as PNF369
import DASHI.Cognition.PNF.ContextualFractranOccurrenceHyperfabricExact as Context
import DASHI.Cognition.PNF.ContextualFractran369RefinementExact as Refinement
import DASHI.Cognition.PNF.SelfIndexedSemanticFractranTetrationBidiExact as Tetration

------------------------------------------------------------------------
-- Reuse the existing PNF/369 carrier as the address/encoding surface while the
-- contextual FRACTRAN layer supplies world-relative fine valuations beneath it.
-- This does not identify PNF, dialectic, tri-truth, prime or Monster axes.
------------------------------------------------------------------------

record ContextualPNF369Surface : Set₁ where
  constructor contextualPNF369Surface
  field
    canonicalPNFSurface : PNF369.PNFHyperfabric369Surface
    documentState : Context.DocumentFractranState
    refinementNeed : Refinement.SemanticRefinementNeed

open ContextualPNF369Surface public

record ContextualPNF369Boundary : Set where
  constructor contextualPNF369Boundary
  field
    PNFAndPrimeAxesRemainDistinct : Bool
    documentTimeAxisCanIndexContextualTransport : Bool
    coarse369AddressDeterminesFineWorld : Bool
    selfIndexingTetrationIsOrdinaryPNFProductGrowth : Bool
    primeCarrierLabelPromotesMonsterTheorem : Bool

canonicalContextualPNF369Boundary : ContextualPNF369Boundary
canonicalContextualPNF369Boundary =
  contextualPNF369Boundary true true false false false
