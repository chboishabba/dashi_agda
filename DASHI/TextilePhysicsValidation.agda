module DASHI.TextilePhysicsValidation where

open import DASHI.Physics.Textile.Everything
open import DASHI.Topology.TextileStitchHyperfabricExact
open import DASHI.Topology.TextileStitchOperationalSemanticsExact

------------------------------------------------------------------------
-- Import-only validation surface for the textile physics tranche.
-- If this module typechecks, the canonical SI dimension owner, mechanical
-- fibre, Jacquard physical bridge, neutral stitch topology, knit/crochet
-- operational semantics, and stitch physical bridge all elaborate together
-- without creating parallel unit or textile architectures.
------------------------------------------------------------------------
