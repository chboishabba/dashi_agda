module DASHI.TextilePhysicsValidation where

open import DASHI.Physics.Textile.Everything
open import DASHI.Topology.TextileStitchHyperfabricExact

------------------------------------------------------------------------
-- Import-only validation surface for the textile physics tranche.
-- If this module typechecks, the canonical SI dimension owner, mechanical
-- fibre, Jacquard physical bridge, and neutral stitch topology all elaborate
-- together without creating a parallel units hierarchy.
------------------------------------------------------------------------
