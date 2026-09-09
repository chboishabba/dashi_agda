module DASHI.TextilePhysicsValidation where

open import DASHI.Physics.Textile.Everything
open import DASHI.Topology.TextileStitchHyperfabricExact
open import DASHI.Topology.TextileStitchOperationalSemanticsExact
open import DASHI.Topology.CircularKnittingHelicalLoopBridgeExact
open import DASHI.Topology.CrochetHookMicroSemanticsExact

------------------------------------------------------------------------
-- Import-only validation surface for the textile physics tranche.
-- If this module typechecks, the canonical SI dimension owner, mechanical
-- fibre, conditional constitutive laws, local and finite-network equilibrium,
-- slip/failure predicates, Jacquard physical bridge, neutral stitch topology,
-- knit/crochet operational semantics, circular-knitting helical loop bridge,
-- generic crochet hook micro-semantics, and stitch physical bridge all
-- elaborate together without creating parallel unit or textile architectures.
------------------------------------------------------------------------
