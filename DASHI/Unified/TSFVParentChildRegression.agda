{-# OPTIONS --safe #-}
module DASHI.Unified.TSFVParentChildRegression where

------------------------------------------------------------------------
-- S11 independent OWNERS, one kernel-checking root.
--
-- The original native Yang--Mills Golden regression root belongs to
-- #1444; the original TSVF/observer/Lorentz/KK/OS finite and conditional
-- weld belongs to #1460. Both are imported by this exact new root
-- WITHOUT re-exporting colliding unqualified names, changing the
-- original source definitions, or using the parent branch as a
-- surrogate for physical proof.
--
-- Importing both modules in Agda is a proper TRANSITIVE typecheck
-- dependency, not a source-text copy or a scientific existence claim.
------------------------------------------------------------------------

import DASHI.Unified.BalabanRGTOERegression as YMParent
import DASHI.Unified.TSFVUnifiedRegression as TSVFChild

-- The parent keeps full native YM/OS ownership. The child retains
-- only its separate original TSVF/KK/Stone same-source mathematics.
-- Neither import provides a physical inhabitant of the other's
-- conditional Hilbert/action/source hypotheses.
