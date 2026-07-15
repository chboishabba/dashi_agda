module DASHI.Physics.YangMills.P06ExactEnumerationIntegration where

------------------------------------------------------------------------
-- Focused integration surface for the preferred P06 finite-enumeration
-- theorem.  This intentionally avoids DASHI/Everything.agda and the wider
-- YM receipt graph: it checks the complete owned exact-DFS import path.
------------------------------------------------------------------------

open import DASHI.Physics.YangMills.P06ExactEnumerationEndpoint public
open import DASHI.Physics.YangMills.P06ActiveConsumerMigration public
