module DASHI.Physics.YangMills.BalabanClayGate4PeriodicTraversalGeometryReuseExact where

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using ([]; _∷_)

open import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier using (pair)
open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanClayT2PeriodicTraversalDecoderExact as Decoder
import DASHI.Physics.YangMills.BalabanClayGate4PeriodicCoordinateClosureExact as Geometry

------------------------------------------------------------------------
-- Repository-specific finite geometry.  The conventional link reversal is
-- standard; the actual proof below reuses DASHI's exact cyclic-coordinate laws.
--
-- Michael Creutz, "Quarks, Gluons and Lattices", Cambridge University Press,
-- open-access reissue (2022). DOI: 10.1017/9781009290395.
------------------------------------------------------------------------

periodicDirectionInverseLaw : ∀ n → Decoder.DirectionInverseLaw n
periodicDirectionInverseLaw n = record
  { forwardThenReverse =
      λ { block (pair axis true) →
            Geometry.negativeAfterPositiveBlock block axis
        ; block (pair axis false) →
            Geometry.positiveAfterNegativeBlock block axis
        }
  }

periodicSingleEdgeReturns :
  ∀ {n} block direction →
  Decoder.replayTerminal block
    (direction ∷ Decoder.reverseDirection direction ∷ [])
  ≡ block
periodicSingleEdgeReturns {n} =
  Decoder.singleEdgeReturns (periodicDirectionInverseLaw n)

periodicTraversalDirectionInverseLevel : ProofLevel
periodicTraversalDirectionInverseLevel = machineChecked

periodicSingleEdgeReturnLevel : ProofLevel
periodicSingleEdgeReturnLevel = machineChecked
