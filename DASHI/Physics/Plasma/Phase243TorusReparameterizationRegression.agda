module DASHI.Physics.Plasma.Phase243TorusReparameterizationRegression where

open import DASHI.Core.Prelude

import DASHI.Physics.Plasma.PhaseRook270Exact as Rook
import DASHI.Physics.Plasma.Phase243TorusReparameterizationExact as Torus

allCoreStatesAdvanceByCanonicalTorusPullback :
  (x : Rook.Core243) →
  Torus.pullbackCoreByCanonicalAdvance x ≡ Rook.advanceCore x
allCoreStatesAdvanceByCanonicalTorusPullback =
  Torus.canonicalAdvancePullbackIntertwines

allCoreStatesInvertByTorusReflection :
  (x : Rook.Core243) →
  Torus.reflectCore x ≡ Rook.inverseCore x
allCoreStatesInvertByTorusReflection =
  Torus.reflectionIntertwines
