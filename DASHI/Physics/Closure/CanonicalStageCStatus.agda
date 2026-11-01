module DASHI.Physics.Closure.CanonicalStageCStatus where

data ClosureSurfaceStatus : Set where
  canonicalProved : ClosureSurfaceStatus
  compatibilityOnly : ClosureSurfaceStatus
  prototypeOnly : ClosureSurfaceStatus

