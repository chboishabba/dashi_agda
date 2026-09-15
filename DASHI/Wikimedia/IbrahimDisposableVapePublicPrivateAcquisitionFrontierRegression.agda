module DASHI.Wikimedia.IbrahimDisposableVapePublicPrivateAcquisitionFrontierRegression where

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.String using (String)

record AcquisitionFrontierRegression : Set where
  constructor acquisition-frontier-regression
  field
    sameDeviceGateRequired : Bool
    puffResolvedGateRequired : Bool
    aerosolGateRequired : Bool
    broadNonTargetGateRequired : Bool
    publicVsPrivateStatusRequired : Bool
    nearMissesRetainedRequired : Bool
    notLocatedNotSameAsNotPerformed : Bool
    acquisitionTarget : String
open AcquisitionFrontierRegression public

requiredAcquisitionFrontierRegression : AcquisitionFrontierRegression
requiredAcquisitionFrontierRegression = acquisition-frontier-regression
  true true true true true true true
  "same-device puff-resolved disposable aerosol broad-organic non-target dataset"
