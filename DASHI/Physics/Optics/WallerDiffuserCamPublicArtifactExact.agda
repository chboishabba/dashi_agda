module DASHI.Physics.Optics.WallerDiffuserCamPublicArtifactExact where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

-- Source-bounded receipt for the public Waller Lab DiffuserCam implementation.
-- This records artifact identity and published code semantics only.  Possession
-- of a PSF stack does not itself prove a restricted inverse theorem or a
-- matched-photon superiority claim.

wallerDiffuserCamRepository : String
wallerDiffuserCamRepository = "Waller-Lab/DiffuserCam"

wallerDiffuserCamPinnedCommit : String
wallerDiffuserCamPinnedCommit = "c8516cb8f482c2bb15e75ebebd91a74b88732c95"

publicPSFStackPath : String
publicPSFStackPath = "example_data/example_psfs.mat"

publicPSFStackGitBlobSHA1 : String
publicPSFStackGitBlobSHA1 = "db59065bdaf44fe771a6d3fbe22ae3c703527b5f"

publicPSFStackBytes : Nat
publicPSFStackBytes = 10823885

publicRawExposurePath : String
publicRawExposurePath = "example_data/example_raw.png"

publicRawExposureGitBlobSHA1 : String
publicRawExposureGitBlobSHA1 = "3b4c3b2ca674bbd21d925a1f0a1ea79a77efe5df"

publicRawExposureBytes : Nat
publicRawExposureBytes = 122698

record WallerDiffuserCamPublicArtifactReceipt : Set where
  field
    publicPSFStackPresent : Bool
    publicRawExposurePresent : Bool
    psfStackIsDepthIndexedCalibrationArtifact : Bool
    rawExposureIsUSAFExample : Bool
    exampleWasDownsampledBySource : Bool
    artifactAloneProvesGlobalInjectivity : Bool
    artifactAloneProvesMatchedPhotonAdvantage : Bool

open WallerDiffuserCamPublicArtifactReceipt public

wallerDiffuserCamPublicArtifactReceipt : WallerDiffuserCamPublicArtifactReceipt
wallerDiffuserCamPublicArtifactReceipt = record
  { publicPSFStackPresent = true
  ; publicRawExposurePresent = true
  ; psfStackIsDepthIndexedCalibrationArtifact = true
  ; rawExposureIsUSAFExample = true
  ; exampleWasDownsampledBySource = true
  ; artifactAloneProvesGlobalInjectivity = false
  ; artifactAloneProvesMatchedPhotonAdvantage = false
  }
