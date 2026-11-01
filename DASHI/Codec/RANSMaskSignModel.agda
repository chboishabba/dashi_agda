module DASHI.Codec.RANSMaskSignModel where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_)

open import DASHI.Codec.TriadicMaskSign using
  ( Mask3
  ; Sign
  ; mask3
  ; off
  ; on
  ; minus
  ; plus
  )

------------------------------------------------------------------------
-- This module is a finite model/interface boundary, not a theorem that a
-- particular implementation attains entropy or wall-clock performance.
------------------------------------------------------------------------

ScaleBits : Nat
ScaleBits = 12

TotalFrequency : Nat
TotalFrequency = 4096

record MaskFrequencyTable : Set where
  constructor maskFrequencyTable
  field
    f000 f001 f010 f100 f011 f101 f110 f111 : Nat

open MaskFrequencyTable public

maskFrequency : MaskFrequencyTable → Mask3 → Nat
maskFrequency t (mask3 off off off) = f000 t
maskFrequency t (mask3 off off on)  = f001 t
maskFrequency t (mask3 off on  off) = f010 t
maskFrequency t (mask3 on  off off) = f100 t
maskFrequency t (mask3 off on  on)  = f011 t
maskFrequency t (mask3 on  off on)  = f101 t
maskFrequency t (mask3 on  on  off) = f110 t
maskFrequency t (mask3 on  on  on)  = f111 t

maskFrequencyTotal : MaskFrequencyTable → Nat
maskFrequencyTotal t =
  f000 t + f001 t + f010 t + f100 t +
  f011 t + f101 t + f110 t + f111 t

-- Sparse cold-start table discussed in the codec formalism.
-- Symbol order: 000, 001, 010, 100, 011, 101, 110, 111.
sparseMaskFrequency : MaskFrequencyTable
sparseMaskFrequency = maskFrequencyTable 2610 431 431 431 61 61 61 10

sparseMaskFrequency-normalized :
  maskFrequencyTotal sparseMaskFrequency ≡ TotalFrequency
sparseMaskFrequency-normalized = refl

record MaskCDF : Set where
  constructor maskCDF
  field
    c0 c1 c2 c3 c4 c5 c6 c7 c8 : Nat

open MaskCDF public

sparseMaskCDF : MaskCDF
sparseMaskCDF = maskCDF 0 2610 3041 3472 3903 3964 4025 4086 4096

sparseMaskCDF-startsAtZero : c0 sparseMaskCDF ≡ 0
sparseMaskCDF-startsAtZero = refl

sparseMaskCDF-endsAtTotal : c8 sparseMaskCDF ≡ TotalFrequency
sparseMaskCDF-endsAtTotal = refl

record SignFrequencyTable : Set where
  constructor signFrequencyTable
  field
    fMinus fPlus : Nat

open SignFrequencyTable public

signFrequency : SignFrequencyTable → Sign → Nat
signFrequency t minus = fMinus t
signFrequency t plus  = fPlus t

signFrequencyTotal : SignFrequencyTable → Nat
signFrequencyTotal t = fMinus t + fPlus t

balancedSignFrequency : SignFrequencyTable
balancedSignFrequency = signFrequencyTable 2048 2048

balancedSignFrequency-normalized :
  signFrequencyTotal balancedSignFrequency ≡ TotalFrequency
balancedSignFrequency-normalized = refl

record SignCDF : Set where
  constructor signCDF
  field
    s0 s1 s2 : Nat

open SignCDF public

balancedSignCDF : SignCDF
balancedSignCDF = signCDF 0 2048 4096

balancedSignCDF-startsAtZero : s0 balancedSignCDF ≡ 0
balancedSignCDF-startsAtZero = refl

balancedSignCDF-endsAtTotal : s2 balancedSignCDF ≡ TotalFrequency
balancedSignCDF-endsAtTotal = refl

------------------------------------------------------------------------
-- Production contract.
------------------------------------------------------------------------

record RANSModelContract : Set where
  field
    maskTable       : MaskFrequencyTable
    signTable       : SignFrequencyTable
    maskNormalized  : maskFrequencyTotal maskTable ≡ TotalFrequency
    signNormalized  : signFrequencyTotal signTable ≡ TotalFrequency

coldStartModel : RANSModelContract
coldStartModel = record
  { maskTable      = sparseMaskFrequency
  ; signTable      = balancedSignFrequency
  ; maskNormalized = sparseMaskFrequency-normalized
  ; signNormalized = balancedSignFrequency-normalized
  }

-- Encoder/decoder implementations may instantiate this contract with trained
-- per-plane or contextual tables.  Claims about achieved rate, parallelism,
-- patents, AV1 comparison, or compute cost remain empirical/external claims.
