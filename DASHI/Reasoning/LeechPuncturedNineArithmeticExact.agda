{-# OPTIONS --safe #-}
module DASHI.Reasoning.LeechPuncturedNineArithmeticExact where

-- Safe arithmetic leaf for the actual Leech-LILA hidden/head widths.
-- This is numerical compatibility, NOT a Leech lattice automorphism.
-- Source prior: DASHI/OggSSPP2BalancedTernaryPuncturedPlaneExact
-- owns T² minus centre = eight positions = four opposite pairs.
-- Original Leech-LILA author: Anatolii Kornienko,
-- https://doi.org/10.5281/zenodo.18784424
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_; _*_; _-_)

puncturedNineCount : Nat
puncturedNineCount = 3 * 3 - 1

puncturedNineIsEight : puncturedNineCount ≡ 8
puncturedNineIsEight = refl

puncturedNineIsFourPairs : puncturedNineCount ≡ 4 * 2
puncturedNineIsFourPairs = refl

one24DChart : 24 ≡ 3 * puncturedNineCount
one24DChart = refl

fullLearner : 384 ≡ 16 * 3 * puncturedNineCount
fullLearner = refl

primeFactorisation : 384 ≡ 2 * 2 * 2 * 2 * 2 * 2 * 2 * 3
primeFactorisation = refl

block24PrimeFactorisation : 24 ≡ 2 * 2 * 2 * 3
block24PrimeFactorisation = refl

oneHead : 48 ≡ 2 * 3 * puncturedNineCount
oneHead = refl

eightHeads : 384 ≡ 8 * 2 * 3 * puncturedNineCount
eightHeads = refl

headPrimeFactorisation : 48 ≡ 2 * 2 * 2 * 2 * 3
headPrimeFactorisation = refl

-- A 9-site wave has 1 DC Fourier mode and eight non-DC modes.
-- The eight non-DC modes pair into four conjugate character pairs.
nineModes : 9 ≡ 1 + puncturedNineCount
nineModes = refl

threeEightModeWaveLanes : 24 ≡ 3 * (4 * 2)
threeEightModeWaveLanes = refl

-- This arithmetic does not identify punctured site amplitudes with
-- nontrivial dual-group characters or prove an analytic j/CM relation.
