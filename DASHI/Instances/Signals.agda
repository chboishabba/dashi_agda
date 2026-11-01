{-# OPTIONS --safe #-}
module DASHI.Instances.Signals where

record SignalInstance : Set₁ where
  field
    S : Set
    T : S → S
