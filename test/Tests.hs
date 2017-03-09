{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses #-}
{-# LANGUAGE FlexibleInstances #-}

module Main where

import Data.Poly
import Data.Poly.Functor
import Data.Poly.Function
import Control.IndexT.Constructor
import Control.IndexT.Function
import Control.IndexT

import Control.ConstraintManip

import Data.HeteroList

import Test.Hspec (hspec, it, shouldBe)
import Data.Ratio ((%), Rational)

triple = Poly @((IsHomoFunc 1) &&& ((Arg 0) `IxConstrainBy` Num)) (*3)
compareZero = Poly @((IsFunc 1) &&& ((Arg 0) `IxConstrainBy` (Num &&& Ord)) &&& ((Result 1) `IxIs` Ordering)) (`compare` 0)
greaterThanZero = Poly @((IsFunc 1) &&& ((Arg 0) `IxConstrainBy` (Num &&& Ord)) &&& ((Result 1) `IxIs` Bool)) (> 0)

f = triple :- compareZero :- greaterThanZero :- Nil
x = (42 :: Int) :- (-100 :: Float) :- (22 % 7 :: Rational) :- Nil
--f = triple :- Nil
--x = (3 :: Integer) :- Nil
main = hspec $ do
  it "mkPolyFunc1 test" $ (f `hap` x) `shouldBe` (126 :- -300 :- 66 % 7 :- GT :- LT :- GT :- True :- False :- True :- Nil)

