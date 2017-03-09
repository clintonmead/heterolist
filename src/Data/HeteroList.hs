{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE UndecidableSuperClasses #-}

{-|
This module provides heterogenuous lists. There are a few functions on these lists which are an attempt
to be parallels of the 'Data.Functor.Functor', 'Control.Applicative.Applicative' and 'Control.Monad.Monad' classes,
although these are not part of type classes, and certainly not the above classes because the types don't match.

I believe this sort of package has potential in testing generic libraries.

For example, lets say you have @(n)@ sets of test data.

And @(m)@ different functions that work on that data.

And @(m)@ different "check functions" (perhaps just the functions above but one release back as a control).

Making a complete test case for all this is tricky, because you may be testing different types and the functions you're
testing on them may have different results.

You can sometimes get situations where you just have to write @(n * m)@ test cases.

This approach hopefully makes the work @(n + m)@ instead.

It probably needs some work but I have included a functional example in the documentation for 'hap'.
-}
module Data.HeteroList (
  HeteroList((:-), Nil),
  (++), happend,
  HeteroListConstraint,
  IsHeteroList,
  GetHead, GetTail,
  GetHeteroListParam,
  hconcat,
  hmap,
  hconcatMap,
  HeteroMapConstraint,
  hmapfl,
  hap,
  ConcatT,
  toList,
  IsHomogeneousList,
  length,
  ListLength
)
where

import GHC.Exts (Constraint)
import Data.Poly (Poly(Poly), IsPoly, GetPolyConstraint)
--import Data.Poly.Functor (PolyFunctor, hmap, PolyFunctorConstraint)

import Data.Proxy (Proxy(Proxy))
import Control.IndexT.Constructor (IsData)

import Control.IndexT.Function (IsFunc,ResultT)
import Control.IndexT (IndexT)

import Data.Poly.Function (Equal)

import GHC.TypeLits (Nat, type (+))

import Prelude (
  Show, show,
  Eq, (==), Bool(True, False), (&&),
  Ord, compare, Ordering(GT, EQ, LT),
  Int, (+),
  seq
  )
import qualified Prelude

import Data.Foldable (Foldable)

data ShowRest a = ShowRest a

instance Show (HeteroList '[]) where
  show Nil = "[]"

instance (Show a, Show (ShowRest (HeteroList as))) => Show (HeteroList (a:as)) where
  show (x :- xs) = "[" Prelude.++ show x Prelude.++ (show (ShowRest xs)) Prelude.++ "]"

instance (Show a, Show (ShowRest (HeteroList as))) => Show (ShowRest (HeteroList (a:as))) where
  show (ShowRest (x :- xs)) = ", " Prelude.++ show x Prelude.++ show (ShowRest xs)

instance Show (ShowRest (HeteroList '[])) where
  show (ShowRest Nil) = ""
{-|
Heterogeneous list type. Construct like so:

> x = (5 :: Int) :- 'a' :- True :- Nil
-}
data HeteroList (l :: [*]) where
  (:-) :: a -> HeteroList as -> HeteroList (a:as)
  Nil :: HeteroList '[]

instance (HeteroListConstraint Eq a) => Eq (HeteroList a) where
  (x :- xs) == (y :- ys) = x == y && xs == ys
  Nil == Nil = True
  _ == _ = False

instance (HeteroListConstraint Eq a, HeteroListConstraint Ord a) => Ord (HeteroList a) where
  compare (x :- xs) (y :- ys) =
    let r = compare x y in
      case r of
        EQ -> compare xs ys
        _ -> r
  compare Nil Nil = EQ

infixr 5 :-

type family (a :: [*]) :++ (b :: [*]) where
  '[] :++ b = b
  (a:as) :++ b = a:(as :++ b)

{-|
Append two heterogeneous lists. Of course, as 'HeteroList's know their type, this produces a new type.
-}
(++) :: HeteroList a -> HeteroList b -> HeteroList (a :++ b)
(++) x y = case x of
  Nil -> y
  (x :- xs) -> x :- (xs ++ y)

{-|
Synonym for '(++)'.
-}
happend :: HeteroList a -> HeteroList b -> HeteroList (a :++ b)
happend = (++)

{-|
Get the type of the first element of a 'HeteroList'
-}
type family GetHead a where
  GetHead (HeteroList (a:_)) = a

{-|
Get the type of the tail of a 'HeteroList'.
-}
type family GetTail a where
  GetTail (HeteroList (_:as)) = as

type IsHeteroListT a = a ~ HeteroList ((GetHead a):(GetTail a))

{-|
Constraint which requires the argument to be a 'HeteroList'
-}
class (IsHeteroListT a) => IsHeteroList a
instance (IsHeteroListT a) => IsHeteroList a

{-|
Gets the types of the 'HeteroList'. Naturally this is a list of types of type @[*]@.
-}
type family GetHeteroListParam a where
  GetHeteroListParam (HeteroList a) = a

-- This is an attempt to define hmap as part of the 'Data.Poly.Functor' type class.
-- It's causing more trouble than it's worth for the moment so it's commented out, and a non type class
-- approach is used.
{-
type IsPolyFunctor c t = (PolyFunctor t, PolyFunctorConstraint c t)

type instance PolyFunctorConstraint c (HeteroList (a:as) -> HeteroList (b:bs)) = (c (a -> b), PolyFunctorConstraint c (HeteroList as -> HeteroList bs))
type instance PolyFunctorConstraint c (HeteroList '[] -> HeteroList '[]) = ()


instance (IsHeteroList a, PolyFunctor (HeteroList (GetTail a) -> HeteroList bs)) => PolyFunctor (a -> HeteroList (b:bs)) where
  hmap = hmap'

instance (IsHeteroList b, PolyFunctor (HeteroList as -> HeteroList (GetTail b))) => PolyFunctor (HeteroList (a:as) -> b) where
  hmap = hmap'

instance {-# OVERLAPPING #-} PolyFunctor (HeteroList as -> HeteroList bs) => PolyFunctor (HeteroList (a:as) -> HeteroList (b:bs)) where
  hmap = hmap'

hmap' :: (c (a -> b), PolyFunctorConstraint c (HeteroList as -> HeteroList bs), PolyFunctor (HeteroList as -> HeteroList bs)) => Poly c -> HeteroList (a:as) -> HeteroList (b:bs)
hmap' pf@(Poly f) (x :- xs) = (f x) :- hmap pf xs

instance (a ~ HeteroList '[]) => PolyFunctor (a -> HeteroList '[]) where
  hmap _ Nil = Nil

instance (b ~ HeteroList '[]) => PolyFunctor (HeteroList '[] -> b) where
  hmap _ Nil = Nil

instance {-# OVERLAPPING #-} PolyFunctor (HeteroList '[] -> HeteroList '[]) where
  hmap _ Nil = Nil
-}

type family HeteroListConstraintT c a :: Constraint where
  HeteroListConstraintT c (a:as) = (c a, HeteroListConstraintT c as)
  HeteroListConstraintT _ '[] = ()

{-|
Applies a constraint @c@ to a type of @HeteroList a@.
So you want to write this:

> (HeteroListConstraintT c t) => HeteroList t

not

> HeteroListConstraintT c (HeteroList t)  => HeteroList t
-}
class HeteroListConstraintT c a => HeteroListConstraint c a
instance HeteroListConstraintT c a => HeteroListConstraint c a

{-|
The type of a concatenated list. Note, like 'HeteroListConstraintT' you need to apply this type function to
the parameter to 'HeteroList'.
-}
type family ConcatT a where
  ConcatT ((HeteroList a):as) = (a :++ ConcatT as)
  ConcatT '[] = '[]

{-|
An analogue to 'Prelude.concat'
-}
hconcat :: (HeteroListConstraint IsHeteroList a) => HeteroList a -> HeteroList (ConcatT a)
hconcat (x :- xs) = x ++ hconcat xs
hconcat Nil = Nil

type family HeadList a where
  HeadList (a:_) = a

type family TailList a where
  TailList (_:as) = as

type IsNonEmptyList a = (a ~ ((HeadList a):(TailList a)))

type family HeteroMapConstraintT c a b :: Constraint where
  HeteroMapConstraintT _ '[] b = (b ~ '[])
  HeteroMapConstraintT c a b = (IsNonEmptyList a, IsNonEmptyList b, c ((HeadList a) -> (HeadList b)), HeteroMapConstraintT c (TailList a) (TailList b))

{-|
This constraints @c@, which is intended to be the argument of a 'Poly', to be a constraint which allows one
to map between the two 'HeteroList's of type @a@ and @b@
-}
class HeteroMapConstraintT c a b => HeteroMapConstraint c a b
instance HeteroMapConstraintT c a b => HeteroMapConstraint c a b

{-|
The analogue of 'Prelude.map'. Not you'll need to pass a 'Poly' as the function. A more complex example is
included in the function 'hap'.
-}
hmap :: HeteroMapConstraint c a b => Poly c -> HeteroList a -> HeteroList b
hmap pf@(Poly f) x = case x of
  (x :- xs) -> (f x) :- (hmap pf xs)
  Nil -> Nil

{-|
The analogue of 'Prelude.concatMap', or  '>>=' (\"bind\") from 'Control.Monad.Monad'.
It's just 'hmap' followed by 'hconcat'.
-}
hconcatMap :: forall c a b. (HeteroMapConstraint c a b, HeteroListConstraint IsHeteroList b) => Poly c -> HeteroList a -> HeteroList (ConcatT b)
hconcatMap f x = hconcat ((hmap f x) :: HeteroList b)

{-|
Applies every function in the 'HeteroList' of 'Poly's in the first argument to the 'HeteroList' which is the second argument.
This is much like 'hap' except the result list is not \"flattened\" by 'hconcat'
-}
hmapfl :: forall f a b c. (HeteroMapConstraint c f b, c ~ WhatsC a, HeteroListConstraint IsHeteroList b) => HeteroList f -> HeteroList a -> HeteroList b
hmapfl fs l = hmap g fs where
  g :: Poly c
  g = Poly (\f -> hmap f l)

type WhatsCT a t = (IsFunc 1 t, IsPoly (IndexT 0 t), IsHeteroList (ResultT 1 t), HeteroMapConstraint (GetPolyConstraint (IndexT 0 t)) a (GetHeteroListParam (ResultT 1 t)))

class WhatsCT a t => WhatsC a t
instance WhatsCT a t => WhatsC a t

{-|
This is the analogue of 'Control.Monad.ap', or 'Control.Applicative.\<*\>. Arguments are the same as 'hmapfl', but the result is flattened.

Here's an example usage:

>>> triple = Poly @((IsHomoFunc 1) &&& ((Arg 0) `IxConstrainBy` Num)) (*3)
>>> compareZero = Poly @((IsFunc 1) &&& ((Arg 0) `IxConstrainBy` (Num &&& Ord)) &&& ((Result 1) `IxIs` Ordering)) (`compare` 0)
>>> greaterThanZero = Poly @((IsFunc 1) &&& ((Arg 0) `IxConstrainBy` (Num &&& Ord)) &&& ((Result 1) `IxIs` Bool)) (> 0)

>>> f = triple :- compareZero :- greaterThanZero :- Nil
>>> x = (42 :: Int) :- (-100 :: Float) :- (22 % 7 :: Rational) :- Nil

>>> f `hap` x
[126, -300.0, 66 % 7, GT, LT, GT, True, False, True]

Note that
-}
hap :: forall f a b c. (HeteroMapConstraint c f b, c ~ WhatsC a, HeteroListConstraint IsHeteroList b) => HeteroList f -> HeteroList a -> HeteroList (ConcatT b)
hap f x = hconcat ((hmapfl f x) :: HeteroList b)

{-|
> IsHomogeneousList a t

constraints a 'HeteroList t' to have elements only of type a.

i.e.

> IsHomogeneousList Int t => HeteroList t

means the 'HeteroList' only has elements of type @Int@.
-}
class HeteroListConstraint (Equal a) t => IsHomogeneousList a t
instance HeteroListConstraint (Equal a) t => IsHomogeneousList a t

{-|
Naturally, if (and only if) a 'HeteroList' is actually homogeneous, we can turn it into an ordinary list.
-}
toList :: forall a t. (IsHomogeneousList a t) => HeteroList t -> [a]
toList (x :- xs) = x:(toList xs)
toList Nil = []

{-|
Type level length the paramter of a 'HeteroList'
-}
type family ListLength t :: Nat where
  ListLength '[] = 0
  ListLength (_:as) = 1 + ListLength as

{-|
Length of a 'HeteroList'. I'm not sure if this can be done in constant time as the type defines the length,
but currently it just does the usual traverse the list and count.
-}
length :: forall t. HeteroList t -> Int
length = go 0 where
  go :: forall t. Int -> HeteroList t -> Int
  go acc Nil = acc
  go acc (_ :- xs) = let acc' = acc + 1 in acc' `seq` go acc' xs