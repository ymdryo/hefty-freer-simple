{-# OPTIONS_GHC -Wno-redundant-constraints #-} -- Due to sendM.
{-# OPTIONS_HADDOCK not-home #-}

{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeFamilies #-}

-- The following is needed to define MonadPlus instance. It is decidable
-- (there is no recursion!), but GHC cannot see that.
--
-- TODO: Remove once GHC can deduce the decidability of this instance.
{-# LANGUAGE UndecidableInstances #-}

-- |
-- Module:       Control.Monad.Freer.Internal
-- Description:  Mechanisms to make effects work.
-- Copyright:    (c) 2016 Allele Dev; 2017 Ixperta Solutions s.r.o.; 2017 Alexis King
-- License:      BSD3
-- Maintainer:   Alexis King <lexi.lambda@gmail.com>
-- Stability:    experimental
-- Portability:  GHC specific language extensions.
--
-- Internal machinery for this effects library. This includes:
--
-- * 'Eff' data type, for expressing effects.
-- * 'NonDet' data type, for nondeterministic effects.
-- * Functions for facilitating the construction of effects and their handlers.
--
-- Using <http://okmij.org/ftp/Haskell/extensible/Eff1.hs> as a starting point.
module Control.Monad.Freer.Internal (module Control.Monad.Freer.Internal, module Data.OpenUnion, module Data.FTCQueue) where

import Control.Applicative (Alternative(..))
import Control.Monad (MonadPlus(..))
import Control.Monad.Base (MonadBase, liftBase)
import Control.Monad.IO.Class (MonadIO, liftIO)

import Data.FTCQueue
import Data.OpenUnion
import Control.Natural (type (~>))
import Data.Bifunctor (bimap, first)

-- | Effectful arrow type: a function from @a :: *@ to @b :: *@ that also does
-- effects denoted by @effs :: [* -> *]@.
type Arr eh ef a b = a -> Eff eh ef b

-- | An effectful function from @a :: *@ to @b :: *@ that is a composition of
-- several effectful functions. The paremeter @effs :: [* -> *]@ describes the
-- overall effect. The composition members are accumulated in a type-aligned
-- queue.
type Arrs eh ef a b = FTCQueue (Eff eh ef) a b

-- | The 'Eff' monad provides the implementation of a computation that performs
-- an arbitrary set of algebraic effects. In @'Eff' effs a@, @effs@ is a
-- type-level list that contains all the effects that the computation may
-- perform. For example, a computation that produces an 'Integer' by consuming a
-- 'String' from the global environment and acting upon a single mutable cell
-- containing a 'Bool' would have the following type:
--
-- @
-- 'Eff' '['Control.Monad.Freer.Reader.Reader' 'String', 'Control.Monad.Freer.State.State' 'Bool'] 'Integer'
-- @
--
-- Normally, a concrete list of effects is not used to parameterize 'Eff'.
-- Instead, the 'Member' or 'Members' constraints are used to express
-- constraints on the list of effects without coupling a computation to a
-- concrete list of effects. For example, the above example would more commonly
-- be expressed with the following type:
--
-- @
-- 'Members' '['Control.Monad.Freer.Reader.Reader' 'String', 'Control.Monad.Freer.State.State' 'Bool'] effs => 'Eff' effs 'Integer'
-- @
--
-- This abstraction allows the computation to be used in functions that may
-- perform other effects, and it also allows the effects to be handled in any
-- order.
data Eff eh ef a
  = Val a
  -- ^ Pure value (@'return' = 'pure' = 'Val'@).
  | forall b. E (Either (UnionH eh (Eff eh ef) b) (Union ef b)) (Arrs eh ef b a)
  -- ^ Sending a request of type @Union effs@ with the continuation
  -- @'Arrs' r b a@.

-- | Function application in the context of an array of effects,
-- @'Arrs' eh ef b w@.
qApp :: Arrs eh ef b w -> b -> Eff eh ef w
qApp q' x = case tviewl q' of
  TOne k  -> k x
  k :| t -> case k x of
    Val y -> qApp t y
    E u q -> E u (q >< t)

-- | Composition of effectful arrows ('Arrs'). Allows for the caller to change
-- the effect environment, as well.
qComp :: Arrs eh ef a b -> (Eff eh ef b -> Eff eh' ef' c) -> Arr eh' ef' a c
qComp g h a = h $ qApp g a

instance Functor (Eff eh ef) where
  fmap f (Val x) = Val (f x)
  fmap f (E u q) = E u (q |> (Val . f))
  {-# INLINE fmap #-}

instance Applicative (Eff eh ef) where
  pure = Val
  {-# INLINE pure #-}

  Val f <*> Val x = Val $ f x
  Val f <*> E u q = E u (q |> (Val . f))
  E u q <*> m     = E u (q |> (`fmap` m))
  {-# INLINE (<*>) #-}

instance Monad (Eff eh ef) where
  Val x >>= k = k x
  E u q >>= k = E u (q |> k)
  {-# INLINE (>>=) #-}

instance (MonadBase b m, LastMember m ef) => MonadBase b (Eff eh ef) where
  liftBase = sendM . liftBase
  {-# INLINE liftBase #-}

instance (MonadIO m, LastMember m ef) => MonadIO (Eff eh ef) where
  liftIO = sendM . liftIO
  {-# INLINE liftIO #-}

-- | “Sends” an effect, which should be a value defined as part of an effect
-- algebra (see the module documentation for "Control.Monad.Freer"), to an
-- effectful computation. This is used to connect the definition of an effect to
-- the 'Eff' monad so that it can be used and handled.
send :: Member eff ef => eff a -> Eff eh ef a
send t = E (Right $ inj t) (tsingleton Val)
{-# INLINE send #-}

sendH :: (MemberH eff eh, HFunctor eff) => eff (Eff eh ef) a -> Eff eh ef a
sendH t = E (Left $ injH t) (tsingleton Val)
{-# INLINE sendH #-}

-- | Identical to 'send', but specialized to the final effect in @eh ef@ to
-- assist type inference. This is useful for running actions in a monad
-- transformer stack used in conjunction with 'runM'.
sendM :: (Monad m, LastMember m ef) => m a -> Eff eh ef a
sendM = send
{-# INLINE sendM #-}

--------------------------------------------------------------------------------
                       -- Base Effect Runner --
--------------------------------------------------------------------------------

-- | Runs a pure 'Eff' computation, since an 'Eff' computation that performs no
-- effects (i.e. has no effects in its type-level list) is guaranteed to be
-- pure. This is usually used as the final step of running an effectful
-- computation, after all other effects have been discharged using effect
-- handlers.
--
-- Typically, this function is composed as follows:
--
-- @
-- someProgram
--   'Data.Function.&' runEff1 eff1Arg
--   'Data.Function.&' runEff2 eff2Arg1 eff2Arg2
--   'Data.Function.&' 'run'
-- @
run :: Eff '[] '[] a -> a
run (Val x) = x
run _       = error "Internal:run - This (E) should never happen"

-- | Like 'run', 'runM' runs an 'Eff' computation and extracts the result.
-- /Unlike/ 'run', 'runM' allows a single effect to remain within the type-level
-- list, which must be a monad. The value returned is a computation in that
-- monad, which is useful in conjunction with 'sendM' or 'liftBase' for plugging
-- in traditional transformer stacks.
runM :: Monad m => Eff '[] '[m] a -> m a
runM (Val x) = return x
runM (E (Right u) q) = case extract u of
  mb -> mb >>= runM . qApp q
runM (E (Left _) _) = error "unreachable"
  -- The other case is unreachable since Union [] a cannot be constructed.
  -- Therefore, run is a total function if its argument terminates.

interpretKS
  :: forall t gs s eh' ef w a. KnownLen gs =>
     s
  -> (s -> a -> Eff eh' (gs :++: ef) w)
  -> (forall x. s -> t x -> (s -> Arr eh' (gs :++: ef) x w) -> Eff eh' (gs :++: ef) w)
  -> Eff '[] (t ': ef) a
  -> Eff eh' (gs :++: ef) w
interpretKS s' ret hdl = loop s'
  where
    loop s (Val x)  = ret s x
    loop s (E u' q) =
        case u' of
            Right u'' -> case decomp u'' of
                Right x -> hdl s x k
                Left  u -> E (Right $ weakens @gs u) (tsingleton (k s))
            Left u -> exhaustH u
      where
        k s'' x = loop s'' $ qApp q x
{-# INLINE interpretKS #-}

interpretK
  :: forall t gs eh' ef w a. KnownLen gs =>
     (a -> Eff eh' (gs :++: ef) w)
  -> (forall x. t x -> Arr eh' (gs :++: ef) x w -> Eff eh' (gs :++: ef) w)
  -> Eff '[] (t ': ef) a
  -> Eff eh' (gs :++: ef) w
interpretK ret hdl = loop
  where
    loop (Val x)  = ret x
    loop (E u' q) =
        case u' of
            Right u'' -> case decomp u'' of
                Right x -> hdl x k
                Left  u -> E (Right $ weakens @gs u) (tsingleton k)
            Left u -> exhaustH u
      where
        k x = loop $ qApp q x
{-# INLINE interpretK #-}

interpretKSH
  :: forall t gs s eh' ef w a. (HFunctor t, KnownLen gs) =>
     s
  -> (s -> a -> Eff eh' (gs :++: ef) w)
  -> (forall x. s -> t (Eff '[t] ef) x -> (s -> Arr eh' (gs :++: ef) x w) -> Eff eh' (gs :++: ef) w)
  -> Eff '[t] ef a
  -> Eff eh' (gs :++: ef) w
interpretKSH s' ret elb = loop s'
  where
    loop s (Val x)  = ret s x
    loop s (E u' q) =
        case u' of
            Right u'' -> E (Right $ weakens @gs u'') (tsingleton (k s))
            Left u -> elb s (extractH u) k
      where
        k s'' x = loop s'' $ qApp q x
{-# INLINE interpretKSH #-}

interpretKH
  :: forall t gs eh' ef w a. (HFunctor t, KnownLen gs) =>
     (a -> Eff eh' (gs :++: ef) w)
  -> (forall x. t (Eff '[t] ef) x -> Arr eh' (gs :++: ef) x w -> Eff eh' (gs :++: ef) w)
  -> Eff '[t] ef a
  -> Eff eh' (gs :++: ef) w
interpretKH ret elb = loop
  where
    loop (Val x)  = ret x
    loop (E u' q) =
        case u' of
            Right u'' -> E (Right $ weakens @gs u'') (tsingleton k)
            Left u -> elb (extractH u) k
      where
        k x = loop $ qApp q x
{-# INLINE interpretKH #-}

interpretRecKS
  :: forall t gs s eh ef. KnownLen gs =>
     s
  -> (forall x r. s -> t x -> (s -> Arr eh (gs :++: ef) x r) -> Eff eh (gs :++: ef) r)
  -> Eff eh (t ': ef) ~> Eff eh (gs :++: ef)
interpretRecKS s' hdl = loop s'
  where
    loop :: s -> Eff eh (t ': ef) ~> Eff eh (gs :++: ef)
    loop _ (Val x)  = pure x
    loop s (E u' q) =
        case u' of
            Right u'' -> case decomp u'' of
                Right x -> hdl s x k
                Left  u -> E (Right $ weakens @gs u) (tsingleton (k s))
            Left u -> E (Left $ hfmapUnion (loop s) u) (tsingleton (k s))
      where
        k s'' x = loop s'' $ qApp q x
{-# INLINE interpretRecKS #-}

interpretRecK
  :: forall t gs eh ef. KnownLen gs =>
     (forall x r. t x -> Arr eh (gs :++: ef) x r -> Eff eh (gs :++: ef) r)
  -> Eff eh (t ': ef) ~> Eff eh (gs :++: ef)
interpretRecK hdl = loop
  where
    loop :: Eff eh (t ': ef) ~> Eff eh (gs :++: ef)
    loop (Val x)  = pure x
    loop (E u' q) =
        case u' of
            Right u'' -> case decomp u'' of
                Right x -> hdl x k
                Left  u -> E (Right $ weakens @gs u) (tsingleton k)
            Left u -> E (Left $ hfmapUnion loop u) (tsingleton k)
      where
        k x = loop $ qApp q x
{-# INLINE interpretRecK #-}

interpretRecKSH
  :: forall t gs hs s eh ef. (HFunctor t, KnownLen gs, KnownLen hs) =>
     s
  -> (forall x r. s -> t (Eff (hs :++: eh) (gs :++: ef)) x -> (s -> Arr (hs :++: eh) (gs :++: ef) x r) -> Eff (hs :++: eh) (gs :++: ef) r)
  -> Eff (t ': eh) ef ~> Eff (hs :++: eh) (gs :++: ef)
interpretRecKSH s' elb = loop s'
  where
    loop :: s -> Eff (t ': eh) ef ~> Eff (hs :++: eh) (gs :++: ef)
    loop _ (Val x)  = pure x
    loop s (E u' q) =
        case u' of
            Right u'' -> E (Right $ weakens @gs u'') (tsingleton (k s))
            Left u'' -> case decompH u'' of
                Right x -> elb s (hfmap (loop s) x) k
                Left u -> E (Left $ hfmapUnion (loop s) . weakensH @hs $ u) (tsingleton (k s))
      where
        k s'' x = loop s'' $ qApp q x
{-# INLINE interpretRecKSH #-}

interpretRecKH
  :: forall t gs hs eh ef. (HFunctor t, KnownLen gs, KnownLen hs) =>
     (forall x r. t (Eff (hs :++: eh) (gs :++: ef)) x -> Arr (hs :++: eh) (gs :++: ef) x r -> Eff (hs :++: eh) (gs :++: ef) r)
  -> Eff (t ': eh) ef ~> Eff (hs :++: eh) (gs :++: ef)
interpretRecKH elb = loop
  where
    loop :: Eff (t ': eh) ef ~> Eff (hs :++: eh) (gs :++: ef)
    loop (Val x)  = pure x
    loop (E u' q) =
        case u' of
            Right u'' -> E (Right $ weakens @gs u'') (tsingleton k)
            Left u'' -> case decompH u'' of
                Right x -> elb (hfmap loop x) k
                Left u -> E (Left $ hfmapUnion loop . weakensH @hs $ u) (tsingleton k)
      where
        k x = loop $ qApp q x
{-# INLINE interpretRecKH #-}

interpretKSHF
  :: forall th tf gs s eh' ef w a. (HFunctor th, KnownLen gs) =>
     s
  -> (s -> a -> Eff eh' (gs :++: ef) w)
  -> (forall x. s -> th (Eff '[th] (tf ': ef)) x -> (s -> Arr eh' (gs :++: ef) x w) -> Eff eh' (gs :++: ef) w)
  -> (forall x. s -> tf x -> (s -> Arr eh' (gs :++: ef) x w) -> Eff eh' (gs :++: ef) w)
  -> Eff '[th] (tf ': ef) a
  -> Eff eh' (gs :++: ef) w
interpretKSHF s' ret elb hdl = loop s'
  where
    loop s (Val x)  = ret s x
    loop s (E u' q) =
        case u' of
            Right u'' -> case decomp u'' of
                Right x -> hdl s x k
                Left  u -> E (Right $ weakens @gs u) (tsingleton (k s))
            Left u -> elb s (extractH u) k
      where
        k s'' x = loop s'' $ qApp q x
{-# INLINE interpretKSHF #-}

interposeKS
  :: Member eff ef =>
     s
  -> (s -> a -> Eff '[] ef b)
  -> (forall v. s -> eff v -> (s -> Arr '[] ef v b) -> Eff '[] ef b)
  -> Eff '[] ef a
  -> Eff '[] ef b
interposeKS s' ret h = loop s'
  where
    loop s (Val x) = ret s x
    loop s (E u q) = case u of
        Right u' -> case prj u' of
            Just x -> h s x k
            _      -> E u (tsingleton (k s))
        Left u' -> exhaustH u'
      where
        k s'' x = loop s'' $ qApp q x
{-# INLINE interposeKS #-}

interposeK
  :: Member eff ef =>
     (a -> Eff '[] ef b)
  -> (forall v. eff v -> Arr '[] ef v b -> Eff '[] ef b)
  -> Eff '[] ef a
  -> Eff '[] ef b
interposeK ret h = loop
  where
    loop (Val x) = ret x
    loop (E u q) = case u of
        Right u' -> case prj u' of
            Just x -> h x k
            _      -> E u (tsingleton k)
        Left u' -> exhaustH u'
      where
        k x = loop $ qApp q x
{-# INLINE interposeK #-}

interposeRecKS
  :: forall eff s eh ef. Member eff ef =>
     s
  -> (forall v b. s -> eff v -> (s -> Arr eh ef v b) -> Eff eh ef b)
  -> Eff eh ef ~> Eff eh ef
interposeRecKS s' h = loop s'
  where
    loop _ (Val x) = pure x
    loop s (E u q) = case u of
        Right u' -> case prj u' of
            Just x -> h s x k
            _      -> E u (tsingleton (k s))
        Left _ -> E u (tsingleton (k s))
      where
        k s'' x = loop s'' $ qApp q x
{-# INLINE interposeRecKS #-}

interposeRecK
  :: Member eff ef =>
     (forall v b. eff v -> Arr eh ef v b -> Eff eh ef b)
  -> Eff eh ef ~> Eff eh ef
interposeRecK h = loop
  where
    loop (Val x) = pure x
    loop (E u q) = case u of
        Right u' -> case prj u' of
            Just x -> h x k
            _      -> E u (tsingleton k)
        Left _ -> E u (tsingleton k)
      where
        k x = loop $ qApp q x
{-# INLINE interposeRecK #-}

interposeRecKSH
  :: forall eff s eh ef. (MemberH eff eh, HFunctor eff) =>
     s
  -> (forall v x. s -> eff (Eff eh ef) v -> (s -> Arr eh ef v x) -> Eff eh ef x)
  -> Eff eh ef ~> Eff eh ef
interposeRecKSH s' h = loop s'
  where
    loop :: s -> Eff eh ef ~> Eff eh ef
    loop _ (Val x) = pure x
    loop s (E u q) = case u of
        Right _ -> E u (tsingleton $ k s)
        Left u' -> case prjH u' of
            Just x -> h s x k
            _ -> E (Left $ hfmapUnion (loop s) u') (tsingleton $ k s)
      where
        k s'' x = loop s'' $ qApp q x
{-# INLINE interposeRecKSH #-}

interposeRecKH
  :: forall eff eh ef. (MemberH eff eh, HFunctor eff) =>
     (forall v x. eff (Eff eh ef) v -> Arr eh ef v x -> Eff eh ef x)
  -> Eff eh ef ~> Eff eh ef
interposeRecKH h = loop
  where
    loop :: Eff eh ef ~> Eff eh ef
    loop (Val x) = pure x
    loop (E u q) = case u of
        Right _ -> E u (tsingleton k)
        Left u' -> case prjH u' of
            Just x -> h x k
            _ -> E (Left $ hfmapUnion loop u') (tsingleton k)
      where
        k x = loop $ qApp q x
{-# INLINE interposeRecKH #-}

-- | Embeds a less-constrained 'Eff' into a more-constrained one. Analogous to
-- MTL's 'lift'.
raise :: Eff eh ef a -> Eff eh (e ': ef) a
raise = loop
  where
    loop :: Eff eh ef ~> Eff eh (e ': ef)
    loop (Val x) = pure x
    loop (E u q) = E (bimap (hfmapUnion loop) weaken u) . tsingleton $ qComp q loop
{-# INLINE raise #-}

-- | Embeds a less-constrained 'Eff' into a more-constrained one. Analogous to
-- MTL's 'lift'.
raiseH :: Eff eh ef a -> Eff (e ': eh) ef a
raiseH = loop
  where
    loop :: Eff eh ef ~> Eff (e ': eh) ef
    loop (Val x) = pure x
    loop (E u q) = E (first (hfmapUnion loop . weakenH) u) . tsingleton $ qComp q loop
{-# INLINE raiseH #-}

--------------------------------------------------------------------------------
                    -- Nondeterministic Choice --
--------------------------------------------------------------------------------

-- | A data type for representing nondeterminstic choice.
data NonDet a where
  MZero :: NonDet a
  MPlus :: NonDet Bool

instance Member NonDet ef => Alternative (Eff eh ef) where
  empty = mzero
  (<|>) = mplus

instance Member NonDet ef => MonadPlus (Eff eh ef) where
  mzero       = send MZero
  mplus m1 m2 = send MPlus >>= \x -> if x then m1 else m2
