{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE BlockArguments #-}

-- |
-- Module:       Control.Monad.Freer.State
-- Description:  State effects, for state-carrying computations.
-- Copyright:    (c) 2016 Allele Dev; 2017 Ixperta Solutions s.r.o.; 2017 Alexis King
-- License:      BSD3
-- Maintainer:   Alexis King <lexi.lambda@gmail.com>
-- Stability:    experimental
-- Portability:  GHC specific language extensions.
--
-- Composable handler for 'State' effects. Handy for passing an updatable state
-- through a computation.
--
-- Some computations may not require the full power of 'State' effect:
--
-- * For a read-only state, see "Control.Monad.Freer.Reader".
-- * To accumulate a value without using it on the way, see
--   "Control.Monad.Freer.Writer".
--
-- Using <http://okmij.org/ftp/Haskell/extensible/Eff1.hs> as a starting point.
module Control.Monad.Freer.State
  ( -- * State Effect
    State(..)

    -- * State Operations
  , get
  , put
  , modify
  , gets

    -- * State Handlers
  , runState
  , runStateRec
  , runStateIO
  , evalState
  , execState

    -- * State Utilities
  , transactionState
  , transactionState'
  ) where

import Data.Proxy (Proxy)

import Control.Monad.Freer (Eff, Member, send, interposeKS, interpretKS, interpretRecKS, interpretRec, LastMember, interpret)
import Control.Monad.Freer.Internal (Arr)
import Data.IORef (newIORef, readIORef, writeIORef)
import Control.Monad.IO.Class (liftIO)
import Data.Function ((&))

-- | Strict 'State' effects: one can either 'Get' values or 'Put' them.
data State s r where
  Get :: State s s
  Put :: !s -> State s ()

-- | Retrieve the current value of the state of type @s :: *@.
get :: forall s effs eh. Member (State s) effs => Eff eh effs s
get = send Get

-- | Set the current state to a specified value of type @s :: *@.
put :: forall s effs eh. Member (State s) effs => s -> Eff eh effs ()
put s = send (Put s)

-- | Modify the current state of type @s :: *@ using provided function
-- @(s -> s)@.
modify :: forall s effs eh. Member (State s) effs => (s -> s) -> Eff eh effs ()
modify f = fmap f get >>= put

-- | Retrieve a specific component of the current state using the provided
-- projection function.
gets :: forall s a effs eh. Member (State s) effs => (s -> a) -> Eff eh effs a
gets f = f <$> get

-- | Handler for 'State' effects.
runState :: forall s effs a. s -> Eff '[] (State s ': effs) a -> Eff '[] effs (a, s)
runState s0 = interpretKS @_ @'[] s0 (\s x -> pure (x, s)) $ \s x k -> case x of
  Get -> k s s
  Put s' -> k s' ()

runStateIO :: forall s effs a. LastMember IO effs => s -> Eff '[] (State s ': effs) a -> Eff '[] effs (a, s)
runStateIO s0 m = do
  ref <- liftIO $ newIORef s0
  a <- m & interpret \case
    Get -> liftIO $ readIORef ref
    Put s' -> liftIO $ writeIORef ref s'
  s' <- liftIO $ readIORef ref
  pure (a,s')


-- | Handler for 'State' effects.
runStateRec :: forall s effs eh a. s -> Eff eh (State s ': effs) a -> Eff eh effs a
runStateRec s0 = interpretRecKS @_ @'[] s0 $ \s x k -> case x of
  Get -> k s s
  Put s' -> k s' ()

-- | Run a 'State' effect, returning only the final state.
execState :: forall s effs a. s -> Eff '[] (State s ': effs) a -> Eff '[] effs s
execState s = fmap snd . runState s

-- | Run a State effect, discarding the final state.
evalState :: forall s effs a. s -> Eff '[] (State s ': effs) a -> Eff '[] effs a
evalState s = fmap fst . runState s

-- | An encapsulated State handler, for transactional semantics. The global
-- state is updated only if the 'transactionState' finished successfully.
--
-- GHC cannot infer the @s@ type parameter for this function, so it must be
-- specified explicitly with @TypeApplications@. Alternatively, it can be
-- specified by supplying a 'Proxy' to 'transactionState''.
transactionState
  :: forall s effs a
   . Member (State s) effs
  => Eff '[] effs a
  -> Eff '[] effs a
transactionState m = do
    s0 <- get @s
    (x, s) <- interposeKS s0 (\s x -> pure (x, s)) handle m
    put s
    pure x
  where
    handle :: s -> State s v -> (s -> Arr '[] effs v b) -> Eff '[] effs b
    handle s x k = case x of
      Get -> k s s
      Put s' -> k s' ()

-- | Like 'transactionState', but @s@ is specified by providing a 'Proxy'
-- instead of requiring @TypeApplications@.
transactionState'
  :: forall s effs a
   . Member (State s) effs
  => Proxy s
  -> Eff '[] effs a
  -> Eff '[] effs a
transactionState' _ = transactionState @s
{-# INLINE transactionState' #-}
