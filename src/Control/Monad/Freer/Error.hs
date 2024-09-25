-- |
-- Module:       Control.Monad.Freer.Error
-- Description:  An Error effect and handler.
-- Copyright:    (c) 2016 Allele Dev; 2017 Ixperta Solutions s.r.o.; 2017 Alexis King
-- License:      BSD3
-- Maintainer:   Alexis King <lexi.lambda@gmail.com>
-- Stability:    experimental
-- Portability:  GHC specific language extensions.
--
-- Composable handler for Error effects. Communicates success\/failure via an
-- 'Either' type.
--
-- Using <http://okmij.org/ftp/Haskell/extensible/Eff1.hs> as a starting point.
module Control.Monad.Freer.Error
  ( Error(..)
  , throwError
  , runError
  , catchError
  , handleError
  , runCatch
  , Catch(..)
  ) where

import Control.Monad.Freer (Eff, Member, interposeWith, interpretWith, send, interpretK, interpretRecH, HFunctor, hfmap)
import Control.Natural (type (~>))

-- | Exceptions of the type @e :: *@ with no resumption.
newtype Error e r where
  Error :: e -> Error e r

-- | Throws an error carrying information of type @e :: *@.
throwError :: forall e effs eh a. Member (Error e) effs => e -> Eff eh effs a
throwError e = send (Error e)

-- | Handler for exception effects. If there are no exceptions thrown, returns
-- 'Right'. If exceptions are thrown and not handled, returns 'Left', while
-- interrupting the execution of any other effect handlers.
runError :: forall e effs a. Eff '[] (Error e ': effs) a -> Eff '[] effs (Either e a)
runError = interpretK @_ @'[] (pure . Right) (\(Error e) _ -> pure (Left e))

-- | A catcher for Exceptions. Handlers are allowed to rethrow exceptions.
catchError
  :: forall e effs a
   . Member (Error e) effs
  => Eff '[] effs a
  -> (e -> Eff '[] effs a)
  -> Eff '[] effs a
catchError m handle = interposeWith (\(Error e) _ -> handle e) m

-- | A catcher for Exceptions. Handlers are /not/ allowed to rethrow exceptions.
handleError
  :: forall e effs a
   . Eff '[] (Error e ': effs) a
  -> (e -> Eff '[] effs a)
  -> Eff '[] effs a
handleError m handle = interpretWith (\(Error e) _ -> handle e) m

data Catch e m r where
    Catch :: m a -> (e -> m a) -> Catch e m a

instance HFunctor (Catch e) where
    hfmap f (Catch m hdl) = Catch (f m) (f . hdl)
    {-# INLINE hfmap #-}

runCatch :: forall e ef. Member (Error e) ef => Eff '[Catch e] ef ~> Eff '[] ef
runCatch = interpretRecH $ \(Catch m hdl) -> catchError m hdl
