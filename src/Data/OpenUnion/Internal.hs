{-# OPTIONS_GHC -Wno-redundant-constraints #-} -- Due to use of TypeError.
{-# OPTIONS_HADDOCK not-home #-}

{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

-- |
-- Module:       Data.OpenUnion.Internal
-- Description:  Open unions (type-indexed co-products) for extensible effects.
--
-- Copyright:    (c) 2016 Allele Dev; 2017 Ixperta Solutions s.r.o.; 2017 Alexis King
-- License:      BSD3
-- Maintainer:   Alexis King <lexi.lambda@gmail.com>
-- Stability:    experimental
-- Portability:  GHC specific language extensions.
--
-- These are internal definitions and should be used with caution. There are no
-- guarantees that the API of this module will be preserved between minor
-- versions of this package.
--
-- Open unions (type-indexed co-products, i.e. type-indexed sums) for
-- extensible effects All operations are constant-time.
--
-- Based on
-- <http://okmij.org/ftp/Haskell/extensible/OpenUnion51.hs OpenUnion51.hs>.
--
-- Type-list @r :: [* -> *]@ of open union components is a small Universe.
-- Therefore, we can use a @Typeable@-like evidence in that universe. In our
-- case a simple index of an element in the type-list is sufficient
-- substitution for @Typeable@.
module Data.OpenUnion.Internal where

import Data.Kind (Type)
import GHC.TypeLits (TypeError, ErrorMessage(..))
import Unsafe.Coerce (unsafeCoerce)
import Control.Natural (type (~>))

type EffectF = Type -> Type
type EffectH = (Type -> Type) -> EffectF

-- | Open union is a strong sum (existential with an evidence).
data Union (r :: [EffectF]) a where
  Union :: {-# UNPACK #-} !Word -> t a -> Union r a

data UnionH (r :: [EffectH]) (m :: Type -> Type) a where
  UnionH :: {-# UNPACK #-} !Word -> t n a -> (forall x. n x -> m x) -> UnionH r m a

hfmapUnion :: (forall x. m x -> n x) -> UnionH r m a -> UnionH r n a
hfmapUnion f (UnionH n a koi) = UnionH n a (f . koi)
{-# INLINE hfmapUnion #-}

-- | Takes a request of type @t :: * -> *@, and injects it into the 'Union'.
--
-- Summand is assigning a specified 'Word' value, which is a position in the
-- type-list @(t ': r) :: * -> *@.
--
-- __This function is unsafe.__
--
-- /O(1)/
unsafeInj :: Word -> t a -> Union r a
unsafeInj = Union
{-# INLINE unsafeInj #-}

-- | Project a value of type @'Union' (t ': r) :: * -> *@ into a possible
-- summand of the type @t :: * -> *@. 'Nothing' means that @t :: * -> *@ is not
-- the value stored in the @'Union' (t ': r) :: * -> *@.
--
-- It is assumed that summand is stored in the 'Union' when the 'Word' value is
-- the same value as is stored in the 'Union'.
--
-- __This function is unsafe.__
--
-- /O(1)/
unsafePrj :: Word -> Union r a -> Maybe (t a)
unsafePrj n (Union n' x)
  | n == n'   = Just (unsafeCoerce x)
  | otherwise = Nothing
{-# INLINE unsafePrj #-}

unsafeInjH :: Word -> t m a -> UnionH r m a
unsafeInjH n a = UnionH n a id
{-# INLINE unsafeInjH #-}

unsafePrjH :: HFunctor t => Word -> UnionH r m a -> Maybe (t m a)
unsafePrjH n (UnionH n' x f)
  | n == n'   = Just (hfmap f $ unsafeCoerce x)
  | otherwise = Nothing
{-# INLINE unsafePrjH #-}

-- | Represents position of element @t :: * -> *@ in a type list
-- @r :: [* -> *]@.
newtype P (t :: k) (r :: [k]) = P {unP :: Word}

-- | Find an index of an element @t :: * -> *@ in a type list @r :: [* -> *]@.
-- The element must exist. The @w :: [* -> *]@ type represents the entire list,
-- prior to recursion, and it is used to produce better type errors.
--
-- This is essentially a compile-time computation without run-time overhead.
class FindElem (t :: k) (r :: [k]) where
  -- | Position of the element @t :: * -> *@ in a type list @r :: [* -> *]@.
  --
  -- Position is computed during compilation, i.e. there is no run-time
  -- overhead.
  --
  -- /O(1)/
  elemNo :: P t r

-- | Base case; element is at the current position in the list.
instance FindElem t (t ': r) where
  elemNo = P 0

-- | Recursion; element is not at the current position, but is somewhere in the
-- list.
instance {-# OVERLAPPABLE #-} FindElem t r => FindElem t (t' ': r) where
  elemNo = P $ 1 + unP (elemNo :: P t r)

-- | Instance resolution for this class fails with a custom type error
-- if @t :: * -> *@ is not in the list @r :: [* -> *]@.
class IfNotFound (t :: k) (r :: [k]) (w :: [k])

-- | If we reach an empty list, that’s a failure, since it means the type isn’t
-- in the list. For GHC >=8, we can render a custom type error that explicitly
-- states what went wrong.
instance TypeError ('Text "‘" ':<>: 'ShowType t
                    ':<>: 'Text "’ is not a member of the type-level list"
                    ':$$: 'Text "  ‘" ':<>: 'ShowType w ':<>: 'Text "’"
                    ':$$: 'Text "In the constraint ("
                    ':<>: 'ShowType (Member t w) ':<>: 'Text ")")
    => IfNotFound t '[] w

-- | If we reach an empty list, that’s a failure, since it means the type isn’t
-- in the list. For GHC >=8, we can render a custom type error that explicitly
-- states what went wrong.
instance TypeError ('Text "‘" ':<>: 'ShowType t
                    ':<>: 'Text "’ is not a member of the type-level list"
                    ':$$: 'Text "  ‘" ':<>: 'ShowType w ':<>: 'Text "’"
                    ':$$: 'Text "In the constraint ("
                    ':<>: 'ShowType (MemberH t w) ':<>: 'Text ")")
    => IfNotFound t '[] w

instance IfNotFound t (t ': r) w
instance {-# OVERLAPPABLE #-} IfNotFound t r w => IfNotFound t (t' ': r) w

-- | Pass if @r@ is uninstantiated. The incoherence here is safe, since picking
-- this instance doesn’t cause any variation in behavior, except possibly the
-- production of an inferior error message. For more information, see
-- lexi-lambda/freer-simple#3, which describes the motivation in more detail.
instance {-# INCOHERENT #-} IfNotFound t r w

-- | A constraint that requires that a particular effect, @eff@, is a member of
-- the type-level list @effs@. This is used to parameterize an
-- 'Control.Monad.Freer.Eff' computation over an arbitrary list of effects, so
-- long as @eff@ is /somewhere/ in the list.
--
-- For example, a computation that only needs access to a cell of mutable state
-- containing an 'Integer' would likely use the following type:
--
-- @
-- 'Member' ('Control.Monad.Freer.State.State' 'Integer') effs => 'Control.Monad.Freer.Eff' effs ()
-- @
class FindElem eff effs => Member (eff :: EffectF) effs where
  -- This type class is used for two following purposes:
  --
  -- * As a @Constraint@ it guarantees that @t :: * -> *@ is a member of a
  --   type-list @r :: [* -> *]@.
  --
  -- * Provides a way how to inject\/project @t :: * -> *@ into\/from a 'Union',
  --   respectively.
  --
  -- Following law has to hold:
  --
  -- @
  -- 'prj' . 'inj' === 'Just'
  -- @

  -- | Takes a request of type @t :: * -> *@, and injects it into the
  -- 'Union'.
  --
  -- /O(1)/
  inj :: eff a -> Union effs a

  -- | Project a value of type @'Union' (t ': r) :: * -> *@ into a possible
  -- summand of the type @t :: * -> *@. 'Nothing' means that @t :: * -> *@ is
  -- not the value stored in the @'Union' (t ': r) :: * -> *@.
  --
  -- /O(1)/
  prj :: Union effs a -> Maybe (eff a)

instance (FindElem t r, IfNotFound t r r) => Member t r where
  inj = unsafeInj $ unP (elemNo :: P t r)
  {-# INLINE inj #-}

  prj = unsafePrj $ unP (elemNo :: P t r)
  {-# INLINE prj #-}

class FindElem eff effs => MemberH (eff :: EffectH) effs where
  injH :: HFunctor eff => eff m a -> UnionH effs m a
  prjH :: HFunctor eff => UnionH effs m a -> Maybe (eff m a)

class HFunctor eff where
    hfmap :: (f ~> g) -> eff f a -> eff g a

instance (FindElem t r, IfNotFound t r r) => MemberH t r where
  injH = unsafeInjH $ unP (elemNo :: P t r)
  {-# INLINE injH #-}

  prjH = unsafePrjH $ unP (elemNo :: P t r)
  {-# INLINE prjH #-}

-- | Orthogonal decomposition of a @'Union' (t ': r) :: * -> *@. 'Right' value
-- is returned if the @'Union' (t ': r) :: * -> *@ contains @t :: * -> *@, and
-- 'Left' when it doesn't. Notice that 'Left' value contains
-- @Union r :: * -> *@, i.e. it can not contain @t :: * -> *@.
--
-- /O(1)/
decomp :: Union (t ': r) a -> Either (Union r a) (t a)
decomp (Union 0 a) = Right $ unsafeCoerce a
decomp (Union n a) = Left  $ Union (n - 1) a
{-# INLINE [2] decomp #-}

-- | Specialized version of 'decomp' for efficiency.
--
-- /O(1)/
--
-- TODO: Check that it actually adds on efficiency.
decomp0 :: Union '[t] a -> Either (Union '[] a) (t a)
decomp0 (Union _ a) = Right $ unsafeCoerce a
{-# INLINE decomp0 #-}
{-# RULES "decomp/singleton"  decomp = decomp0 #-}

-- | Specialised version of 'prj'\/'decomp' that works on an
-- @'Union' '[t] :: * -> *@ which contains only one specific summand. Hence the
-- absence of 'Maybe', and 'Either'.
--
-- /O(1)/
extract :: Union '[t] a -> t a
extract (Union _ a) = unsafeCoerce a
{-# INLINE extract #-}

-- | Inject whole @'Union' r@ into a weaker @'Union' (any ': r)@ that has one
-- more summand.
--
-- /O(1)/
weaken :: Union r a -> Union (any ': r) a
weaken (Union n a) = Union (n + 1) a
{-# INLINE weaken #-}

exhaust :: Union '[] a -> r
exhaust _ = error "unreachable"
{-# INLINE exhaust #-}

exhaustH :: UnionH '[] m a -> r
exhaustH _ = error "unreachable"
{-# INLINE exhaustH #-}

infixr 5 :++:
type family xs :++: ys where
  '[] :++: ys = ys
  (x ': xs) :++: ys = x ': (xs :++: ys)

weakens :: forall q r a. KnownLen q => Union r a -> Union (q :++: r) a
weakens (Union n a) = Union (n + reifyLen @_ @q) a
{-# INLINE weakens #-}

-- | Orthogonal decomposition of a @'Union' (t ': r) :: * -> *@. 'Right' value
-- is returned if the @'Union' (t ': r) :: * -> *@ contains @t :: * -> *@, and
-- 'Left' when it doesn't. Notice that 'Left' value contains
-- @Union r :: * -> *@, i.e. it can not contain @t :: * -> *@.
--
-- /O(1)/
decompH :: HFunctor t => UnionH (t ': r) m a -> Either (UnionH r m a) (t m a)
decompH (UnionH 0 a koi) = Right $ hfmap koi $ unsafeCoerce a
decompH (UnionH n a koi) = Left  $ UnionH (n - 1) a koi
{-# INLINE [2] decompH #-}

-- | Specialized version of 'decomp' for efficiency.
--
-- /O(1)/
--
-- TODO: Check that it actually adds on efficiency.
decomp0H :: HFunctor t => UnionH '[t] m a -> Either (UnionH '[] m a) (t m a)
decomp0H (UnionH _ a koi) = Right $ hfmap koi $ unsafeCoerce a
{-# INLINE decomp0H #-}
{-# RULES "decomp/singleton"  decompH = decomp0H #-}

-- | Specialised version of 'prj'\/'decomp' that works on an
-- @'Union' '[t] :: * -> *@ which contains only one specific summand. Hence the
-- absence of 'Maybe', and 'Either'.
--
-- /O(1)/
extractH :: HFunctor t => UnionH '[t] m a -> t m a
extractH (UnionH _ a koi) = hfmap koi $ unsafeCoerce a
{-# INLINE extractH #-}

-- | Inject whole @'Union' r@ into a weaker @'Union' (any ': r)@ that has one
-- more summand.
--
-- /O(1)/
weakenH :: UnionH r m a -> UnionH (any ': r) m a
weakenH (UnionH n a koi) = UnionH (n + 1) a koi
{-# INLINE weakenH #-}

weakensH :: forall q r m a. KnownLen q => UnionH r m a -> UnionH (q :++: r) m a
weakensH (UnionH n a koi) = UnionH (n + reifyLen @_ @q) a koi
{-# INLINE weakensH #-}

-- from speff
class KnownLen (es :: [k]) where
  -- | Get the length of the list.
  reifyLen :: Word

instance KnownLen '[] where
  reifyLen = 0

instance KnownLen es => KnownLen (e ': es) where
  reifyLen = 1 + reifyLen @_ @es
