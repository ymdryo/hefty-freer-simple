{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

-- |
-- Module:       Data.OpenUnion
-- Description:  Open unions (type-indexed co-products) for extensible effects.
-- Copyright:    (c) 2016 Allele Dev; 2017 Ixperta Solutions s.r.o.; 2017 Alexis King
-- License:      BSD3
-- Maintainer:   Alexis King <lexi.lambda@gmail.com>
-- Stability:    experimental
-- Portability:  GHC specific language extensions.
--
-- Open unions (type-indexed co-products, i.e. type-indexed sums) for
-- extensible effects All operations are constant-time.
module Data.OpenUnion
  ( -- * Open Union
    Union

    -- * Open Union Operations
  , weakens
  , (:++:)
  , decomp
  , weaken
  , extract

    -- * Open Union Membership Constraints
  , Member(..)
  , Members
  , LastMember
  , UnionH
  , weakensH
  , decompH
  , weakenH
  , extractH

    -- * Open Union Membership Constraints
  , MemberH(..)
  , MembersH
  , hfmapUnion
  , HFunctor (..)
  , exhaust, exhaustH
  , KnownLen
  ) where

import Data.Kind (Constraint)

import Data.OpenUnion.Internal
  ( Member(inj, prj)
  , Union
  , weakens
  , (:++:)
  , decomp
  , extract
  , weaken
  , MemberH(injH, prjH)
  , UnionH
  , weakensH
  , decompH
  , extractH
  , weakenH
  , hfmapUnion
  , HFunctor (hfmap)
  , exhaust, exhaustH
  , KnownLen
  )

-- | A shorthand constraint that represents a combination of multiple 'Member'
-- constraints. That is, the following 'Members' constraint:
--
-- @
-- 'Members' '[Foo, Bar, Baz] effs
-- @
--
-- …is equivalent to the following set of 'Member' constraints:
--
-- @
-- ('Member' Foo effs, 'Member' Bar effs, 'Member' baz effs)
-- @
--
-- Note that, since each effect is translated into a separate 'Member'
-- constraint, the order of the effects does /not/ matter.
type family Members effs effs' :: Constraint where
  Members (eff ': effs) effs' = (Member eff effs', Members effs effs')
  Members '[] effs' = ()

-- | A shorthand constraint that represents a combination of multiple 'Member'
-- constraints. That is, the following 'Members' constraint:
--
-- @
-- 'Members' '[Foo, Bar, Baz] effs
-- @
--
-- …is equivalent to the following set of 'Member' constraints:
--
-- @
-- ('Member' Foo effs, 'Member' Bar effs, 'Member' baz effs)
-- @
--
-- Note that, since each effect is translated into a separate 'Member'
-- constraint, the order of the effects does /not/ matter.
type family MembersH effs effs' :: Constraint where
  MembersH (eff ': effs) effs' = (MemberH eff effs', MembersH effs effs')
  MembersH '[] effs' = ()

-- | Like 'Member', @'LastMember' eff effs@ is a constraint that requires that
-- @eff@ is in the type-level list @effs@. However, /unlike/ 'Member',
-- 'LastMember' requires @m@ be the __final__ effect in @effs@.
--
-- Generally, this is not especially useful, since it is preferable for
-- computations to be agnostic to the order of effects, but it is quite useful
-- in combination with 'Control.Monad.Freer.sendM' or
-- 'Control.Monad.Base.liftBase' to embed ordinary monadic effects within an
-- 'Control.Monad.Freer.Eff' computation.
class Member m effs => LastMember m effs | effs -> m
instance {-# OVERLAPPABLE #-} LastMember m effs => LastMember m (eff ': effs)
instance LastMember m (m ': '[])
