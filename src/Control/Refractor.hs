{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# OPTIONS_GHC -Wno-partial-type-signatures #-}
module Control.Refractor
  ( Lens, Iso,
    lens, iso,
    gets, get, set, modify,
    toListOf, foldrOf, foldlOf, mapAccumLOf, mapAccumROf,
    fstL, sndL, swapL, unitL, constL
  ) where

import Prelude hiding (Functor (..), id, map)

import Control.Applicative
import Control.Applicative.Backwards (Backwards (..))
import Control.Categorical.Functor
import Control.Category
import Control.Category.Dual
import Control.Category.Unicode
import Control.Monad.Trans.State (State, state, runState)
import Data.Functor.Identity
import qualified Data.Monoid as Monoid (Dual (..))
import Data.Morphism.Endo
import Data.Profunctor
import Data.Proxy
import Data.Tuple (swap)

type Refractor s t f α β a b = s a (f b) -> t α (f β)

type Lens s t α β a b = ∀ f . Functor s t f => Refractor s t f α β a b

type Iso σ τ s t α β a b = ∀ p f . (Functor (Dual σ) (NT (->)) p, ∀ x . Functor s (->) (p x), Functor τ s f) => Refractor p p f α β a b

lens :: (α -> a) → (b → α → β) → Lens (->) (->) α β a b
lens get set ret = liftA2 map (flip set) (ret ∘ get)

iso :: ∀ σ τ s t α β a b . Proxy s -> σ α a → τ b β → Iso σ τ s t α β a b
iso _ f g = map (map g :: s _ _) ∘ nt (map (Dual f))

get :: ((a → Const a b) → α → Const a β) → α → a
get l = gets l id

gets :: ((a -> Const c b) -> α -> Const c β) -> (a -> c) -> α -> c
gets l f = getConst ∘ l (Const ∘ f)

set :: ((a → Identity b) → α → Identity β) → b → α → β
set l = modify l ∘ pure

modify :: ((a → Identity b) → α → Identity β) → (a → b) → α → β
modify l f = runIdentity ∘ l (Identity ∘ f)

-- foldOf :: Monoid a => Getting a α β a b -> α -> a
-- foldOf = get

-- foldMapOf :: Getting c α β a b -> (a -> c) -> α -> c
-- foldMapOf = gets

toListOf :: Getting (Endo (->) [a]) α β a b -> α -> [a]
toListOf l = foldrOf l (:) []

foldrOf :: Getting (Endo (->) c) α β a b -> (a -> c -> c) -> c -> α -> c
foldrOf l f z₀ = flip endo z₀ ∘ gets l (Endo ∘ f)

foldlOf :: Getting (Monoid.Dual (Endo (->) c)) α β a b -> (c -> a -> c) -> c -> α -> c
foldlOf l f z₀ = flip endo z₀ ∘ Monoid.getDual ∘ gets l (Monoid.Dual ∘ Endo ∘ flip f)

-- foldMapAccumOf :: Monoid c => ((a -> (c, b)) -> α -> (c, β)) -> (a -> (c, b)) -> α -> (c, β)
-- foldMapAccumOf = id

mapAccumROf :: ((a -> State c b) -> α -> State c β) -> (a -> c -> (c, b)) -> c -> α -> (c, β)
mapAccumROf l f z₀ = swap ∘ flip runState z₀ ∘ l (state ∘ (swap ∘) ∘ f)

mapAccumLOf :: ((a -> Backwards (State c) b) -> α -> Backwards (State c) β) -> (c -> a -> (c, b)) -> c -> α -> (c, β)
mapAccumLOf l f z₀ = swap ∘ flip runState z₀ ∘ forwards ∘ l (Backwards ∘ state ∘ (swap ∘) ∘ flip f)

type Getting r α β a b = (a -> Const r b) -> α -> Const r β

fstL :: Lens (->) (->) (a, c) (b, c) a b
fstL = swapL ∘ sndL

sndL :: Lens (->) (->) (a, b) (a, c) b c
sndL f = id *** f >>> uncurry (map ∘ (,))

swapL :: Iso (->) (->) (->) (->) (a, b) (c, d) (b, a) (d, c)
swapL = iso (Proxy :: Proxy (->)) swap swap

unitL :: Lens (->) (->) α α () ()
unitL = lens (pure ()) (\ () -> id)

constL :: Iso (->) (->) (->) (->) (Const a α) (Const b β) a b
constL = iso (Proxy :: Proxy (->)) getConst Const
