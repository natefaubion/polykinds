{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module PolyKinds.StateExcM where

import Control.Monad.Except (MonadError, catchError, throwError)
import Control.Monad.State (MonadState, state)

newtype StateExcM e s a = StateExcM (forall r. s -> (s -> e -> r) -> (s -> a -> r) -> r)

{-# INLINE runStateExcM #-}
runStateExcM :: s -> StateExcM e s a -> (Either e a, s)
runStateExcM s (StateExcM k) = k s (\s' e -> (Left e, s')) (\s' a -> (Right a, s'))

instance Functor (StateExcM e s) where
  {-# INLINE fmap #-}
  fmap f (StateExcM k) = StateExcM $ \(!s) ke ks ->
    k s ke $ \(!s') a ->
      ks s' (f a)

instance Applicative (StateExcM e s) where
  {-# INLINE pure #-}
  pure = return

  {-# INLINE (<*>) #-}
  StateExcM k1 <*> StateExcM k2 = StateExcM $ \(!s) ke ks ->
    k1 s ke $ \(!s') f ->
      k2 s' ke $ \(!s'') a ->
        ks s'' (f a)

instance Monad (StateExcM e s) where
  {-# INLINE return #-}
  return a = StateExcM $ \(!s) _ ks -> ks s a

  {-# INLINE (>>=) #-}
  StateExcM k1 >>= k2 = StateExcM $ \(!s) ke ks ->
    k1 s ke $ \(!s') a ->
      let StateExcM k3 = k2 a in k3 s' ke ks

instance MonadState s (StateExcM e s) where
  {-# INLINE state #-}
  state k = StateExcM $ \(!s) _ ks ->
    let (a, !s') = k s in ks s' a

instance MonadError e (StateExcM e s) where
  {-# INLINE throwError #-}
  throwError e = StateExcM $ \s ke _ -> ke s e

  {-# INLINE catchError #-}
  StateExcM k1 `catchError` k2 = StateExcM $ \(!s) ke ks ->
    flip (k1 s) ks $ \(!s') e ->
      let StateExcM k3 = k2 e in k3 s' ke ks
