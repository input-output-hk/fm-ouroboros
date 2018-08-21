{-# LANGUAGE RankNTypes #-}

module Ouroboros.Chi_Calculus.Process.DeltaQ (

    deltaQ

) where

import Prelude                        hiding (map)

import Control.Concurrent             (forkIO)
import Control.Concurrent.MVar        (MVar, newEmptyMVar, putMVar, takeMVar)
import Control.Monad                  (void)

import Data.Function                  (fix)
import Data.Functor.Const             (Const (Const, getConst))
import Data.Functor.Identity          (Identity (Identity, runIdentity))
import Data.List.FixedLength          (map)

import Numeric.Natural                (Natural)

import Ouroboros.Chi_Calculus.DeltaQ  (DeltaQ)
import Ouroboros.Chi_Calculus.Process (Interpretation, Process (..))

deltaQ :: Interpretation (Const Natural) Identity (IO ())
deltaQ dataInter = undefined
{-
worker

    where

    worker Stop                 = return ()
    worker (Send chan _ val)    = putMVar chan (runIdentity (dataInter val))
    worker (Receive chan cont)  = takeMVar chan >>= worker . cont . Identity
    worker (Parallel prc1 prc2) = do
                                      finishedVar1 <- newEmptyMVar
                                      finishedVar2 <- newEmptyMVar
                                      void $ forkIO $ do
                                          worker prc1
                                          putMVar finishedVar1 ()
                                      void $ forkIO $ do
                                          worker prc2
                                          putMVar finishedVar2 ()
                                      takeMVar finishedVar1
                                      takeMVar finishedVar2
    worker (NewChannel cont)    = newEmptyMVar >>= worker . cont
    worker (Var meaning)        = meaning
    worker (Letrec defs res)    = worker (res (fix (map worker . defs)))
    -}
