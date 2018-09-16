{-# OPTIONS_GHC -Wall #-}
{-# LANGUAGE CPP #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  ToySolver.Data.MIP
-- Copyright   :  (c) Masahiro Sakai 2011-2014
-- License     :  BSD-style
--
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  provisional
-- Portability :  non-portable
--
-- Mixed-Integer Programming Problems with some commmonly used extensions
--
-----------------------------------------------------------------------------
module ToySolver.Data.MIP
  ( module ToySolver.Data.MIP.Base
  , readFile
  , readLPFile
  , readMPSFile
  , parseLPString
  , parseMPSString
  , writeFile
  , writeLPFile
  , writeMPSFile
  , toLPString
  , toMPSString
  , ParseError (..)
  ) where

import Prelude hiding (readFile, writeFile)
import Control.Exception
import Data.Char
import Data.Scientific (Scientific)
import qualified Data.Text.Lazy as TL
import qualified Data.Text.Lazy.IO as TLIO
#if MIN_VERSION_megaparsec(6,0,0)
import Data.Void
#endif
import System.FilePath (takeExtension)
import System.IO hiding (readFile, writeFile)
import Text.Megaparsec

import ToySolver.Data.MIP.Base
import qualified ToySolver.Data.MIP.LPFile as LPFile
import qualified ToySolver.Data.MIP.MPSFile as MPSFile

-- | Parse .lp or .mps file based on file extension
readFile :: FileOptions -> FilePath -> IO (Problem Scientific)
readFile opt fname =
  case map toLower (takeExtension fname) of
    ".lp"  -> readLPFile opt fname
    ".mps" -> readMPSFile opt fname
    ext -> ioError $ userError $ "unknown extension: " ++ ext

-- | Parse a file containing LP file data.
readLPFile :: FileOptions -> FilePath -> IO (Problem Scientific)
readLPFile = LPFile.parseFile

-- | Parse a file containing MPS file data.
readMPSFile :: FileOptions -> FilePath -> IO (Problem Scientific)
readMPSFile = MPSFile.parseFile

-- | Parse a string containing LP file data.
#if MIN_VERSION_megaparsec(6,0,0)
parseLPString :: FileOptions -> String -> String -> Either (ParseError Char Void) (Problem Scientific)
#elif MIN_VERSION_megaparsec(5,0,0)
parseLPString :: FileOptions -> String -> String -> Either (ParseError Char Dec) (Problem Scientific)
#else
parseLPString :: FileOptions -> String -> String -> Either ParseError (Problem Scientific)
#endif
parseLPString = LPFile.parseString

-- | Parse a string containing MPS file data.
#if MIN_VERSION_megaparsec(6,0,0)
parseMPSString :: FileOptions -> String -> String -> Either (ParseError Char Void) (Problem Scientific)
#elif MIN_VERSION_megaparsec(5,0,0)
parseMPSString :: FileOptions -> String -> String -> Either (ParseError Char Dec) (Problem Scientific)
#else
parseMPSString :: FileOptions -> String -> String -> Either ParseError (Problem Scientific)
#endif
parseMPSString = MPSFile.parseString

writeFile :: FileOptions -> FilePath -> Problem Scientific -> IO ()
writeFile opt fname prob =
  case map toLower (takeExtension fname) of
    ".lp"  -> writeLPFile opt fname prob
    ".mps" -> writeMPSFile opt fname prob
    ext -> ioError $ userError $ "unknown extension: " ++ ext

writeLPFile :: FileOptions -> FilePath -> Problem Scientific -> IO ()
writeLPFile opt fname prob =
  case LPFile.render opt prob of
    Left err -> ioError $ userError err
    Right s ->
      withFile fname WriteMode $ \h -> do
        case optFileEncoding opt of
          Nothing -> return ()
          Just enc -> hSetEncoding h enc
        TLIO.hPutStr h s

writeMPSFile :: FileOptions -> FilePath -> Problem Scientific -> IO ()
writeMPSFile opt fname prob =
  case MPSFile.render opt prob of
    Left err -> ioError $ userError err
    Right s ->
      withFile fname WriteMode $ \h -> do
        case optFileEncoding opt of
          Nothing -> return ()
          Just enc -> hSetEncoding h enc
        TLIO.hPutStr h s

toLPString :: FileOptions -> Problem Scientific -> Either String TL.Text
toLPString = LPFile.render

toMPSString :: FileOptions -> Problem Scientific -> Either String TL.Text
toMPSString = MPSFile.render
