{-# LANGUAGE TemplateHaskell #-}
module Main where

import Test.Hspec
import Test.QuickCheck
import Test.QuickCheck.All

import qualified Semant
import qualified Syntax
import qualified Types

-- prop_len xs = len xs == len $ reverse xs

return [] -- need this for GHC 7.8
-- quickCheckAll generates test cases for all 'prop_*' properties
-- main = $(quickCheckAll)
main = hspec $ do
  Syntax.specs
  Semant.substSpecs
