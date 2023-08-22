{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE OverloadedLists #-}
{-# LANGUAGE RecordWildCards #-}
module Main where

import Control.Lens
import Data.Data
import Data.List.NonEmpty (NonEmpty)
--import Data.Loc
import Data.Monoid
import qualified Data.Set as Set
import Data.Typeable
import Relude (one)

main :: IO ()
main = sequence_ $ map (putStrLn . show) [ example1, example2, example3, example4, example5 ]

----------------------------------------------------------------------
-- Rules

ruleSet :: SemanticInformation -> ExpRule
ruleSet SemanticInformation{..} = simpleRule
  where
    simpleRule :: ExpRule
    simpleRule (CallMethod (ClassName "javax.crypto.Cipher") "getInstance" [ExpValue arg])
      | Unknown `elem` arg = one "maybe unsafe"
      | StringLiteral "DES/ECB/NoPadding" `elem` arg =
          one "unsafe"
    simpleRule (CallMethod cls@(ClassName className) method _)
      | deprecatedMethod cls method =
          one $ "call to deprecated method: " <> className <> "." <> method
    -- .... more rules
    simpleRule _ = mempty

----------------------------------------------------------------------
-- Simple program (control flow graph) and AST

type Program e = [Stmt e]

data Stmt e = Assign Loc LValue e
            | StmtExp Loc e             -- ^ Statement evaluated for its side-effect
            | StmtLabel Loc Label
            | Jump Loc Label
              deriving (Show, Eq, Foldable)

data LValue = LValueVar Ident
              deriving (Show, Eq)

type Ident = String

type Label = Int

type Loc = Int

data Exp = CallMethod ClassDesc MethodName [Exp]
         | Add Exp Exp
         | Sub Exp Exp
         | ExpValue (NonEmpty Value)   -- ^ one (or more possible values)
           deriving (Show, Eq)

data ClassDesc = ClassName String
                 deriving (Show, Eq)

type MethodName = Ident

-- | Explicit or derived value(s).
data Value = Unknown
           | StringLiteral String
           | IntLiteral Int
             deriving (Show, Eq)

----------------------------------------------------------------------
-- apply the rules on a program

type ExpRule = Exp -> [String]

applyRules :: Program Exp -> [String]
applyRules p = foldMapOf (folded . folded) (ruleSet sem) p
  where
    sem = SemanticInformation{..}
    deprecatedMethod (ClassName className) methodName =
      Set.member (className, methodName) deprecatedMethods

    deprecatedMethods = Set.fromList [ ("java.core", "useRust")
                                     ]

----------------------------------------------------------------------
-- semantic information

data SemanticInformation = SemanticInformation {
    deprecatedMethod :: ClassDesc -> MethodName -> Bool
}

----------------------------------------------------------------------
-- example input

example1 = applyRules [ Jump 0 1
                      , StmtExp 1 (CallMethod (ClassName "javax.crypto.Cipher") "getInstance" [ExpValue (one (StringLiteral "DES/ECB/NoPadding"))])
                      ]

example2 = applyRules [ Jump 0 1
                      , StmtExp 1 (CallMethod (ClassName "javax.crypto.Cipher") "getInstance" [ExpValue (one (StringLiteral "foo"))])
                      ]

example3 = applyRules [ Jump 0 1
                      , StmtExp 1 (CallMethod (ClassName "javax.crypto.Cipher") "getInstance" [ExpValue (one Unknown)])
                      ]

example4 = applyRules [ Jump 0 1
                      , StmtExp 1 (CallMethod (ClassName "javax.crypto.Cipher") "getInstance" [ExpValue (one Unknown)])
                      , Jump 2 3, StmtExp 1 (CallMethod (ClassName "javax.crypto.Cipher") "getInstance" [ExpValue (one (StringLiteral "DES/ECB/NoPadding"))])
                      ]

example5 = applyRules [ Jump 0 1
                      , StmtExp 1 (CallMethod (ClassName "java.core") "useRust" [ExpValue (one Unknown)])
                      , StmtExp 1 (CallMethod (ClassName "javax.crypto.Cipher") "getInstance" [ExpValue (one Unknown)])
                      ]
