{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE ViewPatterns #-}
module Combinator where

import Control.Lens hiding (Empty)
import Control.Monad.Trans.State.Lazy
import Data.Graph.Inductive hiding (Context, (&))
import qualified Data.Graph.Inductive as G
import Data.Graph.Inductive.PatriciaTree
import Data.List
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe
import Data.Sequence (Seq(..))
import Relude (one, fromList)

----------------------------------------------------------------------
--
-- Contexts

data EnvContext = EnvContext {
    _bindings :: Map Ident Exp
  , _progContext :: ProgramContext
  , _tentativeFinding :: Maybe Finding
}

data ProgramContext = ProgramContext {
    _cfg :: CFG
  -- ^ The whole context graph, may be narrowed, e.g. to a single function.
  , _contextNode :: Node
  -- ^ Key of the current node in the graph
  , _block :: Block
  -- ^ current block, mid statements consumed to indicate statements ahead
}

data MatchResult = MatchPositive | NoMatch | MatchWithFinding Finding
                   deriving (Eq, Show)

type RuleM = StateT EnvContext (State ProgramContext)

-- Signal a match, to be applied
type ExpMatcher = Stmt -> RuleM [Finding]

type ExpMatcher2 = Stmt -> State EnvContext MatchResult

{-
ExpMatcher is applied in blocks to find interesting anchor positions, it can adjust
the context and give a handler (function that may be based on combinators) that
describes further matches that needs to be explored.

Note: If the match is enough, it still needs a function:
-}

-- | The control flow graph
type CFG = Gr Block EdgeLabel

data EdgeLabel = NextBlock | ExitToCaller

data Finding = Finding {
    message :: String,
    pos :: Pos
} deriving (Eq, Show)

type Pos = Int

type Label = Int

data Context

data Block = Block Label [Stmt] Exit
             deriving Show

type Exit = Stmt

data Stmt = Assign Pos Ident Exp
          | StmtExp Exp

          -- Exit statements
          | Call Pos Class Method [Exp]
          | Jump Pos Label
          | JumpTrue Pos Exp Label Label  -- to fallThrough labels
             deriving (Eq, Ord, Show)

data Exp = IntValue Int
         | StringValue String
         | Add Exp Exp
         | Sub Exp Exp
         | Neg Exp
         | AnyExp                      -- for indexing
           deriving (Eq, Ord, Show)

data Ident = Ident String
           | IdentAny                  -- for indexing
             deriving (Eq, Ord, Show)

data Class = Class String
             deriving (Eq, Ord, Show)

data Method = Method String
              deriving (Eq, Ord, Show)

makeLenses ''EnvContext
makeLenses ''ProgramContext

{-

So it can return  'matchHandler0 "unsafe crypto algorithm used"' and let matchHandler0
pick up the position and pack the output.

More elaborate handlers will describe other points using graph combinators, e.g.
withContext ctx (always inBlock anotherExpMatcher)

To search a block, can also be applied to same function or whole program.
The context can be

Traversals like this are expensive, it may make sense to apply a skeleton match
in a map lookup, so that one can quickly find potential matches.
- This requires some indexing operation (memoization?) to create the map if needed
- once found, we can refine it by 1) finding a path between the nodes, 2) thread the
  context through the path, if path and refined match (with updated context) still
  match, then it is a finding.

Such matcher could be a data DSL data structure

    MethodCall Class MethodName [Capture "arg1"]

The map key can be a function which relaces Capture with WildCard, so that we
can apply it in a subgraph (block, function, group of functions, all program)
to find positions that match.

Then prove PathExists, and use the match expression with Capture in place and
refine the match using Context (updated along (threaded through) path).

Another thing is reachability, returns should be edges back to a caller
node so we can following it past return from the function.
I am not sure reachability closure from a given point, block or function
is worthwhile to base it on. It is better than 'whole program' but there
be more than one and it may be almost as large in reality.

-}


-- bfsWithPred (node list ordered by distance)
--
type MatchContext = G.Context Block EdgeLabel -> Maybe (G.Context Block EdgeLabel)

bfsWithPred :: MatchContext -> ExpMatcher2 -> Seq (EnvContext, Node) -> CFG -> [MatchResult]
bfsWithPred f rm q g = go q g  where
  go Empty _ = []
  go _ g | isEmpty g = []
  go ((ctx, v) :<| q') g =
    case match v g of
      (Just (f -> Just c), g') -> case stepBlock rm ctx (lab' c) of
        (ctx', Just (_loc, MatchPositive)) ->
            MatchPositive : go (q' `mappend` (fromList (map (ctx',) (suc' c)))) g'
        (ctx', Nothing) ->
            NoMatch : go (q' `mappend` (fromList (map (ctx',) (suc' c)))) g'
      (_, g') ->
        -- this should be loop or already visited place
        go q' g'

stepBlock :: ExpMatcher2 -> EnvContext -> Block -> (EnvContext, Maybe (Block, MatchResult))
stepBlock rm ctx block = go ctx block
  where
    go ctx loc@(Block entry [] exit) = case evalState (rm exit) ctx of
      MatchPositive -> (ctx, Just (loc, MatchPositive))
      NoMatch -> ((updateContext ctx exit), Nothing)
    go ctx loc@(Block entry (stmt:stmts) exit) = case evalState (rm stmt) ctx of
      MatchPositive -> (ctx, Just (loc, MatchPositive))
      NoMatch -> go (updateContext ctx stmt) (Block entry stmts exit)

updateContext ctx StmtExp{} = ctx
updateContext ctx (Assign _ ident exp) = ctx & bindings%~Map.insert ident exp

----------------------------------------------------------------------
--
-- DSL support

-- | In a block means not follow edges to other blocks
inBlock :: G.Context a b -> Maybe c
inBlock = const Nothing

-- | In function means no following exit from function edges.
inFunction :: MatchContext
inFunction c
  | (_, ExitToCaller) : _ <- lsuc' c = Nothing
  | otherwise = Just c

followedBy :: RuleKey
           -> MatchContext
           -> ExpMatcher2
           -> RuleM [Finding]
followedBy k f rm = StateT $ \ctx ->
  let accept = pure ([], ctx & tentativeFinding.~Nothing)
      report findings = pure (findings, ctx & tentativeFinding.~Nothing)
  in do
    pctx <- get
    case stepBlock rm ctx (pctx^.block) of
      (_, Just (loc, MatchPositive)) -> accept -- found a positive match
      (ctx, Nothing) ->
        case match (pctx^.contextNode) (pctx^.cfg) of
          (Just c, _) ->
            let matches = nub (bfsWithPred f rm (fromList (map (ctx,) (suc' c))) (pctx^.cfg))
            in handleMatchResult ctx matches accept report

-- One way to handle match results, this one expects all paths to have positive match
handleMatchResult ctx matches accept report
  | expectOnly MatchPositive matches = accept
  | fs@(_:_) <- matchedFindings matches = report fs
  | Just stored <- ctx^.tentativeFinding = report [stored]

-- | Expect all matches to be same
expectOnly what [match] = what == match
expectOnly _ _ = False

-- | Extract all findings from matches
matchedFindings :: [MatchResult] -> [Finding]
matchedFindings ms = mapMaybe f ms
  where f (MatchWithFinding x) = Just x
        f _ = Nothing

-- | Store a tentative finding for later use depending on traversal.
setTentativeFinding pos message =
  modify $ \s -> s & tentativeFinding.~Just (Finding { message = message
                                                     , pos = pos } )

----------------------------------------------------------------------
--
-- Indexing the graph

-- | A pattern key intended to describe a method call
anyCall = Call anyPos anyClass anyMethod anyParams

-- | Matching anything of a given kind
anyPos = 0
anyClass = Class ""
anyMethod = Method ""
anyParams = []
anyExp = AnyExp

type RuleKey = Stmt

----------------------------------------------------------------------
--
-- Rules example

rules :: ExpMatcher
rules stmt = case stmt of
    Call pos1 (Class "theClass") (Method "foo") [arg1] -> do
      setTentativeFinding pos1 "theClass.foo not followed by theClass.bar"
      followedBy anyCall inBlock $ \case
         Call pos2 (Class "theClass") (Method "bar") [arg2]
           | arg1 == arg2 -> pure MatchPositive
         _ -> pure NoMatch
