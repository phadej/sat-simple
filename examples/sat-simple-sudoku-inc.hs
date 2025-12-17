-- This example is the same as in @ersatz@
-- However
-- - we use different encoding.
-- - abuse Applicative/Traversable and symmetry of Sudoku
--   to avoid dealing with indices.
--
module Main (main) where

import Control.Applicative    (liftA2)
import Control.Monad          (when)
import Control.Monad.IO.Class (liftIO)
import Data.Foldable          (for_, toList, traverse_)

import Control.Monad.SAT

-------------------------------------------------------------------------------
-- Main
-------------------------------------------------------------------------------

main :: IO ()
main = do
    putStrLn "Problem:"
    putStr $ render initValues


    putStrLn "Solving..."
    sol <- runSAT $ do
        let stats = True

        m <- sudokuModel
        sudokuValues m initValues

        do
            sudokuRulesDigits m
            sol <- solve m
            liftIO $ do
                putStrLn "Initial guess:"
                putStr $ render $ decode sol

        do
            sudokuRulesRow m
            sol <- solve m
            liftIO $ do
                putStrLn "Adding row rules:"
                putStr $ render $ decode sol

        do
            sudokuRulesColumn m
            sol <- solve m
            liftIO $ do
                putStrLn "Adding column rules:"
                putStr $ render $ decode sol

        do
            sudokuRulesSub m
            sol <- solve m
            liftIO $ do
                putStrLn "Adding subsquare rules:"
                putStr $ render $ decode sol

        when stats $ do
            numberOfVariables >>= \n -> liftIO $ putStrLn $ "variables: " ++ show n
            numberOfClauses   >>= \n -> liftIO $ putStrLn $ "clauses:   " ++ show n

        simplify

        when stats $ do
            numberOfClauses   >>= \n -> liftIO $ putStrLn $ "clauses':  " ++ show n

        sol <- solve m

        when stats $ do
            numberOfLearnts   >>= \n -> liftIO $ putStrLn $ "learnts:   " ++ show n
            numberOfConflicts >>= \n -> liftIO $ putStrLn $ "conflicts: " ++ show n


        return sol

    putStrLn "Solution:"
    putStr $ render $ decode sol

-------------------------------------------------------------------------------
-- Initial values
-------------------------------------------------------------------------------

initValues :: Nine (Nine Int)
initValues = N9
    -- From https://en.wikipedia.org/w/index.php?title=Sudoku&oldid=543290082
    (N9 5 3 0 0 7 0 0 0 0)
    (N9 6 0 0 1 9 5 0 0 0)
    (N9 0 9 8 0 0 0 0 6 0)
    (N9 8 0 0 0 6 0 0 0 3)
    (N9 4 0 0 8 0 3 0 0 1)
    (N9 7 0 0 0 2 0 0 0 6)
    (N9 0 6 0 0 0 0 2 8 0)
    (N9 0 0 0 4 1 9 0 0 5)
    (N9 0 0 0 0 8 0 0 7 9)

-------------------------------------------------------------------------------
-- Rendering
-------------------------------------------------------------------------------

render :: Nine (Nine Int) -> String
render sol = unlines $ renderGroups top divider bottom $ fmap renderLine sol
  where
    top     = bar "┌" "───────" "┬" "┐"
    divider = bar "├" "───────" "┼" "┤"
    bottom  = bar "└" "───────" "┴" "┘"

    bar begin fill middle end = begin ++ fill ++ middle ++ fill ++ middle ++ fill ++ end

renderLine :: Nine Int -> String
renderLine sol = unwords $ renderGroups "│" "│" "│" $ fmap showN sol
  where
    showN n | 1 <= n && n <= 9 = show n
            | otherwise        = " "

renderGroups :: a -> a -> a -> Nine a -> [a]
renderGroups begin middle end (N (T xs ys zs)) =
    [begin] ++ toList xs ++ [middle] ++ toList ys ++ [middle] ++ toList zs ++ [end]

-------------------------------------------------------------------------------
-- Triple
-------------------------------------------------------------------------------

data Triple a = T a a a
  deriving (Functor, Foldable, Traversable)

instance Applicative Triple where
    pure x = T x x x
    T f g h <*> T x y z = T (f x) (g y) (h z)

newtype Nine a = N { unN :: Triple (Triple a) }
  deriving (Functor, Foldable, Traversable)

instance Applicative Nine where
    pure x = N (pure (pure x))
    N f <*> N x = N (liftA2 (<*>) f x)

pattern N9 :: a -> a -> a -> a -> a -> a -> a -> a -> a -> Nine a
pattern N9 a b c d e f g h i = N (T (T a b c) (T d e f) (T g h i))
{-# COMPLETE N9 #-}

-------------------------------------------------------------------------------
-- Sudoku model
-------------------------------------------------------------------------------

-- | Model is nine rows of nine columns of nine bits.
newtype Model a = M (Nine (Nine (Nine a)))
  deriving (Functor, Foldable, Traversable)

emptyModel :: Model ()
emptyModel = M $ pure $ pure $ pure ()

decode :: Model Bool -> Nine (Nine Int)
decode (M m) = fmap (fmap f) m where
    f :: Nine Bool -> Int
    f (N9 X _ _ _ _ _ _ _ _) = 1
    f (N9 _ X _ _ _ _ _ _ _) = 2
    f (N9 _ _ X _ _ _ _ _ _) = 3
    f (N9 _ _ _ X _ _ _ _ _) = 4
    f (N9 _ _ _ _ X _ _ _ _) = 5
    f (N9 _ _ _ _ _ X _ _ _) = 6
    f (N9 _ _ _ _ _ _ X _ _) = 7
    f (N9 _ _ _ _ _ _ _ X _) = 8
    f (N9 _ _ _ _ _ _ _ _ X) = 9
    f _ = 0

pattern X :: Bool
pattern X = True

-------------------------------------------------------------------------------
-- SAT rules
-------------------------------------------------------------------------------

-- | Populate model with the literals.
sudokuModel :: SAT s (Model (Lit s))
sudokuModel = traverse (\_ -> newLit) emptyModel

-- | Sudoku rules.
--
-- Add constraints of the puzzle.
_sudokuRules :: Model (Lit s) -> SAT s ()
_sudokuRules model = do
    sudokuRulesDigits model
    sudokuRulesRow model
    sudokuRulesColumn model
    sudokuRulesSub model

sudokuRulesDigits :: Model (Lit s) -> SAT s ()
sudokuRulesDigits model = do
    -- each "digit" is 1..9
    -- we encode digits using 9 bits.
    -- exactly one, i.e. at most one and and least one have to set.
    forDigit_ model $ \d -> do
        let lits = toList d
        assertAtMostOne lits
        assertAtLeastOne lits
    
-- With above digit encoding the sudoku rules are easy to encode:
-- For each row we should have at least one 1, at least one 2, ... 9
-- And similarly for columns and subsquares.
--
-- If we also require that each row, column and subsquare has at most one 1..9
-- the given problem becomes trivial, as is solved by initial unit propagation.

-- | each row
sudokuRulesRow :: Model (Lit s) -> SAT s ()
sudokuRulesRow model = do
    forRow_ model $ \block -> do
        let block' = sequenceA block
        for_ block' $ \d -> do
            let lits = toList d
            assertAtLeastOne lits
            -- assertAtMostOne lits
            
-- | each column
sudokuRulesColumn :: Model (Lit s) -> SAT s ()
sudokuRulesColumn model = do
    forColumn_ model $ \block -> do
        let block' = sequenceA block
        for_ block' $ \d -> do
            let lits = toList d
            assertAtLeastOne lits
            -- assertAtMostOne lits

-- | each subsquare
sudokuRulesSub :: Model (Lit s) -> SAT s ()
sudokuRulesSub model = do
    forSubSq_ model $ \block -> do
        let block' = sequenceA block
        for_ block' $ \d -> do
            let lits = toList d
            assertAtLeastOne lits
            -- assertAtMostOne lits

forDigit_ :: Applicative f => Model a -> (Nine a -> f b) -> f ()
forDigit_ (M m) f = traverse_ (traverse_ f) m

forRow_ :: Applicative f => Model a -> (Nine (Nine a) -> f b) -> f ()
forRow_ (M m) f = traverse_ f m

forColumn_ :: Applicative f => Model a -> (Nine (Nine a) -> f b) -> f ()
forColumn_ (M m) f = traverse_ f (sequenceA m)

forSubSq_ :: Applicative f => Model a -> (Nine (Nine a) -> f b) -> f ()
forSubSq_ (M m) f = traverse_ f $ fmap N $ N $ fmap sequenceA $ unN $ fmap unN m

-- | Add constraints of the initial setup.
sudokuValues :: Model (Lit s) -> Nine (Nine Int) -> SAT s ()
sudokuValues (M m) v = traverse_ sequenceA $ liftA2 (liftA2 f) m v
  where
    -- force the corresponding bit.
    f :: Nine (Lit s) -> Int -> SAT s ()
    f (N9 l _ _ _ _ _ _ _ _) 1 = addClause [l]
    f (N9 _ l _ _ _ _ _ _ _) 2 = addClause [l]
    f (N9 _ _ l _ _ _ _ _ _) 3 = addClause [l]
    f (N9 _ _ _ l _ _ _ _ _) 4 = addClause [l]
    f (N9 _ _ _ _ l _ _ _ _) 5 = addClause [l]
    f (N9 _ _ _ _ _ l _ _ _) 6 = addClause [l]
    f (N9 _ _ _ _ _ _ l _ _) 7 = addClause [l]
    f (N9 _ _ _ _ _ _ _ l _) 8 = addClause [l]
    f (N9 _ _ _ _ _ _ _ _ l) 9 = addClause [l]

    f _ _ = return ()
