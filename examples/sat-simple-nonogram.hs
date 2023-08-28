module Main (main) where

import Control.Monad          (forM, forM_)
import Control.Monad.IO.Class (liftIO)
import Data.Functor.Compose   (Compose (..))
import Data.List              (nub)
import Data.Map               (Map)

import qualified Data.Map as Map

import Control.Monad.SAT

-------------------------------------------------------------------------------
-- Examples
-------------------------------------------------------------------------------

easyP :: ([[Int]], [[Int]])
easyP = ([[2], [1]], [[2],[1]])

-- | https://en.wikipedia.org/wiki/Nonogram#Example
problemP :: ([[Int]], [[Int]])
problemP = (rows, cols) where
    rows =
        [ []
        , [4]
        , [6]
        , [2,2]
        , [2,2]
        , [6]
        , [4]
        , [2]
        , [2]
        , [2]
        , []
        ]

    cols =
      [ []
      , [9]
      , [9]
      , [2,2]
      , [2,2]
      , [4]
      , [4]
      , []
      ]

-- | https://en.wikipedia.org/wiki/Nonogram#/media/File:Nonogram_wiki.svg
problemW :: ([[Int]], [[Int]])
problemW = (rows, cols) where
    rows =
        [ [8,7,5,7]
        , [5,4,3,3]
        , [3,3,2,3]
        , [4,3,2,2]
        , [3,3,2,2]
        , [3,4,2,2]
        , [4,5,2]
        , [3,5,1]
        , [4,3,2]
        , [3,4,2]
        , [4,4,2]
        , [3,6,2]
        , [3,2,3,1]
        , [4,3,4,2]
        , [3,2,3,2]
        , [6,5]
        , [4,5]
        , [3,3]
        , [3,3]
        , [1,1]
        ]

    cols =
        [ [1]
        , [1]
        , [2]
        , [4]
        , [7]
        , [9]
        , [2,8]
        , [1,8]
        , [8]
        , [1,9]
        , [2,7]
        , [3,4]
        , [6,4]
        , [8,5]
        , [1,11]
        , [1,7]
        , [8]
        , [1,4,8]
        , [6,8]
        , [4,7]
        , [2,4]
        , [1,4]
        , [5]
        , [1,4]
        , [1,5]
        , [7]
        , [5]
        , [3]
        , [1]
        , [1]
        ]


-------------------------------------------------------------------------------
-- Main
-------------------------------------------------------------------------------

main :: IO ()
main = do
    nonogram "Easy" easyP
    nonogram "Letter P" problemP
    nonogram "Letter W" problemW
  where
    nonogram name p = do
        putStrLn name
        solP <- uncurry solveNonogram p
        putStrLn $ render solP

-------------------------------------------------------------------------------
-- Render
-------------------------------------------------------------------------------

render :: [[Bool]] -> String
render sol = unlines
    [ map (\b -> if b then '*' else ' ') l
    | l <- sol
    ]

-------------------------------------------------------------------------------
-- Solve
-------------------------------------------------------------------------------

solveNonogram :: [[Int]] -> [[Int]] -> IO [[Bool]]
solveNonogram rows cols = runSAT $ do
    let lits' :: [[SAT s (Lit s)]]
        lits' = [ [ newLit | _ <- cols ] | _ <- rows ]

    -- create solution variables.
    Compose lits <- sequence (Compose lits')

    -- row constraints
    forM_ (zip rows lits) $ \(r, ls) -> do
        regexp r ls

    -- column constraints
    forM_ (zip cols (transpose lits)) $ \(r, ls) -> do
        regexp r ls

    numberOfVariables >>= \n -> liftIO $ putStrLn $ "variables: " ++ show n
    numberOfClauses   >>= \n -> liftIO $ putStrLn $ "clauses:   " ++ show n

    -- solve
    Compose sol <- solve (Compose lits)

    return sol

transpose:: [[a]] -> [[a]]
transpose ([]:_) = []
transpose x      = map head x : transpose (map tail x)

-------------------------------------------------------------------------------
-- NFA matching
-------------------------------------------------------------------------------

data RE a
    = Emp
    | Eps
    | Chr a
    | Rep (RE a)
    | App (RE a) (RE a)
    -- | Alt (RE a) (RE a)
  deriving (Eq, Ord, Show)

{-
alt :: RE a -> RE a -> RE a
alt Emp       s   = s
alt r         Emp = r
alt (Alt r t) s   = alt r (alt t s)
alt r         s   = Alt r s
-}

app :: RE a -> RE a -> RE a
app Emp       _   = Emp
app _         Emp = Emp
app Eps       s   = s
app r         Eps = r
app (App r t) s   = app r (app t s)
app r         s   = App r s

nullable :: RE a -> Bool
nullable Emp         = False
nullable Eps         = True
nullable (Chr _)     = False
nullable (Rep _)     = True
nullable (App r1 r2) = nullable r1 && nullable r2
-- nullable (Alt r1 r2) = nullable r1 || nullable r2

derivate :: Eq a => a -> RE a -> [RE a]
derivate _ Emp       = []
derivate _ Eps       = []
derivate c (Chr c')  = if c == c' then [Eps] else []
-- derivate c (Alt r s) = derivate c r ++ derivate c s
derivate c (Rep r)   = [ app r' (Rep r) | r' <- derivate c r ]
derivate c (App r s)
    | nullable r = [ app r' s | r' <- derivate c r ] ++ derivate c s
    | otherwise  = [ app r' s | r' <- derivate c r ]

derivateAny :: RE a -> [RE a]
derivateAny Emp       = []
derivateAny Eps       = []
derivateAny (Chr _)   = [Eps]
derivateAny (Rep r)   = [ app r' (Rep r) | r' <- derivateAny r ]
-- derivateAny (Alt r s) = derivateAny r ++ derivateAny s
derivateAny (App r s)
    | nullable r = [ app r' s | r' <- derivateAny r ] ++ derivateAny s
    | otherwise  = [ app r' s | r' <- derivateAny r ]

-- | Does regexp accept any string of given length.
accepts :: Eq a => Int -> RE a -> Bool
accepts n r
    | n <= 0    = nullable r
    | otherwise = any (accepts (n - 1)) (nub (derivateAny r))

convert :: [Int] -> RE Bool
convert []     = Rep (Chr False)
convert (n:ns) = App (Rep (Chr False)) $ nOnes n $ convert ns
  where
    nOnes m r = if m >= 1 then App (Chr True) (nOnes (m - 1) r) else r

regexp :: forall s. [Int] -> [Lit s] -> SAT s ()
regexp r0 ls0 = do
    tl <- trueLit
    go [(tl, convert r0)] ls0
  where
    go :: [(Lit s, RE Bool)] -> [Lit s] -> SAT s ()
    go s [] = do
        -- we should have reached at least one nullable state
        assertAtLeastOne
            [ l
            | (l, r) <- s
            , nullable r
            ]

    go s (l:ls) = do
        -- next states with a list from which states they can be reached.
        let next :: Map (RE Bool) [(Lit s, Bool)]
            next = Map.fromListWith (++)
                [ (r', [(l', c)])
                | (l', r) <- s
                , c       <- [True, False]
                -- nub doesn't seem to affect.
                , r'      <- nub $ derivate c r
                , accepts (length ls) r'
                ]

        -- add definitions for the next NFA states,
        -- with their values depending on current `l` and previous states.
        s' <- forM (Map.toList next) $ \(r', steps) -> do
            n <- addDefinition $ foldr (\/) false
                [ lit l' /\ if b then lit l else neg (lit l)
                | (l', b) <- steps
                ]

            return (n, r')

        go s' ls
