module Main (main) where

import Control.Applicative    (liftA2)
import Control.Monad          (void)
import Control.Monad.IO.Class (liftIO)
import Data.Foldable          (toList)

import Control.Monad.SAT

data H3 a = H3 a a a
  deriving (Show, Functor, Foldable, Traversable)

instance Applicative H3 where
    pure x = H3 x x x
    H3 f1 f2 f3 <*> H3 x1 x2 x3 = H3 (f1 x1) (f2 x2) (f3 x3)

data H5 a = H5 a a a a a
  deriving (Show, Functor, Foldable, Traversable)

instance Applicative H5 where
    pure x = H5 x x x x x
    H5 f1 f2 f3 f4 f5 <*> H5 x1 x2 x3 x4 x5 = H5 (f1 x1) (f2 x2) (f3 x3) (f4 x4) (f5 x5)

eval :: H5 Bool -> Bool
eval (H5 p q r s t) =
    not ((p && q) == r) && (impl s (p && t))
  where
    impl x y = not x || y

title :: String -> IO ()
title s = do
    putStrLn ""
    putStrLn s
    putStrLn $ '-' <$ s

main :: IO ()
main = do
    title "addDefinition >>= addClause . singleton"
    void $ runSATMaybe $ do
        -- ~ ((p /\ q) <-> r) /\ (s -> (p /\ t))
        p <- newLit
        q <- newLit
        r <- newLit
        s <- newLit
        t <- newLit
        let prop = neg ((lit p /\ lit q) <-> lit r) /\ (lit s --> (lit p /\ lit t))
        liftIO $ print prop
        f <- addDefinition prop
        addClause [f]

        let lits = H5 p q r s t

        let loop = do
                res <- solve lits
                liftIO $ print (eval res, res)

                let n True  l = neg l
                    n False l = l

                addClause $ toList $ liftA2 n res lits

                loop

        loop

    title "addProp"
    void $ runSATMaybe $ do
        -- ~ ((p /\ q) <-> r) /\ (s -> (p /\ t))
        p <- newLit
        q <- newLit
        r <- newLit
        s <- newLit
        t <- newLit

        addProp $ neg ((lit p /\ lit q) <-> lit r) /\ (lit s --> (lit p /\ lit t))
        let lits = H5 p q r s t

        let loop = do
                res <- solve lits
                liftIO $ print (eval res, res)

                let n True  l = neg l
                    n False l = l

                addClause $ toList $ liftA2 n res lits

                loop

        loop

    title "Same using addProp"
    void $ runSATMaybe $ do
        p <- newLit
        q <- newLit
        r <- newLit
        s <- newLit
        t <- newLit

        let prop = (lit p /\ lit q /\ lit r /\ lit s /\ lit t) \/ (neg (lit p) /\ neg (lit q) /\ neg (lit r) /\ neg (lit s) /\ neg (lit t))
        liftIO $ print prop
        addProp prop
        let lits = H5 p q r s t

        let loop = do
                res <- solve lits
                liftIO $ print res

                let n True  l = neg l
                    n False l = l

                addClause $ toList $ liftA2 n res lits

                loop

        loop

    title "Same using assertAllEqual"
    void $ runSATMaybe $ do
        p <- newLit
        q <- newLit
        r <- newLit
        s <- newLit
        t <- newLit

        assertAllEqual [p, q, r, s, t]
        let lits = H5 p q r s t

        let loop = do
                res <- solve lits
                liftIO $ print res

                let n True  l = neg l
                    n False l = l

                addClause $ toList $ liftA2 n res lits

                loop

        loop

    title "Same using <->"
    void $ runSATMaybe $ do
        p <- newLit
        q <- newLit
        r <- newLit
        s <- newLit
        t <- newLit

        let prop = (lit p <-> lit q) /\
                   (lit q <-> lit r) /\
                   (lit r <-> lit s) /\
                   (lit s <-> lit t)
        liftIO $ print prop
        addProp prop
        let lits = H5 p q r s t

        let loop = do
                res <- solve lits
                liftIO $ print res

                let n True  l = neg l
                    n False l = l

                addClause $ toList $ liftA2 n res lits

                loop

        loop

    title "if-then-else"
    void $ runSATMaybe $ do
        c <- newLit
        t <- newLit
        f <- newLit

        let prop = ite (lit c) (lit t) (lit f)
        liftIO $ putStrLn $ "prop = " ++ show prop
        -- addProp prop
        addDefinition prop >>= addClause . pure

        let lits = H3 c t f
        let loop = do
                res <- solve lits
                liftIO $ print res

                let n True  l = neg l
                    n False l = l

                addClause $ toList $ liftA2 n res lits

                loop

        loop
