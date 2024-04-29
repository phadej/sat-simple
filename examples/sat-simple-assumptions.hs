module Main (main) where

import Control.Monad.SAT

main :: IO ()
main = do
    res <- runSATMaybe $ do
        p <- newLit
        q <- newLit
        r <- newLit
        addClause [p]
        addClause [q]
        addClause [r]

        -- we can solve with assumptions
        a1 <- solveAssuming (pure p)
        a2 <- solveAssuming (pure (neg p))
        b1 <- solveAssuming (pure q)
        b2 <- solveAssuming (pure (neg q))

        -- and then solve the whole thing.
        sol <- solve [p,q,r]

        return ([a1, a2, b1, b2], sol)

    print res