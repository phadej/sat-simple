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

        let model = [p,q,r]

        -- we can solve with assumptions
        b1 <- solveAssuming_ (pure p)
        b2 <- solveAssuming_ (pure (neg p))
        b3 <- solveAssuming_ (pure q)
        b4 <- solveAssuming_ (pure (neg q))

        -- we can solve with assumptions and check the model
        m1 <- solveAssuming model (pure p)
        m2 <- solveAssuming model (pure (neg p))
        m3 <- solveAssuming model (pure q)
        m4 <- solveAssuming model (pure (neg q))

        -- and then solve the whole thing.
        sol <- solve model

        return ([b1, b2, b3, b4], [m1,m2,m3,m4], sol)

    print res
