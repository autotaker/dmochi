module SMTSpec(spec) where
import Language.DMoCHi.ML.Syntax.Typed
import Language.DMoCHi.ML.PrettyPrint.Typed(pprintV)
import Language.DMoCHi.ML.SMT
import Test.Hspec.Core.Spec
import Test.Hspec.Expectations
import Text.PrettyPrint
import Control.Monad

spec :: Spec
spec = do
    describe "sat" $ do
        it "returns the satisfiablity" $ do
            sat [] `shouldReturn` True
            sat [CBool True] `shouldReturn` True
            sat [CBool False] `shouldReturn` False
            sat [Var (Id TBool "x")] `shouldReturn` True
            sat [Var (Id TBool "x"), Op (OpNot (Var (Id TBool "x")))] `shouldReturn` False
        it "abstracts the function" $ do
            let x = Var $ Id TInt "x"
            let y = Var $ Id TInt "y"
            let p1 = Op (OpLt (CInt 0) x)
                p2 = Op (OpLt y x)
                p3 = Op (OpEq y (CInt 1))
                q1 = Op (OpLt (CInt 0) y)
                q2 = Op (OpLt (CInt 0) (Op (OpAdd x y)))
            (do dnf <- fromBDD <$> abst [] [p1,p2,p3,q1,q2]
                forM_ dnf $ \clause -> do
                    let l = [ pprintV 0 (if b then v else Op (OpNot v)) | (v,b) <- clause ] 
                    putStrLn $ render $ hsep $ punctuate comma l
                ) `shouldReturn` ()
