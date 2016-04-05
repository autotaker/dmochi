module SMTSpec(spec) where
import Language.DMoCHi.ML.Syntax.Typed
import Language.DMoCHi.ML.SMT
import Test.Hspec.Core.Spec
import Test.Hspec.Expectations

spec :: Spec
spec = do
    describe "sat" $ do
        it "returns the satisfiablity" $ do
            sat [] `shouldReturn` True
            sat [CBool True] `shouldReturn` True
            sat [CBool False] `shouldReturn` False
            sat [Var (Id TBool "x")] `shouldReturn` True
            sat [Var (Id TBool "x"), Op (OpNot (Var (Id TBool "x")))] `shouldReturn` False



