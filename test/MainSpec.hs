module MainSpec(spec) where
import Language.DMoCHi.ML.Main(verify, Config(..), defaultConfig)

import System.FilePath
import Test.Hspec.Core.Spec
import Test.Hspec.Expectations
import Control.Monad

test :: FilePath -> Spec
test testCase = 
    describe ("Test: " ++ testCase) $ do
        it "fusion successfully ends" $ do
            let conf = (defaultConfig testCase){ fusion = True, incremental = True }
            (v1, _) <- verify conf
            let right (Left _) = False
                right (Right _) = True
            v1 `shouldSatisfy` right
            (v2, _) <- verify (defaultConfig testCase)
            v2 `shouldSatisfy` right
            v1 `shouldBe` v2

spec :: Spec
spec = do
    let cases = [ "sum.ml", "mc91.ml" ] ++ [ "example" ++ show i ++ ".ml" | i <- [1..11] ]
    let pathes = ["sample" </> s | s <- cases ]
    forM_ pathes test
    

