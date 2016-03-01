module Language.DMoCHi.Boolean.Example where
import Syntax
example1 :: Program
example1 = Program defs t0 where
   defs = [ ("g",Lam ["y"] $ Lam ["z"] $ Lam ["x"] $ App (V "z") [V "x"] :+: App (V "y") [V "x"])
          , ("f1",Lam ["x"] $ If (V "x") (V "x") (Omega ""))
          , ("f2",Lam ["x"] $ If (V "x") (Omega "") (V "x"))
          , ("f3",Lam ["x"] $ Omega "") ]
   t1 = Lam ["f"] $
            If (App (V "f") [C True])
                (If (App (V "f") [C False])
                    (Fail "")
                    (App (App (App (V "g") [V "f3"]) [V "f3"]) [Fail ""]))
                (Fail "")
   t0 = App t1 [App (App (V "g") [V "f1"]) [V "f2"]]

example2 :: Program
example2 = Program defs t0 where
   defs = [ ("g",Lam ["y"] $ Lam ["z"] $ V "z" :+: V "y")
          , ("f1",Lam ["x"] $ If (V "x") (V "x") (Omega ""))
          , ("f2",Lam ["x"] $ If (V "x") (Omega "") (V "x"))
          , ("f3",Lam ["x"] $ Omega "") ]
   t1 = Lam ["f"] $
            If (App (V "f") [C True])
                (If (App (V "f") [C False])
                    (Fail "")
                    (App (App (App (V "g") [V "f3"]) [V "f3"]) [Fail ""]))
                (Fail "")
   t0 = App t1 [App (App (V "g") [V "f1"]) [V "f2"]]

example3 :: Program
example3 = Program defs t0 where
   defs = [ ("g",Lam ["y"] $ Lam ["z"] $ V "z" :+: V "y")
          , ("f1",Lam ["x"] $ If (V "x") (V "x") (Omega ""))
          , ("f2",Lam ["x"] $ If (V "x") (Omega "") (V "x"))
          , ("f3",Lam ["x"] $ Omega "") 
          , ("f4",Lam ["x","y"] $ App (Omega "") [V "f4"] ) ]
   t1 = Lam ["f"] $
            If (App (V "f") [C True])
                (If (App (V "f") [C False])
                    (Fail "")
                    (App (App (App (V "g") [V "f3"]) [V "f3"]) [Fail ""]))
                (Fail "")
   t0 = App t1 [App (App (V "g") [V "f1"]) [V "f2"]]

example4 :: Program
example4 = Program defs t0 where
   defs = [ ("g",Lam ["y"] $ Lam ["z"] $ Lam ["x"] $ App (V "y") [V "x"] :+: App (V "z") [V "x"])
          , ("f1",Lam ["x"] $ (Omega ""))
          , ("f2",Lam ["x"] $ (Omega ""))]
   t1 = Lam ["f"] $ App (V "f") [C False] :+: App (V "f") [C True]
   t0 = App t1 [App (App (V "g") [V "f1"]) [V "f2"]]

example5 :: Program
example5 = Program defs t0 where
   defs = [ ("f1",Lam ["x"] $ App (V "f2") [V "x"])
          , ("f2",Lam ["x"] $ App (V "f1") [V "x"])]
   t0 = App (V "f1") [C True]
