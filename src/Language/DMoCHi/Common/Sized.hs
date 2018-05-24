module Language.DMoCHi.Common.Sized(Sized(..)) where
class Sized e where
    getSize :: e -> Int
