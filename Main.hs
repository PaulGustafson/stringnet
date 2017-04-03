module Main where

import Stringnet
import TambaraYamagami
import Data.Matrix
import Data.List
--import Test

main :: IO ()
-- main = print $ finalMorphism
-- main = print $ substM finalMorphism
-- main = print $ toTree finalMorphism
-- main = print $ substM $ leaves !! 0
main = putStrLn $ latex $ rmatrix
-- main = print rmatrix


latex :: Show a => Matrix a -> String
latex m =
  intercalate " \\\\ \n" . map (intercalate  " & ". map show) $ toLists m

