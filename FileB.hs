module FileB where
import FileA

{-@ LIQUID "--reflection" @-}
{-@ fes :: { sec (Just 2)} @-}
fes ::  Bool
fes = True 