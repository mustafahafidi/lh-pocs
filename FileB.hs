module FileB where
import FileA

{-@ LIQUID "--reflection" @-}

foo = Just 7


{-@ fes :: { sec (Just 2)} @-}
fes ::  Bool
fes = True 
