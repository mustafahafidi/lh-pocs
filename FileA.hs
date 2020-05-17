module FileA where

{-@ LIQUID "--reflection" @-}
{-@ reflect sec @-}
sec :: Eq a => Maybe a -> Bool
sec  Nothing = True
sec (Just x) = x == x
