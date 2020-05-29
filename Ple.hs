{-@ LIQUID "--ple-local"    @-}
{-@ LIQUID "--reflection"    @-}

{-@ reflect anyM @-}
anyM :: (a -> Bool) -> [a] -> Bool
anyM _ []        = False
anyM p (x:xs)    = p x || anyM p xs 

{-@ reflect asd @-}
asd :: Int -> [Int] -> Bool
asd a b = anyM (\x -> a == x) b

{-@ ple pr @-}
{-@ pr :: { asd 1 [1] } @-}
pr = ()
