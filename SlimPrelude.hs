module SlimPrelude where

import Prelude hiding (length, 
                        (++), 
                        reverse,
                        any
                        )
{-@ measure length @-}
{-@ length :: x:[a] -> { length x >=0 } @-}
length :: [a] -> Int
length [] = 0
length (_:xs) = 1 + length xs

{-@ reflect null @-}
{-@ null :: l:[a] -> {v:Bool | not v <=> len l > 0} @-}
null :: [a] -> Bool
null [] = True
null xs = False 

    
{-@ infix 4  ++ @-}
{-@ reflect ++ @-}
{-@ (++) :: xs:[a] -> ls:[a] -> {vs:[a] | length vs == (length xs) + (length ls) } @-}
(++) :: [a] -> [a] -> [a]
[]       ++ ys = ys
(x : xs) ++ ys = x : (xs ++ ys)


{-@ reflect reverse @-}
{-@ reverse :: xs:[a] -> {ls:[a] | length ls == length xs} @-}
reverse :: [a] -> [a]
reverse []     = []
reverse (x:xs) = reverse xs ++ [x]


{-@ reflect any @-}
any :: (a -> Bool) -> [a] -> Bool
any _ []        = False
any p (x:xs)    = p x || any p xs
