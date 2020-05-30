module CircularList where

{-@ LIQUID "--reflection" @-}

data CList a = Empty
             | CList [a] a [a]
             
{-@ reflect singleton @-} --this works with --no-adt
singleton :: a -> CList a
singleton e = CList [] e [] 

{-@ reflect update @-}    -- this doesn't work with it
update :: a -> CList a -> CList a
update v Empty = CList [] v []
update v (CList l _ r) = CList l v r

-- ..... there should be other code here similar to `update`