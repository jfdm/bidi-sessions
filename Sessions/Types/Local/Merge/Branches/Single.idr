module Sessions.Types.Local.Merge.Branches.Single

import Decidable.Equality

import Data.SnocList
import Data.SnocList.Elem

import public Extra

import Sessions.Types.Local
import Sessions.Types.Local.Difference
import Sessions.Types.Local.Merge.Branch


||| There is an y in ys that results in z
public export
data Merge : (how : (a,b,c : Local rs fs) -> Type)
          -> (x  :      (Branch rs fs))
          -> (ys : List (Branch rs fs))
          -> (z  :      (Branch rs fs))
         -> Type
  where

    Here : Merge how x   y      z
        -> Merge how x (y::ys) z

    Next : (no : {z : Branch rs fs} -> Branch.Merge how x y z -> Void)
        -> Single.Merge how x     ys  z
        -> Merge how x (y::ys) z

export
unique : {0 how : (a,b,c : Local rs fs) -> Type}
      -> (f : {0 a,b,c,d : Local rs fs}
           -> (  this : how a b c)
           -> (  that : how a b d)
           -> c === d)
      -> Single.Merge how x ys a
      -> Single.Merge how x ys b
      -> a === b
unique f (Here x) (Here y) with (unique f x y)
  unique f (Here x) (Here y) | Refl = Refl
unique f (Here x) (Next no ys)
  = void (absurd (no x))

unique f (Next no x) (Here y)
  = void (absurd (no y))

unique f (Next noX x) (Next noY y) with (unique f x y)
  unique f (Next noX x) (Next noY y) | Refl =  Refl


Uninhabited (Merge how x Nil z) where
  uninhabited (Here y) impossible
  uninhabited (Next no y) impossible

export
merge : (f : (a,b : Local rs fs) -> Dec (DPair (Local rs fs)
                                               (how a b)))
     -> (x  :       Branch rs fs)
     -> (ys : List (Branch rs fs))
           -> Dec (DPair (Branch rs fs)
                         (Merge how x ys))
merge f x []
  = No $ \case (fst ** snd) => absurd snd

merge f x (y :: xs) with (merge f x y)
  merge f x (y :: xs) | (Yes (z ** prf))
    = Yes (z ** Here prf)

  merge f x (y :: xs) | (No noH) with (merge f x xs)
    merge f x (y :: xs) | (No noH) | (Yes (z ** ltr))
      = Yes (z ** Next (\w => noH (_ ** w)) ltr)
    merge f x (y :: xs) | (No noH) | (No noL)
      = No (\case (z ** (Here pH)) => noH (z ** pH)
                  (z ** (Next _  pL)) => noL (z ** pL))

-- [ EOF ]
