module Sessions.Types.Local.Merge.Branches.Full

import Decidable.Equality

import Data.SnocList
import Data.SnocList.Elem

import public Extra

import Sessions.Types.Local
import Sessions.Types.Local.Difference
import Sessions.Types.Local.Merge.Branch
import Sessions.Types.Local.Merge.Branches.Single
import Sessions.Types.Local.Merge.Branches.Sparse

%default total


public export
data Merge : (how : (a,b,c : Local rs fs) -> Type)
          -> (xs : List (Branch rs fs))
          -> (ys : List (Branch rs fs))
          -> (zs : List (Branch rs fs))
                -> Type
  where
    Full : {zs : _}
        -> Diff kx ky xs
        -> Diff ky kx ys
        -> Sparse.Union how kx ky zs
        -> Merge how kx ky (xs ++ ys ++ zs)

export
merge : (f : (a,b : Local rs fs) -> Dec (DPair (Local rs fs)
                                                 (how a b)))
       -> (xs : List (Branch rs fs))
       -> (ys : List (Branch rs fs))
             -> Dec (DPair (List (Branch rs fs))
                           (Full.Merge how xs ys))
merge f xs ys with (diff xs ys)
  merge f xs ys | (xys ** pXY) with (diff ys xs)
    merge f xs ys | (xys ** pXY) | (yxs ** pYX) with (Sparse.union f xs ys)
      merge f xs ys | (xys ** pXY) | (yxs ** pYX) | (Yes (zs ** pZS))
        = Yes (xys ++ (yxs ++ zs) ** Full pXY pYX pZS)
      merge f xs ys | (xys ** pXY) | (yxs ** pYX) | (No no)
        = No (\case ((xs ++ (ys ++ zs)) ** (Full x y z)) => no (zs ** z))

export
unique : {0 how : (a,b,c : Local rs fs) -> Type}
      -> (f : {0 a,b,c,d : Local rs fs}
           -> (  this : how a b c)
           -> (  that : how a b d)
           -> c === d)
      -> Full.Merge how xs ys as
      -> Full.Merge how xs ys bs
      -> as === bs

unique f (Full xxy xyx xu) (Full yxy yyx yu) with (uniques xxy yxy)
  unique f (Full xxy xyx xu) (Full yxy yyx yu) | Refl with (uniques xyx yyx)
    unique f (Full xxy xyx xu) (Full yxy yyx yu) | Refl | Refl with (Sparse.unique f xu yu)
      unique f (Full xxy xyx xu) (Full yxy yyx yu) | Refl | Refl | Refl = Refl

-- [ EOF ]
