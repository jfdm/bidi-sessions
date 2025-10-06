module Sessions.Types.Local.Merge.Branches.Sparse

import Decidable.Equality

import Data.SnocList
import Data.SnocList.Elem

import public Extra

import Sessions.Types.Local
import Sessions.Types.Local.Difference
import Sessions.Types.Local.Merge.Branch
import Sessions.Types.Local.Merge.Branches.Single


public export
data Union : (how : (a,b,c : Local rs fs) -> Type)
          -> (xs : List (Branch rs fs))
          -> (ys : List (Branch rs fs))
          -> (zs : List (Branch rs fs))
          -> Type where
  End : Union how Nil ys Nil

  Head : Merge how x ys z
      -> Union how xs ys zs
      -> Union how (x::xs) ys (z::zs)

  Skip : (DPair (Branch rs fs) (Merge how x ys) -> Void)
      -> Diff x ys
      -> Union how xs ys zs
      -> Union how (x::xs) ys zs

export
union : (f : (a,b : Local rs fs) -> Dec (DPair (Local rs fs)
                                               (how a b)))
     -> (xs : List (Branch rs fs))
     -> (ys : List (Branch rs fs))
           -> Dec (DPair (List (Branch rs fs))
                         (Sparse.Union how xs ys))
union f [] ys
  = Yes ([] ** End)

union f (x :: xs) ys with (merge f x ys)
  union f (x :: xs) ys | (Yes (z ** pX)) with (Sparse.union f xs ys)
    union f (x :: xs) ys | (Yes (z ** pX)) | (Yes (zs ** pXS))
      = Yes (z :: zs ** Head pX pXS)

    union f (x :: xs) ys | (Yes (z ** pX)) | (No contra)
      = No (\case ((z :: zs) ** (Head y w)) => contra (zs ** w)
                  (zs ** (Skip _ d y)) => contra (zs ** y))

  union f (x :: xs) ys | (No noMerge) with (diff x ys)
    union f (x :: xs) ys | (No noMerge) | (Yes prfDiff) with (Sparse.union f xs ys)
      union f (x :: xs) ys | (No noMerge) | (Yes prfDiff) | (Yes (zs ** prf))
        = Yes (zs ** Skip noMerge prfDiff prf)

      union f (x :: xs) ys | (No noMerge) | (Yes prfDiff) | (No noLtr)
        = No (\case ((z :: zs) ** (Head pH pltr)) => noLtr (zs ** pltr)
                    (fst ** (Skip noMerge y z)) => noLtr (fst ** z))

    union f (x :: xs) ys | (No noMerge) | (No contra)
      = No (\case ((z :: zs) ** (Head pH pL)) => noMerge (z ** pH)
                  (fst ** (Skip noMerge y z)) => contra y)

export
unique : {0 how : (a,b,c : Local rs fs) -> Type}
      -> (f : {0 a,b,c,d : Local rs fs}
           -> (  this : how a b c)
           -> (  that : how a b d)
           -> c === d)
      -> Union how kx ky as
      -> Union how kx ky bs
      -> as === bs
unique _ End End = Refl
unique f (Head x xs) (Head y ys) with (unique f x y)
  unique f (Head x xs) (Head y ys) | Refl with (unique f xs ys)
    unique f (Head x xs) (Head y ys) | Refl | Refl = Refl

unique f (Head x xs) (Skip no y ys) = void (absurd $ no (_ ** x))
unique f (Skip no x z) (Head y w) = void (absurd $ no (_ ** y))

unique f (Skip nx x xs) (Skip ny y ys) with (unique f xs ys)
  unique f (Skip nx x xs) (Skip ny y ys) | Refl = Refl

-- [ EOF ]
