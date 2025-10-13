module Sessions.Types.Local.Merge.Branches.Pairwise

import Decidable.Equality

import Data.SnocList
import Data.SnocList.Elem

import public Extra

import Sessions.Types.Local
import Sessions.Types.Local.Difference
import Sessions.Types.Local.Merge.Branch

%default total

public export
data Union : (how : (a,b,c : Local rs fs) -> Type)
          -> (xs : List (Branch rs fs))
          -> (ys : List (Branch rs fs))
          -> (zs : List (Branch rs fs))
          -> Type where
  End : Union how Nil Nil Nil

  Head : Merge how x y z
      -> Union how xs ys zs
      -> Union how (x::xs) (y::ys) (z::zs)

Uninhabited (Pairwise.Union how [] (x :: xs) zs) where
  uninhabited End impossible
  uninhabited (Head y z) impossible


Uninhabited  (DPair (List (Branch rs fs)) (Pairwise.Union how [] (x :: xs))) where
  uninhabited (fst ** snd) = absurd snd

Uninhabited (Pairwise.Union how (x :: xs) [] zs) where
  uninhabited End impossible
  uninhabited (Head y z) impossible


Uninhabited  (DPair (List (Branch rs fs)) (Pairwise.Union how (x :: xs) [])) where
  uninhabited (fst ** snd) = absurd snd


export
union : (f : (a,b : Local rs fs) -> Dec (DPair (Local rs fs)
                                               (how a b)))
     -> (xs : List (Branch rs fs))
     -> (ys : List (Branch rs fs))
           -> Dec (DPair (List (Branch rs fs))
                         (Pairwise.Union how xs ys))
union f [] []
  = Yes ([] ** End)
union f [] (x :: xs)
  = No absurd
union f (x :: xs) []
  = No absurd

union f (x :: xs) (y :: ys) with (merge f x y)
  union f (x :: xs) (y :: ys) | (Yes (z ** prf)) with (union f xs ys)
    union f (x :: xs) (y :: ys) | (Yes (z ** prf)) | (Yes (zs ** prfT))
      = Yes (z :: zs ** Head prf prfT)

    union f (x :: xs) (y :: ys) | (Yes (z ** prf)) | (No no)
      = No (\case ((z :: zs) ** (Head pH pT)) => no (zs ** pT))

  union f (x :: xs) (y :: ys) | (No no)
    = No (\case ((z :: zs) ** (Head pH pT)) => no (z ** pH))

export
unique : {0 how : (a,b,c : Local rs fs) -> Type}
      -> (f : {0 a,b,c,d : Local rs fs}
           -> (  this : how a b c)
           -> (  that : how a b d)
           -> c === d)
      -> Union how kx ky as
      -> Union how kx ky bs
      -> as === bs
unique f End End
  = Refl

unique f (Head x xs) (Head y ys) with (unique f x y)
  unique f (Head x xs) (Head y ys) | Refl with (unique f xs ys)
    unique f (Head x xs) (Head y ys) | Refl | Refl = Refl

-- [ EOF ]
