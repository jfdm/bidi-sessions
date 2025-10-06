module Sessions.Types.Local.Merge.Branch

import Decidable.Equality

import Data.SnocList
import Data.SnocList.Elem

import public Extra

import Sessions.Types.Local
import Sessions.Types.Local.Difference

public export
data Merge : (how : (a,b,c : Local rs fs) -> Type) -> (x,y,z : Branch rs fs) -> Type where
  B : (lx = ly)
   -> (tx = ty)
   -> how kx ky kz
   -> Merge how
            (B lx tx kx)
            (B ly ty ky)
            (B lx tx kz)


public export
merge : (f   : (a,b : Local rs fs) -> Dec $ DPair (Local rs fs) (how a b))
     -> (x,y : Branch rs fs)
            -> Dec (DPair (Branch rs fs) (Merge how x y))

merge f (B lx tx kx) (B ly ty ky) with (Equality.decEq lx ly)
  merge f (B lx tx kx) (B lx ty ky) | (Yes Refl) with (decEq tx ty)
    merge f (B lx tx kx) (B lx tx ky) | (Yes Refl) | (Yes Refl) with (f kx ky)
      merge f (B lx tx kx) (B lx tx ky) | (Yes Refl) | (Yes Refl) | (Yes (ty ** prf))
        = Yes (B lx tx ty ** B Refl Refl prf)
      merge f (B lx tx kx) (B lx tx ky) | (Yes Refl) | (Yes Refl) | (No contra)
        = No (\case (B _ _ ty ** B _ _ prf) => contra (ty ** prf))


    merge f (B lx tx kx) (B lx ty ky) | (Yes Refl) | (No contra)
      = No (\case (B _ _ _ ** B _ Refl _) => contra Refl)

  merge f (B lx tx kx) (B ly ty ky) | (No contra)
    = No (\case (B _ _ _ ** B Refl _ _) => contra Refl)

namespace Branches
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

      Next : (Merge how x y c -> Void)
          -> Merge how x     ys  z
          -> Merge how x (y::ys) z

namespace Branches
  isEmpty : DPair (Branch rs fs) (Merge how x []) -> Void
  isEmpty (_ ** Here y) impossible
  isEmpty (_ ** Next f y) impossible

  export
  merge : (f : (a,b : Local rs fs) -> Dec (DPair (Local rs fs)
                                                 (how a b)))
       -> (x  :       Branch rs fs)
       -> (ys : List (Branch rs fs))
             -> Dec (DPair (Branch rs fs)
                           (Merge how x ys))
  merge f x [] = No isEmpty
  merge f x (y :: xs) with (merge f x y)
    merge f x (y :: xs) | (Yes (z ** prf))
      = Yes (z ** Here prf)

    merge f x (y :: xs) | (No noH) with (merge f x xs)
      merge f x (y :: xs) | (No noH) | (Yes (z ** ltr))
        = Yes (z ** Next (\w => noH (z ** w)) ltr)
      merge f x (y :: xs) | (No noH) | (No noL)
        = No (\case (z ** (Here pH)) => noH (z ** pH)
                    (z ** (Next _  pL)) => noL (z ** pL))


namespace Pairwise

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

namespace Sparse

  public export
  data Union : (how : (a,b,c : Local rs fs) -> Type)
            -> (xs : List (Branch rs fs))
            -> (ys : List (Branch rs fs))
            -> (zs : List (Branch rs fs))
            -> Type where
    End : Union how Nil ys Nil

    Head : Merge how x ys z
        -> Sparse.Union how xs ys zs
        -> Sparse.Union how (x::xs) ys (z::zs)

    Skip : Diff x ys
        -> Sparse.Union how xs ys zs
        -> Sparse.Union how (x::xs) ys zs

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
                    (zs ** (Skip d y)) => contra (zs ** y))

    union f (x :: xs) ys | (No noMerge) with (diff x ys)
      union f (x :: xs) ys | (No noMerge) | (Yes prfDiff) with (Sparse.union f xs ys)
        union f (x :: xs) ys | (No noMerge) | (Yes prfDiff) | (Yes (zs ** prf))
          = Yes (zs ** Skip prfDiff prf)

        union f (x :: xs) ys | (No noMerge) | (Yes prfDiff) | (No noLtr)
          = No (\case ((z :: zs) ** (Head pH pltr)) => noLtr (zs ** pltr)
                      (fst ** (Skip y z)) => noLtr (fst ** z))

      union f (x :: xs) ys | (No noMerge) | (No contra)
        = No (\case ((z :: zs) ** (Head pH pL)) => noMerge (z ** pH)
                    (fst ** (Skip y z)) => contra y)

namespace Full
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
