module Sessions.Types.Local.Merge.Experimental

import Decidable.Equality

import Data.SnocList
import Data.SnocList.Elem

import public Extra

import Sessions.Types.Local
import public Sessions.Types.Local.Difference


namespace Branch
  public export
  data Merge : (how : (a,b,c : Local rs fs) -> Type) -> (x,y,z : Branch rs fs) -> Type where
    B : (lx = ly)
     -> (tx = ty)
     -> how kx ky kz
     -> Merge how
              (B lx tx kx)
              (B ly ty ky)
              (B lx tx kz)

namespace Branches

  namespace Branch
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

  public export
  data Merge : (how : (a,b,c : Local rs fs) -> Type)
            -> (xs : List (Branch rs fs))
            -> (ys : List (Branch rs fs))
            -> (zs : List (Branch rs fs))
            -> Type where
    End : Merge how Nil ys Nil

    Head : Merge how x ys z
        -> Merge how xs ys zs
        -> Merge how (x::xs) ys (z::zs)

    Skip : Diff x ys
        -> Merge how xs ys zs
        -> Merge how (x::xs) ys zs

public export
data Merge : (x,y,z : Local rs fs)
           -> Type

  where
    Stop : Merge Stop Stop Stop
    Call : (idxx = idxy)
        -> Merge (Call idxx)
                 (Call idxy)
                 (Call idxx)
    Rec : Merge kx ky kz
       -> Merge (Rec f kx) (Rec f ky)
                (Rec f kz)
    Comm : {zs : List $ Branch rs fs}
        -> (cx = cy)
        -> (sx = sy)
        -> Diff kx ky xs
        -> Diff ky kx ys
        -> Branches.Merge Merge kx ky zs -- <= union
        -> Merge (Comm cx sx kx)
                 (Comm cy sy ky)
                 (Comm cx sx (xs ++ zs ++ ys))

namespace Branch
  public export
  merge : (f   : (a,b : Local rs fs) -> Dec $ DPair (Local rs fs) (Merge a b))
       -> (x,y : Branch rs fs)
              -> Dec (DPair (Branch rs fs) (Merge Merge x y))

  merge f (B lx tx kx) (B ly ty ky) with (decEq lx ly)
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

  namespace Branch
    isEmpty : DPair (Branch rs fs) (Merge Merge x []) -> Void
    isEmpty (_ ** Here y) impossible
    isEmpty (_ ** Next f y) impossible

    export
    merge : (f : (a,b : Local rs fs) -> Dec (DPair (Local rs fs)
                                                   (Merge a b)))
         -> (x  :       Branch rs fs)
         -> (ys : List (Branch rs fs))
               -> Dec (DPair (Branch rs fs)
                             (Merge Merge x ys))
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

  export
  merge : (f : (a,b : Local rs fs) -> Dec (DPair (Local rs fs)
                                                 (Merge a b)))
       -> (xs : List (Branch rs fs))
       -> (ys : List (Branch rs fs))
             -> Dec (DPair (List (Branch rs fs))
                           (Merge Merge xs ys))
  merge f [] ys
    = Yes ([] ** End)

  merge f (x :: xs) ys with (merge f x ys)
    merge f (x :: xs) ys | (Yes (z ** pX)) with (merge f xs ys)
      merge f (x :: xs) ys | (Yes (z ** pX)) | (Yes (zs ** pXS))
        = Yes (z :: zs ** Head pX pXS)

      merge f (x :: xs) ys | (Yes (z ** pX)) | (No contra)
        = No (\case ((z :: zs) ** (Head y w)) => contra (zs ** w)
                    (zs ** (Skip d y)) => contra (zs ** y))

    merge f (x :: xs) ys | (No noMerge) with (diff x ys)
      merge f (x :: xs) ys | (No noMerge) | (Yes prfDiff) with (merge f xs ys)
        merge f (x :: xs) ys | (No noMerge) | (Yes prfDiff) | (Yes (zs ** prf))
          = Yes (zs ** Skip prfDiff prf)

        merge f (x :: xs) ys | (No noMerge) | (Yes prfDiff) | (No noLtr)
          = No (\case ((z :: zs) ** (Head pH pltr)) => noLtr (zs ** pltr)
                      (fst ** (Skip y z)) => noLtr (fst ** z))

      merge f (x :: xs) ys | (No noMerge) | (No contra)
        = No (\case ((z :: zs) ** (Head pH pL)) => noMerge (z ** pH)
                    (fst ** (Skip y z)) => contra y)

--    (merge f xs ys)

--      merge f (x :: xs) ys | (No contra) | (Yes (zs ** pZs))
--        = Yes (zs ** Skip pZs)
--      merge f (x :: xs) ys | (No contra) | (No g)
--        = ?as -- error need to fail when a valid merge attempt fails.
--        --No (\case ((z :: zs) ** (Head pH pT)) => g (zs ** pT)
--        --            (fst ** (Skip y)) => g (fst ** y))
--  merge f [] ys = Yes ([] ** End)
--
--  merge f (x :: xs) ys with (merge f x ys)
--    merge f (x :: xs) ys | (Yes (z ** pH)) with (merge f xs ys)
--      merge f (x :: xs) ys | (Yes (z ** pH)) | Yes (zs ** pT)
--        = Yes (z :: zs ** Head pH pT)
--
--    merge f (x :: xs) ys | (No contra) = ?as
--    with (merge f xs ys)
--      merge f (x :: xs) ys | (No contra) | (zs ** pT)
--        = (zs ** Skip pT)

mergeSC : DPair (Local rs fs) (Merge Stop (Call x)) -> Void
mergeSC (_ ** _) impossible

mergeSR : DPair (Local rs fs) (Merge Stop (Rec x s)) -> Void
mergeSR (_ ** _) impossible

mergeSM : DPair (Local rs fs) (Merge Stop (Comm x y xs)) -> Void
mergeSM (_ ** _) impossible

mergeCR : DPair (Local rs fs) (Merge (Call idx) (Rec x s)) -> Void
mergeCR (_ ** _) impossible

mergeCM : DPair (Local rs fs) (Merge (Call idx) (Comm z x s)) -> Void
mergeCM (_ ** _) impossible

mergeCS : DPair (Local rs fs) (Merge (Call x) Stop ) -> Void
mergeCS (_ ** _) impossible

mergeRS : DPair (Local rs fs) (Merge (Rec x s) Stop) -> Void
mergeRS (_ ** _) impossible

mergeRC: DPair (Local rs fs) (Merge (Rec x s) (Call idx) ) -> Void
mergeRC (_ ** _) impossible

mergeRM: DPair (Local rs fs) (Merge (Rec x s) (Comm a w idx) ) -> Void
mergeRM (_ ** _) impossible


mergeMS : DPair (Local rs fs) (Merge (Comm x y xs) Stop) -> Void
mergeMS (_ ** _) impossible

mergeMC : DPair (Local rs fs) (Merge  (Comm z x s) (Call idx)) -> Void
mergeMC (_ ** _) impossible

mergeMR: DPair (Local rs fs) (Merge (Comm a w idx) (Rec x s)) -> Void
mergeMR (_ ** _) impossible


export
merge : (x,y : Local rs fs) -> Dec (DPair (Local rs fs) (Merge x y))
merge Stop Stop = Yes (Stop ** Stop)
merge Stop (Call x) = No mergeSC
merge Stop (Rec f x) = No mergeSR
merge Stop (Comm x y xs) = No mergeSM

merge (Call x) Stop = No mergeCS
merge (Call x) (Call y) with (decEq x y)
  merge (Call x) (Call x) | (Yes Refl)
    = Yes (Call x ** Call Refl)
  merge (Call x) (Call y) | (No contra)
    = No (\case (Call fst ** Call Refl) => contra Refl)

merge (Call x) (Rec f y) = No mergeCR
merge (Call x) (Comm y z xs) = No mergeCM

merge (Rec f x) Stop = No mergeRS
merge (Rec f x) (Call y) = No mergeRC
merge (Rec f x) (Rec y z) with (decEq f y)
  merge (Rec f x) (Rec f z) | (Yes Refl) with (merge x z)
    merge (Rec f x) (Rec f z) | (Yes Refl) | (Yes (ty ** prf))
      = Yes (Rec f ty ** Rec prf)

    merge (Rec f x) (Rec f z) | (Yes Refl) | (No contra)
      = No (\case (Rec f x ** Rec prf) => contra (x ** prf))

  merge (Rec f x) (Rec y z) | (No contra)
    = No (\case (Rec f x ** Rec snd) => contra Refl)

merge (Rec f x) (Comm y z xs) = No mergeRM

merge (Comm x z xs) Stop = No mergeMS
merge (Comm x z xs) (Call y) = No mergeMC
merge (Comm x z xs) (Rec f y) = No mergeMR
merge (Comm x z xs) (Comm y w ys) with (decEq x y)
  merge (Comm x z xs) (Comm x w ys) | (Yes Refl) with (decEq z w)
    merge (Comm x z xs) (Comm x z ys) | (Yes Refl) | (Yes Refl) with (diff xs ys)
      merge (Comm x z xs) (Comm x z ys) | (Yes Refl) | (Yes Refl) | (dx ** px) with (diff ys xs)
        merge (Comm x z xs) (Comm x z ys) | (Yes Refl) | (Yes Refl) | (dx ** px) | (dy ** py) with (merge merge xs ys)
          merge (Comm x z xs) (Comm x z ys) | (Yes Refl) | (Yes Refl) | (dx ** px) | (dy ** py) | (Yes (zs ** snd))
            = Yes (Comm x z (dx ++ (zs ++ dy)) ** Comm Refl Refl px py snd)
          merge (Comm x z xs) (Comm x z ys) | (Yes Refl) | (Yes Refl) | (dx ** px) | (dy ** py) | (No contra)
            = No (\case (Comm x z (xs ++ zs ++ ys ) ** Comm Refl Refl dx dy snd) => contra (zs ** snd))

        --with (merge merge xs ys)
        --  merge (Comm x z xs) (Comm x z ys) | (Yes Refl) | (Yes Refl) | (dx ** px) | (dy ** py) | (zs ** prf)
        --    = Yes (Comm x z (dx ++ (zs ++ dy)) ** Comm Refl Refl px py prf)

    merge (Comm x z xs) (Comm x w ys) | (Yes Refl) | (No contra)
      = No (\case (Comm x z _ ** Comm Refl Refl dx dy rest) => contra Refl)
  merge (Comm x z xs) (Comm y w ys) | (No contra)
    = No (\case (Comm z x _ ** Comm Refl _ _ _rest) => contra Refl)

-- [ EOF ]
