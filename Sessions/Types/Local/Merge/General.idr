module Sessions.Types.Local.Merge.General

import Decidable.Equality

import Data.SnocList
import Data.SnocList.Elem

import public Extra

import Sessions.Types.Local
import public Sessions.Types.Local.Difference
import public Sessions.Types.Local.Merge.Branch


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

    Send : (sx = sy)
        -> Send.Merge Merge kx ky kz
        -> Merge (Comm SEND sx kx)
                 (Comm SEND sy ky)
                 (Comm SEND sx kz)


    Recv : {zs : List $ Branch rs fs}
        -> (sx = sy)
        -> Diff kx ky xs
        -> Diff ky kx ys
        -> Recv.Merge Merge kx ky zs
        -> Merge (Comm RECV sx kx)
                 (Comm RECV sy ky)
                 (Comm RECV sx (xs ++ zs ++ ys))


namespace Send

  Uninhabited (Send.Merge Merge [] (x :: xs) zs) where
    uninhabited End impossible
    uninhabited (Head y z) impossible


  Uninhabited  (DPair (List (Branch rs fs)) (Send.Merge Merge [] (x :: xs))) where
    uninhabited (fst ** snd) = absurd snd

  Uninhabited (Send.Merge Merge (x :: xs) [] zs) where
    uninhabited End impossible
    uninhabited (Head y z) impossible


  Uninhabited  (DPair (List (Branch rs fs)) (Send.Merge Merge (x :: xs) [])) where
    uninhabited (fst ** snd) = absurd snd


  export
  merge : (f : (a,b : Local rs fs) -> Dec (DPair (Local rs fs)
                                                 (Merge a b)))
       -> (xs : List (Branch rs fs))
       -> (ys : List (Branch rs fs))
             -> Dec (DPair (List (Branch rs fs))
                           (Send.Merge Merge xs ys))
  merge f [] []
    = Yes ([] ** End)
  merge f [] (x :: xs)
    = No absurd
  merge f (x :: xs) []
    = No absurd

  merge f (x :: xs) (y :: ys) with (merge f x y)
    merge f (x :: xs) (y :: ys) | (Yes (z ** prf)) with (merge f xs ys)
      merge f (x :: xs) (y :: ys) | (Yes (z ** prf)) | (Yes (zs ** prfT))
        = Yes (z :: zs ** Head prf prfT)

      merge f (x :: xs) (y :: ys) | (Yes (z ** prf)) | (No no)
        = No (\case ((z :: zs) ** (Head pH pT)) => no (zs ** pT))

    merge f (x :: xs) (y :: ys) | (No no)
      = No (\case ((z :: zs) ** (Head pH pT)) => no (z ** pH))

namespace Recv
  export
  merge : (f : (a,b : Local rs fs) -> Dec (DPair (Local rs fs)
                                                 (Merge a b)))
       -> (xs : List (Branch rs fs))
       -> (ys : List (Branch rs fs))
             -> Dec (DPair (List (Branch rs fs))
                           (Recv.Merge Merge xs ys))
  merge f [] ys
    = Yes ([] ** End)

  merge f (x :: xs) ys with (merge f x ys)
    merge f (x :: xs) ys | (Yes (z ** pX)) with (Recv.merge f xs ys)
      merge f (x :: xs) ys | (Yes (z ** pX)) | (Yes (zs ** pXS))
        = Yes (z :: zs ** Head pX pXS)

      merge f (x :: xs) ys | (Yes (z ** pX)) | (No contra)
        = No (\case ((z :: zs) ** (Head y w)) => contra (zs ** w)
                    (zs ** (Skip d y)) => contra (zs ** y))

    merge f (x :: xs) ys | (No noMerge) with (diff x ys)
      merge f (x :: xs) ys | (No noMerge) | (Yes prfDiff) with (Recv.merge f xs ys)
        merge f (x :: xs) ys | (No noMerge) | (Yes prfDiff) | (Yes (zs ** prf))
          = Yes (zs ** Skip prfDiff prf)

        merge f (x :: xs) ys | (No noMerge) | (Yes prfDiff) | (No noLtr)
          = No (\case ((z :: zs) ** (Head pH pltr)) => noLtr (zs ** pltr)
                      (fst ** (Skip y z)) => noLtr (fst ** z))

      merge f (x :: xs) ys | (No noMerge) | (No contra)
        = No (\case ((z :: zs) ** (Head pH pL)) => noMerge (z ** pH)
                    (fst ** (Skip y z)) => contra y)

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

mergeMSR: DPair (Local rs fs) (Merge (Comm SEND w idx) (Comm RECV v ix)) -> Void
mergeMSR (_ ** _) impossible

mergeMRS: DPair (Local rs fs) (Merge (Comm RECV w idx) (Comm SEND v ix)) -> Void
mergeMRS (_ ** _) impossible


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
merge (Comm cx rx xs) (Comm cy ry ys) with (decEq cx cy)
  merge (Comm cx rx xs) (Comm cy ry ys) | (Yes pC) with (decEq rx ry)
    merge (Comm RECV rx xs) (Comm RECV rx ys) | (Yes Refl) | (Yes Refl) with (diff xs ys)
      merge (Comm RECV rx xs) (Comm RECV rx ys) | (Yes Refl) | (Yes Refl) | (xys ** prfXY) with (diff ys xs)
        merge (Comm RECV rx xs) (Comm RECV rx ys) | (Yes Refl) | (Yes Refl) | (xys ** prfXY) | (yxs ** prfYX) with (Recv.merge merge xs ys)
          merge (Comm RECV rx xs) (Comm RECV rx ys) | (Yes Refl) | (Yes Refl) | (xys ** prfXY) | (yxs ** prfYX) | (Yes (zs ** prfZS))
            = Yes (Comm RECV rx (xys ++ (zs ++ yxs)) ** Recv Refl prfXY prfYX prfZS)
          merge (Comm RECV rx xs) (Comm RECV rx ys) | (Yes Refl) | (Yes Refl) | (xys ** prfXY) | (yxs ** prfYX) | (No no)
            = No (\case (Comm RECV rx (xys ++ zs ++ yxs) ** Recv Refl _ _ prf) => no (zs ** prf))

    merge (Comm SEND rx xs) (Comm SEND rx ys) | (Yes Refl) | (Yes Refl) with (Send.merge merge xs ys)
      merge (Comm SEND rx xs) (Comm SEND rx ys) | (Yes Refl) | (Yes Refl) | (Yes (zs ** prf))
        = Yes (Comm SEND rx zs ** Send Refl prf)
      merge (Comm SEND rx xs) (Comm SEND rx ys) | (Yes Refl) | (Yes Refl) | (No no)
        = No (\case (Comm SEND rx xs ** Send Refl zs) => no (xs ** zs))

    merge (Comm cx rx xs) (Comm cx ry ys) | (Yes Refl) | (No contra)
      = No (\case (Comm SEND _ _ ** Send Refl _) => contra Refl
                  (Comm RECV _ _ ** Recv Refl _ _ _) => contra Refl)

  -- [ NOTE ] c'est horrible

  merge (Comm SEND rx xs) (Comm SEND ry ys) | (No no)
    = No (\case (Comm SEND _ _ ** Send Refl snd) => no Refl)
  merge (Comm SEND rx xs) (Comm RECV ry ys) | (No no)
    = No mergeMSR
  merge (Comm RECV rx xs) (Comm SEND ry ys) | (No no)
    = No mergeMRS
  merge (Comm RECV rx xs) (Comm RECV ry ys) | (No no)
    = No (\case (Comm RECV _ _ ** Recv Refl _ _ _) => no Refl)


-- [ EOF ]
