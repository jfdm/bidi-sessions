module Sessions.Types.Local.Merge.Projection

import Decidable.Equality

import Data.SnocList
import Data.SnocList.Elem

import public Extra

import Sessions.Types.Local
import public Sessions.Types.Local.Difference
import public Sessions.Types.Local.Merge.Branch
import public Sessions.Types.Local.Merge.Branches

import public Sessions.Types.Local.Merge.Merges

%default total

public export
data Merge : (x,y,z : Local rs fs)
           -> Type

  where
    Stop : Merge Stop Stop Stop
    Call : Equal idxx  idxy
        -> Merge (Call idxx)
                 (Call idxy)
                 (Call idxx)
    Rec : Merge kx ky kz
       -> Merge (Rec kx)
                (Rec ky)
                (Rec kz)

    Send : (sx = sy)
        -> Pairwise.Union Merge kx ky kz
        -> Merge (Comm SEND sx kx)
                 (Comm SEND sy ky)
                 (Comm SEND sx kz)


    Recv : {zs : List $ Branch rs fs}
        -> (sx = sy)
        -> Full.Merge Merge kx ky zs
        -> Merge (Comm RECV sx kx)
                 (Comm RECV sy ky)
                 (Comm RECV sx zs)


mergeSC : DPair (Local rs fs) (Merge Stop (Call x)) -> Void
mergeSC (_ ** _) impossible

mergeSR : DPair (Local rs fs) (Merge Stop (Rec s)) -> Void
mergeSR (_ ** _) impossible

mergeSM : DPair (Local rs fs) (Merge Stop (Comm x y xs)) -> Void
mergeSM (_ ** _) impossible

mergeCR : DPair (Local rs fs) (Merge (Call idx) (Rec s)) -> Void
mergeCR (_ ** _) impossible

mergeCM : DPair (Local rs fs) (Merge (Call idx) (Comm z x s)) -> Void
mergeCM (_ ** _) impossible

mergeCS : DPair (Local rs fs) (Merge (Call x) Stop ) -> Void
mergeCS (_ ** _) impossible

mergeRS : DPair (Local rs fs) (Merge (Rec s) Stop) -> Void
mergeRS (_ ** _) impossible

mergeRC: DPair (Local rs fs) (Merge (Rec s) (Call idx) ) -> Void
mergeRC (_ ** _) impossible

mergeRM: DPair (Local rs fs) (Merge (Rec s) (Comm a w idx) ) -> Void
mergeRM (_ ** _) impossible


mergeMS : DPair (Local rs fs) (Merge (Comm x y xs) Stop) -> Void
mergeMS (_ ** _) impossible

mergeMC : DPair (Local rs fs) (Merge  (Comm z x s) (Call idx)) -> Void
mergeMC (_ ** _) impossible

mergeMR: DPair (Local rs fs) (Merge (Comm a w idx) (Rec s)) -> Void
mergeMR (_ ** _) impossible

mergeMSR: DPair (Local rs fs) (Merge (Comm SEND w idx) (Comm RECV v ix)) -> Void
mergeMSR (_ ** _) impossible

mergeMRS: DPair (Local rs fs) (Merge (Comm RECV w idx) (Comm SEND v ix)) -> Void
mergeMRS (_ ** _) impossible

mutual
  namespace Full
    export
    merge : (xs : List (Branch rs fs))
         -> (ys : List (Branch rs fs))
               -> Dec (DPair (List (Branch rs fs))
                             (Full.Merge Projection.Merge xs ys))
    merge = Full.merge Projection.merge


  export
  merge : (x,y : Local rs fs) -> Dec (DPair (Local rs fs) (Merge x y))
  merge Stop Stop = Yes (Stop ** Stop)
  merge Stop (Call x) = No mergeSC
  merge Stop (Rec x) = No mergeSR
  merge Stop (Comm x y xs) = No mergeSM

  merge (Call x) Stop = No mergeCS
  merge (Call x) (Call y) with (decEq x y)
    merge (Call x) (Call y) | (Yes prf)
      = Yes (Call x ** Call prf)
    merge (Call x) (Call y) | (No contra)
      = No (\case (Call fst ** Call prf) => contra prf)

  merge (Call x) (Rec y) = No mergeCR
  merge (Call x) (Comm y z xs) = No mergeCM

  merge (Rec x) Stop = No mergeRS
  merge (Rec x) (Call y) = No mergeRC
  merge (Rec x) (Rec y) with (merge x y)
    merge (Rec x) (Rec y) | (Yes ((fst ** snd))) = Yes (Rec fst ** Rec snd)
    merge (Rec x) (Rec y) | (No contra)
      = No $ \case (((Rec kz) ** (Rec z))) => contra (kz ** z)

  merge (Rec x) (Comm y z xs) = No mergeRM

  merge (Comm x z xs) Stop = No mergeMS
  merge (Comm x z xs) (Call y) = No mergeMC
  merge (Comm x z xs) (Rec y) = No mergeMR
  merge (Comm cx rx xs) (Comm cy ry ys) with (decEq cx cy)
    merge (Comm cx rx xs) (Comm cy ry ys) | (Yes pC) with (decEq rx ry)
      merge (Comm RECV rx xs) (Comm RECV rx ys) | (Yes Refl) | (Yes Refl) with (Full.merge xs ys)
        merge (Comm RECV rx xs) (Comm RECV rx ys) | (Yes Refl) | (Yes Refl) | (Yes (zs ** prf))
          = Yes (Comm RECV rx zs ** Recv Refl prf)
        merge (Comm RECV rx xs) (Comm RECV rx ys) | (Yes Refl) | (Yes Refl) | (No no)
          = No (\case (Comm RECV _ _ ** Recv Refl snd) => no (_ ** snd))

      merge (Comm SEND rx xs) (Comm SEND rx ys) | (Yes Refl) | (Yes Refl) with (Pairwise.union merge xs ys)
        merge (Comm SEND rx xs) (Comm SEND rx ys) | (Yes Refl) | (Yes Refl) | (Yes (zs ** prf))
          = Yes (Comm SEND rx zs ** Send Refl prf)
        merge (Comm SEND rx xs) (Comm SEND rx ys) | (Yes Refl) | (Yes Refl) | (No no)
          = No (\case (Comm SEND _ _ ** Send Refl prf) => no (_ ** prf))

      merge (Comm cx rx xs) (Comm cx ry ys) | (Yes Refl) | (No contra)
        = No (\case (Comm SEND _ _ ** Send Refl _) => contra Refl
                    (Comm RECV _ _ ** Recv Refl _) => contra Refl)

    -- [ NOTE ] c'est horrible

    merge (Comm SEND rx xs) (Comm SEND ry ys) | (No no)
      = No (\case (Comm SEND _ _ ** Send Refl snd) => no Refl)
    merge (Comm SEND rx xs) (Comm RECV ry ys) | (No no)
      = No mergeMSR
    merge (Comm RECV rx xs) (Comm SEND ry ys) | (No no)
      = No mergeMRS
    merge (Comm RECV rx xs) (Comm RECV ry ys) | (No no)
      = No (\case (Comm RECV _ _ ** Recv Refl _) => no Refl)

mutual
  namespace Full
    export
    unique : Full.Merge Projection.Merge xs ys as
          -> Full.Merge Projection.Merge xs ys bs
          -> as === bs
    unique = Full.unique

  export
  unique : Projection.Merge lx ry a
        -> Projection.Merge lx ry b
        -> a === b
  unique Stop Stop = Refl
  unique (Call x) (Call y) = Refl

  unique (Rec x) (Rec y) with (unique x y)
    unique (Rec x) (Rec y) | Refl = Refl

  unique (Send Refl x) (Send Refl y) with (unique unique x y)
    unique (Send Refl x) (Send Refl y) | Refl = Refl

  unique (Recv Refl x) (Recv Refl y) with (Full.unique x y)
    unique (Recv Refl x) (Recv Refl y) | Refl = Refl


namespace Projection

  export
  merges : (xs : List (Local rs fs))
              -> Dec (DPair (Local rs fs)
                            (Merges Projection.Merge xs))
  merges = Merges.merge Projection.merge Projection.unique

  namespace Merges
    export
    unique : Merges Projection.Merge xs a
          -> Merges Projection.Merge xs b
          -> a === b
    unique = Merges.unique Projection.unique
-- [ EOF ]
